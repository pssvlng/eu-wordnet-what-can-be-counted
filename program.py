#!/usr/bin/env python3
"""
Reproduces every figure reported in the paper

    What Can Be Counted Over Aligned Wordnets?
    An Artefact Taxonomy and a Portability Criterion

The data are seven wordnets aligned to the same 120,053 Interlingual Index
(ILI) concepts: English (ewn) and the hybrid Italian, Spanish, French, Dutch,
Portuguese and German wordnets of Bergh et al. (2025).

    python3 program.py all            everything below, in this order
    python3 program.py install        download and install the seven lexicons
    python3 program.py check          verify software and lexicons
    python3 program.py detect         main run: filters, detectors, fan-in matrix
    python3 program.py sensitivity    re-runs with one setting changed
    python3 program.py annotation     seeded annotation sheets
    python3 program.py report         every figure in the paper, checked

All inputs are downloaded; all outputs are written to outputs/ next to this
file. Requirements and the meaning of every output file: README.md.
"""

import argparse
import difflib
import gzip
import hashlib
import io
import json
import math
import os
import random
import re
import subprocess
import sys
import tempfile
import zipfile
from collections import defaultdict
from dataclasses import dataclass

import wn

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUT_DIR = os.path.join(SCRIPT_DIR, 'outputs')

# language code -> (wn lexicon id, version). Versions are pinned so that other
# wordnets installed alongside (e.g. a newer Open English WordNet) are ignored.
LEXICONS = {
    'en': ('ewn', '2020'),
    'it': ('hyit', '0.1'),
    'es': ('hyes', '0.1'),
    'fr': ('hyfr', '0.1'),
    'nl': ('hynl', '0.1'),
    'pt': ('hypt', '0.1'),
    'de': ('hyde', '0.1'),
}
LANGUAGES = {lang: f'{lex}:{ver}' for lang, (lex, ver) in LEXICONS.items()}
EN_LEXICON = LANGUAGES['en']

# software versions the published figures were produced with
TESTED_VERSIONS = {'python': '3.10.12', 'wn': '0.9.4', 'espeak-ng': '1.50'}

# English WordNet 2020 marks the 2,573 concepts it proposes for the ILI with
# ili="in", i.e. without an identifier. The hybrid wordnets refer to them as
# in_i1 ... in_i2573, numbered in the order they appear in the English file by
# the script that built the hybrids. `install` applies the same numbering to
# the official download; without it those concepts are not aligned.
PROPOSED_ILI_COUNT = 2573
FIRST_PROPOSED_SYNSET = ('ewn-05698967-n', 'in_i1')  # "color barrier"

# the hybrid wordnets, pinned to the commit holding the files the paper used
HYBRID_REPO = 'https://github.com/pssvlng/open-european-wordnets-hybrid'
HYBRID_COMMIT = '95a69f6c6274483f0cb83fc01b72cf4cf19a88b0'  # 2023-08-07

# SHA-256 of the unpacked <lang>_hybrid.xml files the paper's figures were computed from
HYBRID_SHA256 = {
    'it': 'af1b226896560809072b70a4841392805e53cfd5ad47f0d03948883e78593bd8',
    'es': 'edce72e5eb6865574ef2c534ab3f5e06bfe4210cb8a5d3285df049c222c73788',
    'fr': '7b4ef7ec079258edb12f26d804106b8958455f042e95f5bb8e748d4f64ac525a',
    'nl': 'c8ece11cddc4a0020f307cc6080ccc902d7d2ca1756cbd0741b415778055cf21',
    'pt': '212f2f96141d34e3feb879d28bf95996671b3f7d49f6da32bbcfc73a753df5be',
    'de': 'a1afb5af2d31d0f36eaf5db46eeee2c40746b53ac94f47330fef0d56791fe5da',
}

# espeak-ng voice codes differ slightly from wn/ISO language codes for a couple of languages
ESPEAK_VOICE = {
    'en': 'en-gb',
    'it': 'it',
    'es': 'es',
    'fr': 'fr-fr',
    'nl': 'nl',
    'pt': 'pt-pt',
    'de': 'de',
}

WORD_RE = re.compile(r"^[^\W\d_]+$", re.UNICODE)  # single alphabetic "word" (letters only, no spaces/digits)
VOWEL_RE = re.compile(r"[aeiouyàáâãäåèéêëìíîïòóôõöùúûüæœ]", re.IGNORECASE)

# F1: at 1-2 letters, WordNet entries are overwhelmingly acronyms, chemical
# symbols, unit abbreviations and letter names (e.g. "A" = adenine/vitamin
# A/ampere/the letter itself) rather than ordinary words.
MIN_LEMMA_LENGTH = 3

# how many entries the summary JSON keeps per category (full/untruncated results
# always go into the per-language detail files in outputs/<lang>.json)
SUMMARY_EXAMPLE_CAP = 25
SUMMARY_CLUSTER_CAP = 15

NEAR_HOMOPHONE_MIN_RATIO = 0.90
COGNATE_MIN_RATIO = 0.6
DOUBLET_MIN_RATIO = 0.7
DOUBLET_MAX_RATIO = 0.95  # exclude near-identical spelling variants (inflections/typos)

# Languages where capitalization is a GRAMMATICAL rule (marks a noun), not a
# proper-noun signal — German capitalizes every common noun (Substantiv-
# großschreibung: "Gehirn", "Freiheit", "Kunde" are all ordinary nouns), so
# F3 would wrongly delete most of the German vocabulary. These languages
# skip F3 entirely; F6 compensates for the case-variant pairs this creates.
CAPITALIZATION_MARKS_NOUN_LANGUAGES = frozenset({'de'})

# negation particles used to filter out contronym "candidates" that are really
# just a word and its morphological negation (e.g. NL "chirurgisch" / "niet
# chirurgisch") rather than a single word whose OWN sense drifted to its
# opposite (e.g. EN "cleave" = join AND split).
NEGATION_MARKERS = {
    'en': [' not ', 'not '],
    'it': [' non ', 'non '],
    'es': [' no ', 'no ', ' sin ', 'sin '],
    'fr': [' non ', 'non ', ' pas ', 'pas ', ' sans ', 'sans '],
    'nl': [' niet ', 'niet ', ' zonder ', 'zonder '],
    'pt': [' não ', 'não ', ' sem ', 'sem '],
    'de': [' nicht ', 'nicht ', ' kein ', 'kein ', ' ohne ', 'ohne '],
}

# productive part-of-speech-changing derivational suffixes per language, used
# to exclude near-homophone and spoonerism-style pairs that are really two
# unrelated stems fed through the same derivation (e.g. ES "rápidamente"/
# "felizmente", both ADJECTIVE+"-mente") rather than a phonological
# coincidence between two independent words (paper §3.3).
POS_CHANGING_SUFFIXES = {
    'en': ['ly', 'ness', 'ity', 'tion', 'sion', 'able', 'ible', 'ment', 'ism', 'ist',
           'ation', 'ization', 'isation'],
    'it': ['mente', 'ita', 'ità', 'zione', 'sione', 'abile', 'ibile', 'ismo', 'ista'],
    'es': ['mente', 'idad', 'ción', 'sión', 'able', 'ible', 'ismo', 'ista'],
    'fr': ['ment', 'ité', 'tion', 'sion', 'able', 'ible', 'isme', 'iste'],
    'nl': ['heid', 'lijk', 'baar', 'atie', 'isme', 'iste'],
    'pt': ['mente', 'idade', 'ção', 'são', 'ável', 'ível', 'ismo', 'ista'],
    'de': ['lich', 'keit', 'heit', 'ung', 'bar', 'sam', 'isch'],
}


@dataclass(frozen=True)
class Filters:
    """
    Switches for the artefact filters of paper Table 2. The defaults are the
    protocol behind every reported figure; the other settings exist only for
    the `sensitivity` command. F1 (length) and F2 (vowel) are always applied,
    since they define what counts as a single word.
    """
    f3: str = 'drop'   # capitalised lemmas: 'drop', or 'keep_if_lowercase_twin' (the rejected softer rule)
    f4: bool = True    # drop lemmas identical to an English lemma of the same ILI
    f5: bool = True    # merge same-pronunciation forms that share a synset
    f6: bool = True    # merge same-pronunciation forms that differ only in case


PROTOCOL = Filters()


# --------------------------------------------------------------------------
# Data loading (filters F1-F4)
# --------------------------------------------------------------------------

def is_single_word(lemma: str) -> bool:
    # F1 (length) and F2 (a vowel requirement, which removes remaining
    # abbreviation-like strings such as the compass code "SWbW" that pass the
    # length and alphabetic checks but aren't pronounceable words)
    return (bool(WORD_RE.match(lemma))
            and len(lemma) >= MIN_LEMMA_LENGTH
            and bool(VOWEL_RE.search(lemma)))


def senses_for(index: dict, lemma: str) -> list:
    """Full sense list for a lemma: one entry per distinct synset, with meaning + ids."""
    seen = set()
    result = []
    for e in index['words'].get(lemma, []):
        if e['synset_id'] in seen:
            continue
        seen.add(e['synset_id'])
        result.append({
            'pos': e['pos'],
            'definition': e['definition'],
            'synset_id': e['synset_id'],
            'ili': e['ili'],
        })
    return result


_LEXICON_ROWS = {}


def read_lexicon(lexicon: str) -> list:
    """
    (synset id, ili, pos, lemmas, definition) for every synset of a lexicon.
    Reading through wn is the slow step, and the sensitivity analyses build
    several indices from one lexicon, so the rows are cached per process.
    """
    if lexicon not in _LEXICON_ROWS:
        print(f'reading {lexicon}...', flush=True)
        rows = []
        synsets = wn.synsets(lexicon=lexicon)
        for i, synset in enumerate(synsets, 1):
            rows.append((synset.id, synset.ili.id if synset.ili else None, synset.pos,
                         synset.lemmas(), synset.definition() or ''))
            if i % 40000 == 0:
                print(f'  {i}/{len(synsets)} synsets', flush=True)
        _LEXICON_ROWS[lexicon] = rows
    return _LEXICON_ROWS[lexicon]


def load_language_index(lang: str, english_lemmas_by_ili: dict = None,
                        filters: Filters = PROTOCOL) -> dict:
    """
    Build an in-memory index for one language:
      words:     lemma -> list of {pos, synset_id, ili, definition}
      by_synset: synset_id -> {ili, pos, lemmas: [...], definition}
      by_ili:    ili -> same dict as above (for cross-lingual alignment,
                 since each lexicon has its own local synset ids but shares
                 the same ILI space)
      filter_stats: lemma-occurrences removed by F3 and F4
    Only single-word lemmas (F1, F2) are included in `words` (phonological/
    orthographic phenomena don't apply to multi-word phrases); `by_synset`/
    `by_ili` keep everything for cross-lingual synset alignment.

    F3: a capitalised lemma is excluded as a likely proper noun or acronym
    (WordNet has no proper-noun tag). The softer rule tried first — keep it if
    a lowercase counterpart exists somewhere — let real proper nouns through
    whenever they collided with an unrelated common word (ES "Cola" the plant
    genus vs "cola" tail/queue/soda); it is kept only as a sensitivity setting.
    German is exempt (see CAPITALIZATION_MARKS_NOUN_LANGUAGES).

    F4: for non-English languages, if `english_lemmas_by_ili` is given, a
    lemma is dropped when it matches (case-insensitively) one of the ENGLISH
    lemmas of the same ILI. Machine translation in the inferred portion of the
    hybrid wordnets returns some English strings unchanged, so e.g. the German
    synset for "trash" lists "Ramsch"/"Kitsch"/"Schund" AND "Trash" itself.
    """
    lexicon = LANGUAGES[lang]
    rows = read_lexicon(lexicon)
    words = defaultdict(list)
    by_synset = {}
    by_ili = {}
    f3_dropped = 0
    f4_dropped = 0
    apply_f3 = lang not in CAPITALIZATION_MARKS_NOUN_LANGUAGES

    lowercase_forms = set()
    if apply_f3 and filters.f3 == 'keep_if_lowercase_twin':
        lowercase_forms = {l.lower() for _, _, _, lemmas, _ in rows for l in lemmas
                           if is_single_word(l) and not l[0].isupper()}

    for synset_id, ili, pos, lemmas, definition in rows:
        entry = {
            'ili': ili,
            'pos': pos,
            'lemmas': lemmas,
            'definition': definition,
        }
        by_synset[synset_id] = entry
        if ili:
            by_ili[ili] = entry
        english_lemmas_lower = None
        if english_lemmas_by_ili is not None and ili:
            english_lemmas_lower = english_lemmas_by_ili.get(ili)
        for lemma in lemmas:
            if not is_single_word(lemma):
                continue
            if lemma[0].isupper() and apply_f3:
                if filters.f3 == 'drop' or lemma.lower() not in lowercase_forms:
                    f3_dropped += 1
                    continue
            if filters.f4 and english_lemmas_lower and lemma.lower() in english_lemmas_lower:
                f4_dropped += 1
                continue
            words[lemma].append({
                'pos': pos,
                'synset_id': synset_id,
                'ili': ili,
                'definition': definition,
            })

    f3_msg = 'F3 not applied' if not apply_f3 else f'F3 removed {f3_dropped}'
    print(f'[{lang}] {len(words)} distinct single-word lemmas ({f3_msg}, F4 removed '
          f'{f4_dropped} lemma-occurrences), {len(by_synset)} synsets', flush=True)
    return {'words': words, 'by_synset': by_synset, 'by_ili': by_ili,
            'filter_stats': {'f3_dropped': f3_dropped, 'f4_dropped': f4_dropped}}


def english_lemmas_by_ili(en_index: dict) -> dict:
    """ILI -> lowercased English lemmas, the reference set for F4."""
    return {ili: {l.lower() for l in entry['lemmas']} for ili, entry in en_index['by_ili'].items()}


# --------------------------------------------------------------------------
# espeak-ng IPA transcription (with caching)
# --------------------------------------------------------------------------

class Phonemizer:
    def __init__(self, lang: str, voice: str = None):
        # `voice` overrides the default for that language. Used for the accent
        # sensitivity analysis: espeak-ng's en-gb is non-rhotic, so pairs such as
        # "tuna"/"tuner" collapse to one phoneme string, while the rhotic en-us
        # keeps them distinct (ə vs ɚ). Homophone counts are therefore partly a
        # property of the accent model, not only of the language.
        self.voice = voice or ESPEAK_VOICE[lang]
        self._cache = {}

    def transcribe_batch(self, wordlist):
        """
        Transcribe many words in one espeak-ng call (much faster than per-word
        subprocess). Plain newline-separated input gets silently merged into a
        single utterance by espeak-ng, so each word is forced onto its own
        utterance with a '.' separator line, which reliably yields one IPA
        line of output per input word.
        """
        todo = [w for w in wordlist if w not in self._cache]
        if not todo:
            return
        chunk_size = 1000
        for start in range(0, len(todo), chunk_size):
            chunk = todo[start:start + chunk_size]
            input_text = '\n.\n'.join(chunk)
            try:
                result = subprocess.run(
                    ['espeak-ng', '-v', self.voice, '-q', '--ipa', '--stdin'],
                    input=input_text,
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
                lines = result.stdout.strip('\n').split('\n')
            except Exception as e:
                print(f'  espeak-ng batch failed ({e}); skipping {len(chunk)} words', flush=True)
                lines = []
            for word, ipa in zip(chunk, lines):
                self._cache[word] = ipa.strip()
            for word in chunk[len(lines):]:
                self._cache[word] = ''

    def get(self, word):
        return self._cache.get(word, '')


def strip_ipa_stress(ipa: str) -> str:
    """Remove stress marks / syllable boundaries so we compare pure phoneme sequences."""
    return re.sub(r"[ˈˌ.'|]", '', ipa)


# --------------------------------------------------------------------------
# Category detectors (single language)
# --------------------------------------------------------------------------

def detect_homographs(index: dict) -> dict:
    """
    Homograph: same written form, different meaning (different synset),
    regardless of pronunciation or part of speech. We count lemmas that
    appear in 2+ distinct synsets.
    """
    matches = []
    for lemma, entries in index['words'].items():
        distinct_synsets = {e['synset_id'] for e in entries}
        if len(distinct_synsets) >= 2:
            matches.append(lemma)
    matches.sort()
    full = [{'lemma': lemma, 'senses': senses_for(index, lemma)} for lemma in matches]
    return {
        'count': len(matches),
        'examples': matches[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
    }


def detect_polysemes(index: dict) -> dict:
    """
    Polyseme: a word with multiple *related* meanings under one written form,
    approximated as same lemma + same POS in 2+ distinct synsets (the
    standard operational proxy, vs. homonymy which is usually cross-POS).
    """
    matches = []
    for lemma, entries in index['words'].items():
        by_pos = defaultdict(set)
        for e in entries:
            by_pos[e['pos']].add(e['synset_id'])
        if any(len(s) >= 2 for s in by_pos.values()):
            matches.append(lemma)
    matches.sort()
    full = [{'lemma': lemma, 'senses': senses_for(index, lemma)} for lemma in matches]
    return {
        'count': len(matches),
        'examples': matches[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
    }


def detect_homonyms(index: dict) -> dict:
    """
    Homonym (operational proxy): same written form spanning 2+ *different*
    parts of speech — true etymological unrelatedness can't be determined
    from WordNet, so this is a cross-POS homograph proxy.
    """
    matches = []
    for lemma, entries in index['words'].items():
        distinct_pos = {e['pos'] for e in entries}
        if len(distinct_pos) >= 2:
            matches.append(lemma)
    matches.sort()
    full = [{'lemma': lemma, 'senses': senses_for(index, lemma)} for lemma in matches]
    return {
        'count': len(matches),
        'examples': matches[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
    }


def detect_heteronyms(index: dict) -> dict:
    """
    Heteronym: same written form, different meaning AND different pronunciation
    (e.g. 'lead' /liːd/ to guide vs 'lead' /lɛd/ the metal).
    """
    # espeak-ng is deterministic given one written form, so it cannot itself
    # produce two different transcriptions for the same input string; true
    # heteronym detection would need a pronunciation dictionary with per-sense
    # stress variants (e.g. CMUdict). We instead report the cross-POS homograph
    # subset as an unverified upper-bound candidate list, since English
    # heteronyms are overwhelmingly noun/verb stress-shift pairs (REcord/reCORD).
    matches = sorted(lemma for lemma, entries in index['words'].items()
                     if len({e['pos'] for e in entries}) >= 2)
    full = [{'lemma': lemma, 'senses': senses_for(index, lemma)} for lemma in matches]
    return {
        'count': len(matches),
        'examples': matches[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
        'note': 'espeak-ng yields one deterministic reading per written form; true heteronym '
                'detection needs a pronunciation dictionary with per-sense stress variants '
                '(e.g. CMUdict for English). This count is an UNVERIFIED upper bound: cross-POS '
                'homographs that are plausible heteronym candidates.',
    }


def detect_contronyms(index: dict, lexicon: str, lang: str) -> dict:
    """
    Contronym / auto-antonym: a single lemma where one sense is linked by
    WordNet's antonym sense-relation to another sense of a lemma spelled
    identically to itself. Pairs where either definition contains a negation
    particle (e.g. "not", NL "niet", FR "non"/"pas") are excluded: these are a
    word cross-linked to its own morphological negation ("surgical" / "not
    surgical"), not a single word whose sense drifted to its opposite
    ("cleave" = join AND split).
    """
    markers = NEGATION_MARKERS.get(lang, [])

    def is_negation_pair(def_a: str, def_b: str) -> bool:
        a, b = f' {def_a.lower()} ', f' {def_b.lower()} '
        return any(m in a for m in markers) or any(m in b for m in markers)

    matches = {}  # lemma -> list of {sense_definition, antonym_sense_definition}
    words = wn.words(lexicon=lexicon)
    for w in words:
        lemma = w.lemma()
        if not is_single_word(lemma):
            continue
        lemma_l = lemma.lower()
        for sense in w.senses():
            try:
                antonyms = sense.get_related('antonym')
            except Exception:
                antonyms = []
            for a in antonyms:
                try:
                    if a.word().lemma().lower() != lemma_l:
                        continue
                    sense_def = sense.synset().definition() or ''
                    antonym_def = a.synset().definition() or ''
                    if is_negation_pair(sense_def, antonym_def):
                        continue
                    matches.setdefault(lemma_l, []).append({
                        'sense_definition': sense_def,
                        'antonym_sense_definition': antonym_def,
                    })
                except Exception:
                    continue
    sorted_lemmas = sorted(matches.keys())
    full = [{'lemma': lemma, 'opposed_sense_pairs': matches[lemma]} for lemma in sorted_lemmas]
    return {
        'count': len(sorted_lemmas),
        'examples': sorted_lemmas[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
        'note': 'Detected via WordNet antonym sense-relations pointing back to the same written '
                'form, excluding pairs that look like a simple negation of the same sense (e.g. '
                '"surgical"/"not surgical") rather than a genuine drifted-to-opposite meaning. '
                'This under-counts true contronyms since most (e.g. "sanction", "cleave") are not '
                'cross-linked as antonyms in WordNet at all — treat as a lower bound.',
    }


def detect_palindromes(index: dict) -> dict:
    matches = sorted(lemma for lemma in index['words'] if len(lemma) >= 3 and lemma == lemma[::-1])
    full = [{'lemma': lemma, 'senses': senses_for(index, lemma)} for lemma in matches]
    return {
        'count': len(matches),
        'examples': matches[:SUMMARY_EXAMPLE_CAP],
        'all_matches': full,
    }


def collapse_spelling_variants(index: dict, forms: list, filters: Filters = PROTOCOL) -> list:
    """
    Within a set of same-pronunciation written forms, collapse subgroups that
    are really ONE lexeme spelled/inflected differently (e.g. EN "summarise"/
    "summarize", FR "clef"/"clefs"/"clé"/"clés") rather than genuinely
    distinct homophones (EN "write"/"right"/"rite"). Two forms are merged if
      F5: they share ANY synset, or
      F6: they are identical except for case (DE "Ort"/"ort", "Licht"/"licht")
          — German capitalisation marks a noun grammatically, so a capitalised
          noun and its lowercase counterpart are one written word in two roles.
    Connected components are found via union-find, so a chain of partial
    overlaps (clefs~clef~clé~clés, where clefs and clés share no synset
    directly) still merges into one group. Each group is represented by its
    shortest form (alphabetically first among equals). Returns the reduced,
    sorted list of representative forms.
    """
    if len(forms) < 2:
        return forms

    parent = {f: f for f in forms}

    def find(f):
        while parent[f] != f:
            parent[f] = parent[parent[f]]
            f = parent[f]
        return f

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    synsets_by_form = {f: {e['synset_id'] for e in index['words'][f]} for f in forms}
    for i in range(len(forms)):
        for j in range(i + 1, len(forms)):
            if filters.f5 and synsets_by_form[forms[i]] & synsets_by_form[forms[j]]:
                union(forms[i], forms[j])
            elif filters.f6 and forms[i].lower() == forms[j].lower():
                union(forms[i], forms[j])

    groups = defaultdict(list)
    for f in forms:
        groups[find(f)].append(f)

    representatives = []
    for group in groups.values():
        representatives.append(sorted(group, key=lambda w: (len(w), w))[0])
    return sorted(representatives)


def detect_homophones(index: dict, phonemizer: Phonemizer, filters: Filters = PROTOCOL) -> dict:
    """
    Homophone: different written forms, identical pronunciation. Lemmas are
    grouped by stripped IPA transcription, spelling/inflectional and case
    variants of one lexeme are collapsed (F5, F6; see
    collapse_spelling_variants), and any group still holding 2+ forms is a
    homophone cluster.
    """
    all_words = list(index['words'].keys())
    phonemizer.transcribe_batch(all_words)

    by_ipa = defaultdict(set)
    for lemma in all_words:
        ipa = strip_ipa_stress(phonemizer.get(lemma))
        if ipa:
            by_ipa[ipa].add(lemma)

    clusters_by_ipa = {}
    for ipa, forms in by_ipa.items():
        collapsed = collapse_spelling_variants(index, sorted(forms), filters)
        if len(collapsed) >= 2:
            clusters_by_ipa[ipa] = collapsed
    clusters = list(clusters_by_ipa.values())
    total_words_involved = sum(len(c) for c in clusters)
    examples = sorted(clusters, key=len, reverse=True)[:SUMMARY_CLUSTER_CAP]
    full = [
        {
            'ipa': ipa,
            'words': [{'lemma': w, 'senses': senses_for(index, w)} for w in forms],
        }
        for ipa, forms in sorted(clusters_by_ipa.items(), key=lambda kv: -len(kv[1]))
    ]
    return {
        'cluster_count': len(clusters),
        'words_involved': total_words_involved,
        'examples': examples,
        'all_clusters': full,
        'note': 'Written forms sharing a synset with another form in the same pronunciation '
                'group (spelling variants like "summarise"/"summarize", or inflected agreement '
                'forms like FR "annulé"/"annulée"/"annulés"/"annulées") are collapsed to one '
                'representative form before counting, so they are not double-counted as if they '
                'were distinct homophone words.',
    }


def detect_near_homophones(index: dict, phonemizer: Phonemizer, lang: str) -> dict:
    """
    Near-homophones (paronyms): different written forms, very similar but
    NOT identical pronunciation (IPA string similarity >= 0.90). Naive O(n^2)
    comparison is infeasible at full vocabulary scale, so we bucket by IPA
    length and first phoneme. Pairs where either word ends in a productive
    POS-changing suffix are excluded beforehand (see has_pos_changing_suffix).
    """
    all_words = list(index['words'].keys())
    phonemizer.transcribe_batch(all_words)

    buckets = defaultdict(list)
    for lemma in all_words:
        if has_pos_changing_suffix(lang, lemma):
            continue
        ipa = strip_ipa_stress(phonemizer.get(lemma))
        if not ipa:
            continue
        key = (ipa[0] if ipa else '', len(ipa))
        buckets[key].append((lemma, ipa))

    pairs = []
    seen_pairs = set()
    for key, items in buckets.items():
        if len(items) < 2 or len(items) > 200:  # skip pathological mega-buckets for performance
            continue
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                w1, ipa1 = items[i]
                w2, ipa2 = items[j]
                if w1 == w2 or ipa1 == ipa2:
                    continue
                # skip pairs that already share a synset (same meaning) — these
                # are spelling variants of one sense, not a phonological
                # near-miss between two distinct words
                synsets1 = {e['synset_id'] for e in index['words'][w1]}
                synsets2 = {e['synset_id'] for e in index['words'][w2]}
                if synsets1 & synsets2:
                    continue
                ratio = difflib.SequenceMatcher(None, ipa1, ipa2).ratio()
                if ratio >= NEAR_HOMOPHONE_MIN_RATIO:
                    pair_key = tuple(sorted((w1, w2)))
                    if pair_key not in seen_pairs:
                        seen_pairs.add(pair_key)
                        pairs.append({'a': w1, 'b': w2, 'ratio': round(ratio, 3)})

    pairs.sort(key=lambda p: -p['ratio'])
    full = [
        {
            'a': p['a'], 'b': p['b'], 'ratio': p['ratio'],
            'a_senses': senses_for(index, p['a']),
            'b_senses': senses_for(index, p['b']),
        }
        for p in pairs
    ]
    return {
        'pair_count': len(pairs),
        'examples': pairs[:SUMMARY_EXAMPLE_CAP],
        'all_pairs': full,
        'note': f'IPA similarity >= {NEAR_HOMOPHONE_MIN_RATIO} via difflib ratio, bucketed by '
                f'(first phoneme, IPA length) for tractability — some true near-homophone pairs '
                f'across bucket boundaries are missed. Words carrying a known productive POS-'
                f'changing derivational suffix for this language (e.g. EN "-ly"/"-ness", ES/PT '
                f'"-mente", DE "-keit"/"-ung") are excluded beforehand, since these otherwise '
                f'produce many "near-homophone" pairs that are really just systematic derivation '
                f'(e.g. "sociobiologically"/"sociobiological") rather than coincidental similarity.',
    }


def has_pos_changing_suffix(lang: str, word: str) -> bool:
    """
    True if `word` ends in one of this language's productive part-of-speech-
    changing derivational suffixes (e.g. EN "-ly", ES/PT "-mente", DE "-keit").
    """
    suffixes = POS_CHANGING_SUFFIXES.get(lang, [])
    wl = word.lower()
    return any(wl.endswith(suf) and len(wl) > len(suf) + 2 for suf in suffixes)


def detect_spoonerisms(index: dict, phonemizer: Phonemizer, lang: str) -> dict:
    """
    Spoonerism-style word pairs: two single words sharing an identical
    phonetic rime (>= 4 phonemes) but differing in their onset consonant(s),
    a word-level proxy for the onset transposition behind true spoonerisms
    (which operate on phrases: "blushing crow" / "crushing blow"). Words with
    a productive POS-changing suffix are excluded, since large suffix families
    otherwise dominate the rime buckets.
    """
    onset_re = re.compile(r'^([^aeiouəɪʊɛɔæɑʌ]*)(.*)$')
    all_words = list(index['words'].keys())
    phonemizer.transcribe_batch(all_words)

    by_rime = defaultdict(list)
    for lemma in all_words:
        if has_pos_changing_suffix(lang, lemma):
            continue
        ipa = strip_ipa_stress(phonemizer.get(lemma))
        if not ipa:
            continue
        m = onset_re.match(ipa)
        onset, rime = (m.group(1), m.group(2)) if m else ('', ipa)
        # require a longer, more distinctive rime (>=4 phonemes) so short,
        # extremely common rimes (e.g. "-ed") don't dominate
        if onset and rime and len(rime) >= 4:
            by_rime[rime].append((lemma, onset))

    pairs = []
    seen_pairs = set()
    for rime, items in by_rime.items():
        if len(items) < 2 or len(items) > 200:
            continue
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                w1, onset1 = items[i]
                w2, onset2 = items[j]
                if onset1 == onset2 or w1 == w2:
                    continue
                pair_key = tuple(sorted((w1, w2)))
                if pair_key in seen_pairs:
                    continue
                seen_pairs.add(pair_key)
                pairs.append({'a': w1, 'b': w2, 'shared_rime': rime})

    pairs.sort(key=lambda p: (p['a'], p['b']))
    return {
        'pair_count': len(pairs),
        'examples': pairs[:SUMMARY_EXAMPLE_CAP],
        'all_pairs': pairs,
        'note': 'Detects single-word pairs sharing an identical phonetic rime but differing '
                'onset consonant(s) (e.g. "cat"/"hat"-style minimal pairs), used here as a '
                'word-level proxy for the onset-transposition mechanism behind true spoonerisms. '
                'True spoonerisms transpose onsets BETWEEN TWO WORDS IN A PHRASE ("blushing '
                'crow" / "crushing blow"), which requires a phrase corpus, not a lexicon — '
                'out of scope for WordNet-only data. Treat this category as illustrative only. '
                'Words carrying a known productive POS-changing derivational suffix for this '
                'language (e.g. EN "-ly"/"-ness", ES/PT "-mente", DE "-keit"/"-ung") are excluded '
                'beforehand, since large suffix families otherwise inflate pair counts through '
                'systematic derivation rather than genuine phonological coincidence. '
                'Sense/definition metadata is omitted here (unlike other categories) to keep '
                'file size manageable given the high pair count (tens of thousands per language) '
                '— cross-reference "lemma" against the homographs/polysemes detail for meanings.',
    }


# --------------------------------------------------------------------------
# Cross-lingual / etymological categories (Class III: released, not compared)
# --------------------------------------------------------------------------

def detect_cognates(indices: dict, base_lang='en') -> dict:
    """
    Candidate cognates: lemmas across two languages that map to the SAME ILI
    (the same meaning) and have high orthographic similarity. "Drift"
    candidates are pairs whose aligned definitions also differ substantially,
    a crude semantic-drift proxy. Reported per language against English.
    """
    results = {}
    en_by_ili = indices['en']['by_ili']

    for lang, index in indices.items():
        if lang == base_lang:
            continue
        pairs = []
        drifted = []
        for ili, en_entry in en_by_ili.items():
            other_entry = index['by_ili'].get(ili)
            if not other_entry:
                continue
            for en_lemma in en_entry['lemmas']:
                if not is_single_word(en_lemma):
                    continue
                for other_lemma in other_entry['lemmas']:
                    if not is_single_word(other_lemma):
                        continue
                    ratio = difflib.SequenceMatcher(
                        None, en_lemma.lower(), other_lemma.lower()
                    ).ratio()
                    if ratio >= COGNATE_MIN_RATIO and en_lemma.lower() != other_lemma.lower():
                        pair = {'en': en_lemma, lang: other_lemma, 'ratio': round(ratio, 3)}
                        pairs.append(pair)
                        def_ratio = difflib.SequenceMatcher(
                            None, en_entry['definition'], other_entry['definition']
                        ).ratio()
                        if def_ratio < 0.15:
                            drifted.append(pair)

        pairs.sort(key=lambda p: -p['ratio'])
        results[lang] = {
            'candidate_cognate_pairs': len(pairs),
            'examples': pairs[:25],
            'possible_semantic_drift_candidates': len(drifted),
            'drift_examples': drifted[:15],
        }
    return {
        'note': f'Candidate cognates = lemma pairs sharing an ILI-aligned synset (same meaning) '
                f'with orthographic similarity >= {COGNATE_MIN_RATIO} (difflib ratio) between '
                f'English and the target language. This detects FORM similarity only, not shared '
                f'Latin/other etymology, so false positives (coincidental resemblance) and false '
                f'negatives (real cognates with divergent modern spelling, e.g. "ship"/"eschipe") '
                f'both occur. "Drift candidates" additionally require definition strings to differ '
                f'a lot across the aligned pair (crude proxy — not real sense-divergence analysis).',
        'by_language': results,
    }


def detect_doublets(index: dict) -> dict:
    """
    Candidate doublets: two DIFFERENT lemmas in the SAME language that map to
    the SAME synset and are moderately similar in form (ruling out pure
    coincidence) but not so similar that they're inflectional variants.
    """
    pairs = []
    seen = set()
    for synset_id, entry in index['by_synset'].items():
        lemmas = [l for l in entry['lemmas'] if is_single_word(l)]
        for i in range(len(lemmas)):
            for j in range(i + 1, len(lemmas)):
                w1, w2 = lemmas[i], lemmas[j]
                if w1.lower() == w2.lower():
                    continue
                ratio = difflib.SequenceMatcher(None, w1.lower(), w2.lower()).ratio()
                if DOUBLET_MIN_RATIO <= ratio <= DOUBLET_MAX_RATIO:
                    pair_key = tuple(sorted((w1.lower(), w2.lower())))
                    if pair_key not in seen:
                        seen.add(pair_key)
                        pairs.append({'a': w1, 'b': w2, 'ratio': round(ratio, 3), 'synset_id': synset_id})

    pairs.sort(key=lambda p: -p['ratio'])
    full = [
        {**p, 'definition': index['by_synset'][p['synset_id']]['definition']}
        for p in pairs
    ]
    return {
        'candidate_pairs': len(pairs),
        'examples': pairs[:SUMMARY_EXAMPLE_CAP],
        'all_pairs': full,
        'note': f'Candidate doublets = two different lemmas sharing a synset (same meaning) with '
                f'form similarity in [{DOUBLET_MIN_RATIO}, {DOUBLET_MAX_RATIO}]. This is a same-'
                f'meaning + moderate-similarity heuristic, NOT verified shared etymology (WordNet '
                f'has no etymology data) — many pairs will just be near-synonyms that happen to '
                f'look alike, and real doublets with very different modern forms (e.g. "hospital"/'
                f'"hotel") will be missed since their similarity ratio is too low to bucket them here.',
    }


# --------------------------------------------------------------------------
# Fan-in ("concept-collapse") matrix, paper §3.4 and §5.4
# --------------------------------------------------------------------------
#
# For a cluster of related English WordNet concepts (e.g. every hyponym of
# "cut"), count how many DISTINCT words each language uses to cover that same
# cluster (via shared ILI), relative to how many distinct English words cover
# it. A ratio well below 1.0 means the language reuses a smaller set of words
# across the concepts (e.g. Spanish "cortar" covering many English "cut" senses).

MIN_CLUSTER_HYPONYMS = 20  # clusters smaller than this are too noisy
MIN_EN_WORD_DENSITY = 0.8  # english_words / concept_count below this makes the ratio unreliable
                           # (English itself reuses few lemmas across many concepts, deflating
                           # the denominator and inflating every other language's ratio)


def find_minimal_concept_clusters(pos: str, min_size: int = MIN_CLUSTER_HYPONYMS) -> list:
    """
    Find "minimal qualifying" hypernym-rooted clusters in English WordNet:
    synsets whose hyponym closure (including themselves) has >= min_size
    members, where no direct hyponym child ALSO qualifies. This avoids
    picking a broad ancestor (e.g. "move") when a more specific descendant
    (e.g. "walk") already forms its own qualifying cluster.
    """
    synsets = wn.synsets(pos=pos, lexicon=EN_LEXICON)
    sizes = {}
    for s in synsets:
        sizes[s.id] = len(list(s.closure('hyponym'))) + 1  # +1 to include the root itself
    qualifying = {sid for sid, sz in sizes.items() if sz >= min_size}
    minimal = []
    # sorted, so the row order of the matrix (ties in the final sort keep this
    # order) does not depend on Python's per-run string hashing
    for sid in sorted(qualifying):
        s = wn.synset(sid)
        if not any(child.id in qualifying for child in s.hyponyms()):
            minimal.append(sid)
    return minimal


def analyze_concept_cluster(root_id: str, langs: dict,
                            f3_exempt=CAPITALIZATION_MARKS_NOUN_LANGUAGES) -> dict:
    """
    Fan-in ratio for one concept cluster across all languages in `langs`
    ({lang_code: lexicon}), relative to English. Lemmas are filtered by F1-F3
    and by F4 at cluster level (a lemma identical to any English lemma of the
    cluster is dropped). Returns None if the cluster has no usable English
    words. `f3_exempt` lists the languages excused from F3 (German, as
    everywhere else); passing an empty set measures German under F3 too.
    """
    root = wn.synset(root_id)
    cluster = [root] + list(root.closure('hyponym'))
    ilis = {s.ili.id for s in cluster if s.ili}

    en_lemmas = set()
    for ili in ilis:
        for s in wn.synsets(ili=ili, lexicon=langs['en']):
            for l in s.lemmas():
                if is_single_word(l) and not l[0].isupper():
                    en_lemmas.add(l.lower())
    en_count = len(en_lemmas)
    if en_count == 0:
        return None

    row = {
        'root_id': root_id,
        'root_lemma': root.lemmas()[0],
        'root_definition': root.definition() or '',
        'concept_count': len(ilis),
        'en_word_count': en_count,
        'en_word_density': round(en_count / len(ilis), 3) if ilis else 0,
        'ratios': {},
        'word_counts': {},
    }
    for lang, lexicon in langs.items():
        if lang == 'en':
            continue
        skip_cap_filter = lang in f3_exempt
        lemmas = set()
        for ili in ilis:
            for s in wn.synsets(ili=ili, lexicon=lexicon):
                for l in s.lemmas():
                    if not is_single_word(l):
                        continue
                    if l[0].isupper() and not skip_cap_filter:
                        continue
                    if l.lower() in en_lemmas:
                        continue  # F4
                    lemmas.add(l.lower())
        row['word_counts'][lang] = len(lemmas)
        row['ratios'][lang] = round(len(lemmas) / en_count, 3)
    return row


def build_concept_collapse_matrix(langs: dict, pos_list=('v', 'n')) -> dict:
    """
    One row per qualifying English concept cluster (verbs and nouns), with
    each non-English language's fan-in ratio relative to English.
    """
    all_rows = []
    for pos in pos_list:
        print(f'fan-in: finding minimal {pos!r} clusters (>= {MIN_CLUSTER_HYPONYMS} hyponyms)...',
              flush=True)
        cluster_roots = find_minimal_concept_clusters(pos)
        print(f'fan-in: {len(cluster_roots)} {pos!r} clusters found, analyzing...', flush=True)
        for i, root_id in enumerate(cluster_roots, 1):
            row = analyze_concept_cluster(root_id, langs)
            if row:
                row['pos'] = pos
                all_rows.append(row)
            if i % 100 == 0:
                print(f'fan-in:   {i}/{len(cluster_roots)} {pos!r} clusters processed', flush=True)

    non_english_langs = [l for l in langs if l != 'en']
    reliable_rows = [r for r in all_rows if r['en_word_density'] >= MIN_EN_WORD_DENSITY]

    def _summarise(rows):
        out = {}
        for lang in non_english_langs:
            ratios = [r['ratios'][lang] for r in rows]
            if not ratios:
                continue
            mean = sum(ratios) / len(ratios)
            if len(ratios) > 1:
                var = sum((v - mean) ** 2 for v in ratios) / (len(ratios) - 1)
                sd = round(var ** 0.5, 3)
            else:
                sd = None
            out[lang] = {
                'mean_fanin_ratio': round(mean, 3),
                'stdev': sd,
                'cluster_count': len(ratios),
            }
        return out

    # Verb and noun clusters are reported SEPARATELY as well as pooled: they
    # cover disjoint concept sets and behave differently, so any cross-language
    # claim should be read off the per-POS breakdown (paper Table 6).
    summary_by_lang = _summarise(reliable_rows)
    summary_by_lang_by_pos = {
        pos: _summarise([r for r in reliable_rows if r.get('pos') == pos])
        for pos in sorted({r.get('pos') for r in reliable_rows if r.get('pos')})
    }

    all_rows.sort(key=lambda r: sum(r['ratios'].values()) / len(r['ratios']))
    return {
        'note': f'Fan-in ratio = (distinct words language X uses for a concept cluster) / '
                f'(distinct English words for the same cluster), computed per cluster then '
                f'averaged. Clusters are "minimal qualifying" hypernym-rooted groups of English '
                f'WordNet synsets (>= {MIN_CLUSTER_HYPONYMS} hyponyms, no child cluster also '
                f'qualifying, to avoid nested/redundant clusters). Ratio < 1 = language reuses '
                f'fewer distinct words across the concept space than English (more collapse); '
                f'ratio > 1 = language uses MORE distinct words than English for the same space. '
                f'"summary_by_lang" excludes clusters where en_word_density < {MIN_EN_WORD_DENSITY} '
                f'(English itself heavily reuses synonyms within the cluster, which deflates the '
                f'denominator and can inflate other languages\' ratio without them genuinely '
                f'out-lexicalizing English) — use summary_by_lang for headline numbers, but '
                f'"clusters" includes every row (with en_word_density shown) for full transparency. '
                f'Prefer "summary_by_lang_by_pos" over the pooled "summary_by_lang" for any '
                f'cross-language claim: verb and noun clusters cover disjoint concept sets and '
                f'behave differently, so the pooled mean mixes two populations.',
        'min_cluster_hyponyms': MIN_CLUSTER_HYPONYMS,
        'min_en_word_density_for_summary': MIN_EN_WORD_DENSITY,
        'summary_by_lang': summary_by_lang,
        'summary_by_lang_by_pos': summary_by_lang_by_pos,
        'clusters': all_rows,
    }


# --------------------------------------------------------------------------
# Commands: install, check
# --------------------------------------------------------------------------

def english_with_placeholder_ilis(src_gz: str, dst: str) -> int:
    """
    Copy the official English WordNet 2020 file, numbering its proposed
    concepts (ili="in") in_i1, in_i2, ... in file order and dropping their
    <ILIDefinition> lines, which wn accepts only for ili="in". Everything else
    is copied unchanged. Returns the number of concepts numbered.
    """
    n = 0
    with gzip.open(src_gz, 'rt', encoding='utf-8') as fin, open(dst, 'w', encoding='utf-8') as fout:
        for line in fin:
            if '<ILIDefinition>' in line:
                continue
            if 'ili="in"' in line:
                n += 1
                line = line.replace('ili="in"', f'ili="in_i{n}"')
            fout.write(line)
    return n


def english_has_placeholder_ilis() -> bool:
    synset_id, ili = FIRST_PROPOSED_SYNSET
    s = wn.synset(synset_id, lexicon=EN_LEXICON)
    return bool(s.ili) and s.ili.id == ili


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def hybrid_source(lang: str, hybrid_dir: str) -> str:
    """The hybrid wordnet file for `lang`: from `hybrid_dir` if given, else downloaded."""
    if hybrid_dir:
        for name in (f'{lang}_hybrid.xml', f'{lang}_hybrid.zip'):
            path = os.path.join(hybrid_dir, name)
            if os.path.exists(path):
                return path
        sys.exit(f'neither {lang}_hybrid.xml nor {lang}_hybrid.zip found in {hybrid_dir}')
    url = f'{HYBRID_REPO}/raw/{HYBRID_COMMIT}/{lang}_hybrid.zip'
    print(f'downloading {url}...', flush=True)
    return str(wn.download(url, add=False))  # kept in wn's download cache


def cmd_install(args):
    installed = {(l.id, l.version) for l in wn.lexicons()}
    with tempfile.TemporaryDirectory() as tmp:
        lex, ver = LEXICONS['en']
        if (lex, ver) in installed:
            if not english_has_placeholder_ilis():
                sys.exit(f'{lex}:{ver} is installed without the ILI numbering the hybrid wordnets use. '
                         f'Remove it, then run install again:\n'
                         f'  python3 -c "import wn; wn.remove(\'{lex}:{ver}\')"')
            print(f'{lex}:{ver} already installed')
        else:
            print(f'downloading {lex}:{ver}...', flush=True)
            official = wn.download(f'{lex}:{ver}', add=False)
            numbered = os.path.join(tmp, 'english-wordnet-2020.xml')
            n = english_with_placeholder_ilis(official, numbered)
            if n != PROPOSED_ILI_COUNT:
                sys.exit(f'expected {PROPOSED_ILI_COUNT} proposed concepts in {official}, found {n}')
            print(f'numbered {n} proposed concepts; adding {lex}:{ver}...', flush=True)
            wn.add(numbered)

        for lang, expected in HYBRID_SHA256.items():
            lex, ver = LEXICONS[lang]
            if (lex, ver) in installed:
                print(f'{lex}:{ver} already installed')
                continue
            path = hybrid_source(lang, args.hybrid_dir)
            if zipfile.is_zipfile(path):
                with zipfile.ZipFile(path) as z:
                    path = z.extract(f'{lang}_hybrid.xml', tmp)
            if sha256(path) != expected:
                sys.exit(f'{lang}_hybrid.xml differs from the file the paper used (SHA-256 mismatch)')
            print(f'adding {lex}:{ver}...', flush=True)
            wn.add(path)
    print('\nAll seven lexicons installed.')


def espeak_version() -> str:
    try:
        out = subprocess.run(['espeak-ng', '--version'], capture_output=True, text=True).stdout
    except FileNotFoundError:
        return None
    m = re.search(r'text-to-speech:\s*(\S+)', out)
    return m.group(1) if m else out.strip()


def check_environment() -> list:
    """Print the software/lexicon status; return the list of blocking problems."""
    problems = []
    found = {
        'python': sys.version.split()[0],
        'wn': getattr(wn, '__version__', '?'),
        'espeak-ng': espeak_version(),
    }
    for name, expected in TESTED_VERSIONS.items():
        have = found[name]
        if have is None:
            status = 'MISSING'
            problems.append(f'{name} is not installed (see README.md, "Installation")')
        elif have == expected:
            status = 'ok'
        else:
            status = f'differs from the tested {expected}; figures may not match exactly'
        print(f'  {name:<10} {have or "-":<10} {status}')

    installed = {(l.id, l.version) for l in wn.lexicons()}
    for lang, (lex, ver) in LEXICONS.items():
        ok = (lex, ver) in installed
        status = 'ok' if ok else 'MISSING'
        if ok and lang == 'en' and not english_has_placeholder_ilis():
            ok, status = False, 'lacks the ILI numbering of the hybrid wordnets'
        print(f'  lexicon    {lex + ":" + ver:<10} {status}')
        if not ok:
            problems.append(f'lexicon {lex}:{ver} ({lang}): {"not installed" if status == "MISSING" else status} '
                            f'(see README.md, "Install the seven lexicons")')
    return problems


def cmd_check(args):
    problems = check_environment()
    if problems:
        print('\nProblems:\n  ' + '\n  '.join(problems))
        sys.exit(1)
    print('\nAll inputs present.')


def require_environment():
    problems = check_environment()
    if problems:
        sys.exit('Cannot continue:\n  ' + '\n  '.join(problems))


# --------------------------------------------------------------------------
# Command: detect
# --------------------------------------------------------------------------

# keys inside each category's result dict that hold the untruncated data —
# these are stripped out of the summary JSON and are the payload of the
# per-language detail JSON (alongside count/notes)
FULL_DATA_KEYS = ('all_matches', 'all_pairs', 'all_clusters')


def split_summary_and_full(category_result: dict) -> tuple:
    """
    Given one category's detector output (truncated 'examples' plus
    untruncated 'all_*' data), return (summary, full).
    """
    summary = {k: v for k, v in category_result.items() if k not in FULL_DATA_KEYS}
    full = {k: v for k, v in category_result.items() if k not in ('examples',)}
    return summary, full


def run_language(lang: str, index: dict) -> tuple:
    print(f'[{lang}] running detectors...', flush=True)
    lexicon = LANGUAGES[lang]
    phonemizer = Phonemizer(lang)

    categories = {
        'homographs': detect_homographs(index),
        'heteronyms': detect_heteronyms(index),
        'homonyms': detect_homonyms(index),
        'polysemes': detect_polysemes(index),
        'contronyms': detect_contronyms(index, lexicon, lang),
        'palindromes': detect_palindromes(index),
        'homophones': detect_homophones(index, phonemizer),
        'near_homophones': detect_near_homophones(index, phonemizer, lang),
        'spoonerism_word_pairs': detect_spoonerisms(index, phonemizer, lang),
        'doublets': detect_doublets(index),
    }

    header = {
        'lexicon': lexicon,
        'single_word_lemma_count': len(index['words']),
        'synset_count': len(index['by_synset']),
        'filter_stats': index['filter_stats'],
    }

    summary = dict(header)
    full = dict(header)
    for name, result in categories.items():
        cat_summary, cat_full = split_summary_and_full(result)
        summary[name] = cat_summary
        full[name] = cat_full

    print(f'[{lang}] done.', flush=True)
    return summary, full


def write_json(path: str, data) -> None:
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    print(f'wrote {path}', flush=True)


def cmd_detect(args):
    require_environment()
    out_dir = args.out_dir
    os.makedirs(out_dir, exist_ok=True)

    # English is loaded first so its per-ILI lemma set can drive F4 for every
    # other language
    indices = {'en': load_language_index('en')}
    en_lemmas = english_lemmas_by_ili(indices['en'])
    for lang in LANGUAGES:
        if lang != 'en':
            indices[lang] = load_language_index(lang, en_lemmas)

    output = {'languages': {}}
    for lang in LANGUAGES:
        summary, full = run_language(lang, indices[lang])
        output['languages'][lang] = summary
        write_json(os.path.join(out_dir, f'{lang}.json'), full)

    print('running cross-lingual cognate detection...', flush=True)
    output['cognates'] = detect_cognates(indices, base_lang='en')

    # the alignment facts of paper §2.1: the ILIs every lexicon covers, and
    # whether every hybrid synset id carries its inferred-wordnet prefix
    # ('inde-...' etc.), i.e. whether provenance is recoverable from the id
    output['alignment'] = {
        'shared_ili_count': len(set.intersection(*(set(ix['by_ili']) for ix in indices.values()))),
        'synsets_with_inferred_prefix': {
            lang: sum(1 for sid in indices[lang]['by_synset'] if sid.startswith(f'in{lang}-'))
            for lang in LANGUAGES if lang != 'en'
        },
    }
    write_json(os.path.join(out_dir, 'linguistic_anomalies.json'), output)

    if not args.no_fanin:
        print('building fan-in matrix (the slowest step)...', flush=True)
        matrix = build_concept_collapse_matrix(LANGUAGES)
        write_json(os.path.join(out_dir, 'concept_collapse_matrix.json'), matrix)


# --------------------------------------------------------------------------
# Command: sensitivity
# --------------------------------------------------------------------------

def homophone_rate(index: dict, phonemizer: Phonemizer, filters: Filters = PROTOCOL) -> tuple:
    """
    (vocab/clusters/words/rate row, full detector result) for one setting.

    Give every index its own Phonemizer, shared only between settings of that
    same index. espeak-ng's batch mode transcribes about 0.2% of words slightly
    differently depending on the neighbouring words in the batch (a final
    phoneme dropped, or part of the next word attached), so a vocabulary must
    be transcribed as one batch sequence of its own, as `detect` does, for its
    figures to match the paper.
    """
    result = detect_homophones(index, phonemizer, filters)
    vocab = len(index['words'])
    row = {'vocab': vocab, 'clusters': result['cluster_count'], 'words': result['words_involved'],
           'rate': round(100 * result['words_involved'] / vocab, 3)}
    return row, result


def cluster_sets(result: dict) -> set:
    return {frozenset(w['lemma'] for w in c['words']) for c in result['all_clusters']}


def verb_polysemy(homographs: list) -> dict:
    """
    Verb polysemy over a list of {'lemma', 'senses': [{'pos', ...}]} homographs.
      table5:       lemmas with >= 2 verb senses, and their mean verb-sense count
                    (paper Table 5; "most polysemous" by verb senses)
      any_verb:     homographs with >= 1 verb sense, and their mean verb-sense
                    count (a broader definition, reported for comparison only)
    """
    def n_verb(m):
        return sum(1 for s in m['senses'] if s['pos'] == 'v')

    table5 = [m for m in homographs if n_verb(m) >= 2]
    any_verb = [m for m in homographs if n_verb(m) >= 1]
    top = max(table5, key=lambda m: (n_verb(m), m['lemma']))
    return {
        'table5_verbs': len(table5),
        'table5_mean_senses': sum(map(n_verb, table5)) / len(table5),
        'table5_most_polysemous': top['lemma'],
        'table5_most_polysemous_senses': n_verb(top),
        'any_verb_homographs': len(any_verb),
        'any_verb_mean_senses': sum(map(n_verb, any_verb)) / len(any_verb),
    }


def homograph_records(index: dict) -> list:
    return [{'lemma': l, 'senses': senses_for(index, l)}
            for l, entries in index['words'].items() if len({e['synset_id'] for e in entries}) >= 2]


def f4_partition(index: dict, english_lemmas: dict) -> dict:
    """
    Every single-word lemma-occurrence identical to an English lemma of the
    same ILI, split by whether the synset offers a genuine translation beside
    it — another single-word lemma that is not itself an English match — or
    not, in which case the English form is the synset's only target-language
    word, the strongest sign of an untranslated leftover (paper §3.2).
    Counted before F3, i.e. including capitalised forms.
    """
    alone = alongside = 0
    for entry in index['by_synset'].values():
        en = english_lemmas.get(entry['ili']) if entry['ili'] else None
        if not en:
            continue
        for lemma in entry['lemmas']:
            if is_single_word(lemma) and lemma.lower() in en:
                if any(is_single_word(other) and other.lower() not in en
                       for other in entry['lemmas'] if other != lemma):
                    alongside += 1
                else:
                    alone += 1
    return {'alone': alone, 'alongside': alongside, 'total': alone + alongside}


def cmd_sensitivity(args):
    require_environment()
    out_dir = args.out_dir
    os.makedirs(out_dir, exist_ok=True)
    results = {}

    en = load_language_index('en')
    en_lemmas = english_lemmas_by_ili(en)

    # Accent (§5.2): English under the rhotic en-us voice instead of en-gb
    print('accent: English under en-gb and en-us...', flush=True)
    ph_en = Phonemizer('en')
    gb_row, gb = homophone_rate(en, ph_en)
    us_row, us = homophone_rate(en, Phonemizer('en', voice='en-us'))
    gb_sets, us_sets = cluster_sets(gb), cluster_sets(us)
    accent = {
        'en-gb': {k: gb_row[k] for k in ('clusters', 'words', 'rate')},
        'en-us': {k: us_row[k] for k in ('clusters', 'words', 'rate')},
        'gb_only': sorted(sorted(c) for c in gb_sets - us_sets)[:40],
        'us_only': sorted(sorted(c) for c in us_sets - gb_sets)[:40],
        'vocab': len(en['words']),
        'n_gb_only': len(gb_sets - us_sets),
        'n_us_only': len(us_sets - gb_sets),
        'n_shared': len(gb_sets & us_sets),
    }
    write_json(os.path.join(out_dir, 'accent_sensitivity_en.json'), accent)

    # F5 (Table 2): English homophones without the synset-sharing merge
    f5_off, _ = homophone_rate(en, ph_en, Filters(f5=False))
    results['f5_off_en'] = f5_off
    results['en_any_verb_polysemy'] = verb_polysemy(homograph_records(en))

    # F4 (§3.2): French and German homophones with F4 disabled, and the
    # alone/alongside split of the forms F4 matches
    f4 = {}
    indices = {}
    no_f4 = Filters(f4=False)
    for lang in ('fr', 'de'):
        indices[lang] = load_language_index(lang, en_lemmas)
        f4[f'{lang}_F4_on'], _ = homophone_rate(indices[lang], Phonemizer(lang))
        indices[f'{lang}_no_f4'] = load_language_index(lang, en_lemmas, no_f4)
        f4[f'{lang}_F4_off'], _ = homophone_rate(indices[f'{lang}_no_f4'], Phonemizer(lang), no_f4)
        results[f'f4_partition_{lang}'] = f4_partition(indices[lang], en_lemmas)
    write_json(os.path.join(out_dir, 'f4_sensitivity.json'), f4)

    # F6 (Table 2, §5.2): German homophones without the case-only merge
    f6_off_row, f6_off = homophone_rate(indices['de'], Phonemizer('de'), Filters(f6=False))
    f6_off_row['case_only_clusters'] = sum(
        1 for c in f6_off['all_clusters'] if len({w['lemma'].lower() for w in c['words']}) == 1)
    results['f6_off_de'] = f6_off_row

    # F3 (§3.2): share of German single-word forms that F3 would remove. The
    # figure dates from before F4, so it is measured without F4 (75%); with
    # F4 applied the share is 72%.
    de_no_f4 = indices['de_no_f4']
    results['de_capitalised_share'] = {
        'capitalised_forms': sum(1 for w in de_no_f4['words'] if w[0].isupper()),
        'vocab': len(de_no_f4['words']),
        'settings': 'F4 off',
    }

    # F3 (Table 2): Spanish under the softer rule that was tried first, which
    # keeps a capitalised lemma whenever a lowercase twin exists, against F3.
    # Measured as when F3 was tightened, i.e. before F4-F6 existed: F6 would
    # merge the very Cola/cola pairs at issue again.
    f1_to_f3 = Filters(f4=False, f5=False, f6=False)
    soft = Filters(f3='keep_if_lowercase_twin', f4=False, f5=False, f6=False)
    es_strict = load_language_index('es', en_lemmas, f1_to_f3)
    es_soft = load_language_index('es', en_lemmas, soft)
    results['f3_rules_es'] = {
        'settings': 'F4, F5 and F6 off',
        'drop': homophone_rate(es_strict, Phonemizer('es'), f1_to_f3)[0],
        'keep_if_lowercase_twin': homophone_rate(es_soft, Phonemizer('es'), soft)[0],
    }

    # §5.3: Spanish verb polysemy with F4 disabled (the same index: F5 and F6
    # do not affect homographs)
    results['es_f4_off_any_verb_polysemy'] = verb_polysemy(homograph_records(es_strict))

    # §5.4: German fan-in with F3 applied to German as well, over the
    # reliable clusters of the main run
    matrix_path = os.path.join(out_dir, 'concept_collapse_matrix.json')
    if os.path.exists(matrix_path):
        print('fan-in: German with F3 applied...', flush=True)
        matrix = load_json(matrix_path)
        de_f3 = {}
        for pos in ('v', 'n'):
            roots = [r['root_id'] for r in matrix['clusters']
                     if r['pos'] == pos and r['en_word_density'] >= MIN_EN_WORD_DENSITY]
            ratios = [analyze_concept_cluster(root, {'en': EN_LEXICON, 'de': LANGUAGES['de']},
                                              f3_exempt=frozenset())['ratios']['de'] for root in roots]
            de_f3[pos] = {'mean_fanin_ratio': sum(ratios) / len(ratios), 'cluster_count': len(ratios)}
        results['de_fanin_with_f3'] = de_f3
    else:
        print(f'skipping German fan-in re-run: {matrix_path} not found (run `detect` first)')

    write_json(os.path.join(out_dir, 'filter_sensitivity.json'), results)


# --------------------------------------------------------------------------
# Command: annotation
# --------------------------------------------------------------------------
#
# Stratified random samples for human precision annotation (paper §4): one TSV
# per (language, category) with a blank `correct` column for an annotator to
# fill in with 1 (a genuine instance) or 0 (a false positive), plus a
# free-text `note` column. Precision is then mean(correct). Sampling is seeded
# so the drawn items are fixed in advance and can be released with the sheets.

ANNOTATION_CATEGORIES = {
    'homophones':      ('all_clusters', lambda c: ' / '.join(w['lemma'] for w in c['words'])),
    'near_homophones': ('all_pairs',    lambda p: f"{p['a']} ~ {p['b']}"),
    'palindromes':     ('all_matches',  lambda m: m['lemma']),
}
ANNOTATION_LANGUAGES = ['en', 'de']
ANNOTATION_SEED = 20261016
ANNOTATION_N = 50


def annotation_gloss(item, cat):
    if cat == 'homophones':
        return ' || '.join(
            f"{w['lemma']}: " + '; '.join(s['definition'][:60] for s in w['senses'][:2])
            for w in item['words'])
    if cat == 'near_homophones':
        a = '; '.join(s['definition'][:60] for s in item.get('a_senses', [])[:1])
        b = '; '.join(s['definition'][:60] for s in item.get('b_senses', [])[:1])
        return f"{item['a']}: {a} || {item['b']}: {b}"
    return '; '.join(s['definition'][:80] for s in item.get('senses', [])[:2])


def cmd_annotation(args):
    sheet_dir = os.path.join(args.out_dir, 'annotation')
    os.makedirs(sheet_dir, exist_ok=True)
    for lang in args.languages:
        data = load_json(os.path.join(args.out_dir, f'{lang}.json'))
        for cat, (key, render) in ANNOTATION_CATEGORIES.items():
            pool = data.get(cat, {}).get(key, [])
            if not pool:
                print(f'{lang}/{cat}: empty, skipped')
                continue
            rng = random.Random(f'{args.seed}-{lang}-{cat}')
            sample = rng.sample(pool, min(args.n, len(pool)))
            path = os.path.join(sheet_dir, f'{lang}_{cat}.tsv')
            with open(path, 'w', encoding='utf-8') as f:
                f.write('id\titem\tcorrect\tnote\tgloss\n')
                for i, it in enumerate(sample, 1):
                    f.write(f'{i}\t{render(it)}\t\t\t{annotation_gloss(it, cat)}\n')
            print(f'{lang}/{cat}: wrote {len(sample)} of {len(pool)} -> {path}')


# --------------------------------------------------------------------------
# Statistics (stdlib only)
# --------------------------------------------------------------------------

def pearson(xs, ys) -> float:
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    return sxy / math.sqrt(sxx * syy)


def ranks(values) -> list:
    """1-based ranks, ties sharing their average rank."""
    order = sorted(range(len(values)), key=lambda i: values[i])
    result = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and values[order[j + 1]] == values[order[i]]:
            j += 1
        for k in range(i, j + 1):
            result[order[k]] = (i + j) / 2 + 1
        i = j + 1
    return result


def spearman(xs, ys) -> float:
    return pearson(ranks(xs), ranks(ys))


def _betacf(a, b, x):
    """Continued fraction for the regularised incomplete beta (Numerical Recipes 6.4)."""
    tiny = 1e-300
    qab, qap, qam = a + b, a + 1, a - 1
    c, d = 1.0, 1 - qab * x / qap
    d = 1 / (d if abs(d) > tiny else tiny)
    h = d
    for m in range(1, 300):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1 + aa * d
        d = 1 / (d if abs(d) > tiny else tiny)
        c = 1 + aa / c
        c = c if abs(c) > tiny else tiny
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1 + aa * d
        d = 1 / (d if abs(d) > tiny else tiny)
        c = 1 + aa / c
        c = c if abs(c) > tiny else tiny
        delta = d * c
        h *= delta
        if abs(delta - 1) < 1e-15:
            break
    return h


def betainc(a, b, x) -> float:
    if x <= 0 or x >= 1:
        return 0.0 if x <= 0 else 1.0
    front = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
                     + a * math.log(x) + b * math.log(1 - x))
    if x < (a + 1) / (a + b + 2):
        return front * _betacf(a, b, x) / a
    return 1 - front * _betacf(b, a, 1 - x) / b


def correlation_test(xs, ys) -> dict:
    """Pearson r with its t statistic and two-sided p (df = n - 2)."""
    r = pearson(xs, ys)
    df = len(xs) - 2
    t = r * math.sqrt(df) / math.sqrt(1 - r * r)
    p = betainc(df / 2, 0.5, df / (df + t * t))
    return {'r': r, 'r2': r * r, 't': t, 'df': df, 'p': p}


# --------------------------------------------------------------------------
# CLEARPOND (Marian et al. 2012), the external benchmark of paper §5.2
# --------------------------------------------------------------------------

CLEARPOND_FILES = {'en': 'english', 'nl': 'dutch', 'fr': 'french', 'de': 'german', 'es': 'spanish'}
# column 29 of each language file is that language's own PTAN (phonological
# neighbours: total, all types, count), e.g. ePTAN in the English file and
# fPTAN in the French one; the headers file in each download confirms this
CLEARPOND_PTAN_COLUMN = 29
CLEARPOND_PTAN_HEADER = {'en': 'ePTAN', 'nl': 'dPTAN', 'fr': 'fPTAN', 'de': 'gPTAN', 'es': 'sPTAN'}
CLEARPOND_HEADER_FILE = {'en': 'EN', 'nl': 'NL', 'fr': 'FR', 'de': 'DE', 'es': 'SP'}


CLEARPOND_URL = 'https://clearpond.northwestern.edu/{stem}CPdatabase2.zip'


def _clearpond_open(location: str, name: str):
    """Open `name` from a downloaded .zip file, or from a folder of .zip or extracted files."""
    if zipfile.is_zipfile(location):
        zips = [location]
    else:
        path = os.path.join(location, name)
        if os.path.exists(path):
            return open(path, encoding='latin-1')
        zips = [os.path.join(location, z) for z in sorted(os.listdir(location)) if z.lower().endswith('.zip')]
    for zpath in zips:
        z = zipfile.ZipFile(zpath)
        if name in z.namelist():
            return io.TextIOWrapper(z.open(name), encoding='latin-1')
    return None


def clearpond_mean_ptan(directory: str = None) -> dict:
    """
    Mean within-language phonological neighbourhood size per language, from
    local copies in `directory`, or else from the CLEARPOND website (the
    downloads are kept in wn's download cache).
    """
    means = {}
    for lang, stem in CLEARPOND_FILES.items():
        location = directory
        if location is None:
            url = CLEARPOND_URL.format(stem=stem)
            print(f'downloading {url}...', flush=True)
            location = str(wn.download(url, add=False))
        header = _clearpond_open(location, f'clearpondHeaders_{CLEARPOND_HEADER_FILE[lang]}.txt')
        if header is not None:
            columns = header.read().split()
            if columns[CLEARPOND_PTAN_COLUMN] != CLEARPOND_PTAN_HEADER[lang]:
                sys.exit(f'CLEARPOND {stem}: column {CLEARPOND_PTAN_COLUMN} is '
                         f'{columns[CLEARPOND_PTAN_COLUMN]}, expected {CLEARPOND_PTAN_HEADER[lang]}')
        data = _clearpond_open(location, f'{stem}CPdatabase2.txt')
        if data is None:
            sys.exit(f'CLEARPOND file {stem}CPdatabase2.txt (or its .zip) not found in {location}')
        values = [float(line.rstrip('\r\n').split('\t')[CLEARPOND_PTAN_COLUMN])
                  for line in data if line.strip()]
        means[lang] = sum(values) / len(values)
    return means


# --------------------------------------------------------------------------
# Command: report
# --------------------------------------------------------------------------

# Table 1 of the paper: hand-curated base synsets reported by Bergh et al.
# (2025), against the 120,135 OEWN synsets of their release. These are inputs
# taken from that paper, not measured here; they feed the composition test.
BERGH_BASE_SYNSETS = {'fr': 59091, 'pt': 43895, 'es': 38512, 'de': 36268, 'it': 35001, 'nl': 30177}
BERGH_OEWN_SYNSETS = 120135

PAPER_LANG_ORDER = ['en', 'it', 'es', 'fr', 'nl', 'pt', 'de']  # column order of Table 3
FANIN_LANGS = ['it', 'es', 'fr', 'nl', 'pt', 'de']


def load_json(path):
    with open(path, encoding='utf-8') as f:
        return json.load(f)


def format_like(paper: str, value) -> str:
    """Format `value` the way `paper` is printed (decimals, separators, %, ×, ≈)."""
    if isinstance(value, bool):
        return 'yes' if value else 'no'
    if isinstance(value, str):
        return value
    text = paper.replace('−', '-')
    prefix = text[0] if text[0] in '≈~' else ''
    suffix = text[-1] if text[-1] in '%×' else ''
    number = text[len(prefix):len(text) - len(suffix)]
    decimals = len(number.split('.')[1]) if '.' in number else 0
    out = f'{value:,.{decimals}f}' if ',' in number else f'{value:.{decimals}f}'
    if float(out.replace(',', '')) == 0:
        out = out.lstrip('-')
    if number.startswith('+') and not out.startswith('-'):
        out = '+' + out
    return prefix + out + suffix


def _as_number(text: str):
    text = text.replace('−', '-').lstrip('≈~').rstrip('%×').replace(',', '').lstrip('+')
    try:
        return float(text)
    except ValueError:
        return None


def is_close(paper: str, shown: str) -> bool:
    """Within one unit of the last digit the paper prints (e.g. 13.43 for 13.42)."""
    a, b = _as_number(paper), _as_number(shown)
    if a is None or b is None:
        return False
    number = paper.rstrip('%×')
    unit = 10 ** -(len(number.split('.')[1]) if '.' in number else 0)
    return abs(a - b) <= unit * 1.0001


class Report:
    """Collects (paper value, reproduced value) pairs, grouped by paper section."""

    def __init__(self):
        self.sections = []

    def section(self, title):
        self.sections.append((title, []))

    def check(self, item, paper, value):
        shown = format_like(paper, value)
        if value is None:
            status = 'skipped'
        elif shown.replace('−', '-') == paper.replace('−', '-'):
            status = 'match'
        else:
            status = 'close' if is_close(paper, shown) else 'DIFFERS'
        self.sections[-1][1].append({'item': item, 'paper': paper,
                                     'reproduced': shown if value is not None else '-',
                                     'status': status})

    def skip(self, item, paper, reason):
        self.sections[-1][1].append({'item': item, 'paper': paper, 'reproduced': reason,
                                     'status': 'skipped'})

    def rows(self):
        return [r for _, rows in self.sections for r in rows]

    def counts(self) -> dict:
        return {s: sum(1 for r in self.rows() if r['status'] == s)
                for s in ('match', 'close', 'DIFFERS', 'skipped')}

    def summary(self) -> str:
        c = self.counts()
        return (f'{c["match"]} figures match the paper, {c["close"]} are within one unit of '
                f'its last printed digit, {c["DIFFERS"]} differ, {c["skipped"]} skipped.')

    def markdown(self) -> str:
        lines = ['# Paper figures, reproduced', '',
                 'Every number in the paper *What Can Be Counted Over Aligned Wordnets?* that is '
                 'computed from the data, next to the value `program.py` produces. Generated by '
                 '`python3 program.py report`.', '',
                 '✓ identical at the precision the paper prints · ≈ within one unit of the last printed '
                 'digit · ✗ differs · – skipped', '',
                 f'**{self.summary()}**', '']
        for title, rows in self.sections:
            lines += [f'## {title}', '', '| Item | Paper | Reproduced | |', '|---|---|---|---|']
            for r in rows:
                mark = {'match': '✓', 'close': '≈', 'DIFFERS': '✗', 'skipped': '–'}[r['status']]
                lines.append(f"| {r['item']} | {r['paper']} | {r['reproduced']} | {mark} |")
            lines.append('')
        return '\n'.join(lines)


def cmd_report(args):
    out_dir = args.out_dir
    S = load_json(os.path.join(out_dir, 'linguistic_anomalies.json'))
    M = load_json(os.path.join(out_dir, 'concept_collapse_matrix.json'))
    L = S['languages']
    sens_path = os.path.join(out_dir, 'filter_sensitivity.json')
    have_sens = os.path.exists(sens_path)
    if have_sens:
        sens = load_json(sens_path)
        accent = load_json(os.path.join(out_dir, 'accent_sensitivity_en.json'))
        f4 = load_json(os.path.join(out_dir, 'f4_sensitivity.json'))
    else:
        print(f'note: {sens_path} not found; run `sensitivity` first for the full report')
    detail = {lang: load_json(os.path.join(out_dir, f'{lang}.json')) for lang in ('en', 'es', 'fr')}
    try:
        ptan = clearpond_mean_ptan(args.clearpond)
    except wn.Error as e:
        ptan = None
        print(f'note: CLEARPOND could not be downloaded ({e}); the CLEARPOND checks are skipped')

    vocab = {l: L[l]['single_word_lemma_count'] for l in PAPER_LANG_ORDER}
    hp = {l: L[l]['homophones'] for l in PAPER_LANG_ORDER}
    rate = {l: 100 * hp[l]['words_involved'] / vocab[l] for l in PAPER_LANG_ORDER}
    cp_langs = ['fr', 'en', 'de', 'nl', 'es']  # Table 4 row order

    def cp_r(rates, langs=cp_langs):
        return pearson([ptan[l] for l in langs], [rates[l] for l in langs])

    R = Report()

    def need_sens(item, paper, fn):
        try:
            R.check(item, paper, fn()) if have_sens else R.skip(item, paper, 'run `sensitivity`')
        except KeyError:  # a part of `sensitivity` that was skipped
            R.skip(item, paper, 'not in the `sensitivity` output')

    def need_cp(item, paper, fn):
        if ptan is not None:
            R.check(item, paper, fn())
        else:
            R.skip(item, paper, 'needs --clearpond')

    # ---- §2.1 and Table 1
    R.section('§2.1 Lexicons, and Table 1')
    R.check('ILI concepts shared by all seven wordnets', '120,053', S['alignment']['shared_ili_count'])
    for lang in FANIN_LANGS:
        R.check(f'{lang.upper()} synsets carrying the inferred prefix (all of them)', '120,053',
                S['alignment']['synsets_with_inferred_prefix'][lang])
    share = {l: 100 * BERGH_BASE_SYNSETS[l] / BERGH_OEWN_SYNSETS for l in FANIN_LANGS}
    for lang in ['fr', 'pt', 'es', 'de', 'it', 'nl']:
        R.check(f'Table 1 {lang.upper()} hand-curated share (from Bergh et al. base counts)',
                {'fr': '49%', 'pt': '37%', 'es': '32%', 'de': '30%', 'it': '29%', 'nl': '25%'}[lang],
                share[lang])
    R.check('machine-derived share, lowest', '51%', 100 - max(share.values()))
    R.check('machine-derived share, highest', '75%', 100 - min(share.values()))

    # ---- Table 2 and §3.2
    R.section('Table 2 and §3.2: filtering protocol')
    f4_paper = {'de': '35,892', 'it': '24,649', 'fr': '23,803', 'nl': '21,502', 'pt': '15,299', 'es': '11,714'}
    for lang, paper in f4_paper.items():
        R.check(f'F4 lemma-occurrences removed, {lang.upper()}', paper, L[lang]['filter_stats']['f4_dropped'])
    need_sens('F3: ES clusters under the rejected softer rule ÷ under F3 (F4-F6 off)', '≈9×',
              lambda: sens['f3_rules_es']['keep_if_lowercase_twin']['clusters'] / sens['f3_rules_es']['drop']['clusters'])
    need_sens('F5: EN clusters without F5 ÷ with F5', '≈3×',
              lambda: sens['f5_off_en']['clusters'] / hp['en']['cluster_count'])
    need_sens('F6: DE clusters without F6', '3,032', lambda: sens['f6_off_de']['clusters'])
    R.check('F6: DE clusters with F6', '144', hp['de']['cluster_count'])
    need_sens('F6: share of those that are case-only pairs', '95%',
              lambda: 100 * sens['f6_off_de']['case_only_clusters'] / sens['f6_off_de']['clusters'])
    for lang, alone_paper, along_paper in [('fr', '77%', '23%'), ('de', '75%', '25%')]:
        need_sens(f'F4 matches that are the synset\'s only lemma, {lang.upper()}', alone_paper,
                  lambda lang=lang: 100 * sens[f'f4_partition_{lang}']['alone'] / sens[f'f4_partition_{lang}']['total'])
        need_sens(f'F4 matches alongside other lemmas, {lang.upper()}', along_paper,
                  lambda lang=lang: 100 * sens[f'f4_partition_{lang}']['alongside'] / sens[f'f4_partition_{lang}']['total'])
    need_sens('FR homophone rate with F4 (%)', '9.83', lambda: 100 * f4['fr_F4_on']['words'] / f4['fr_F4_on']['vocab'])
    need_sens('FR homophone rate without F4 (%)', '8.50', lambda: 100 * f4['fr_F4_off']['words'] / f4['fr_F4_off']['vocab'])
    need_sens('DE homophone rate with F4 (%)', '0.33', lambda: 100 * f4['de_F4_on']['words'] / f4['de_F4_on']['vocab'])
    need_sens('DE homophone rate without F4 (%)', '1.23', lambda: 100 * f4['de_F4_off']['words'] / f4['de_F4_off']['vocab'])
    need_sens('share of German vocabulary F3 would remove (F4 off)', '~75%',
              lambda: 100 * sens['de_capitalised_share']['capitalised_forms'] / sens['de_capitalised_share']['vocab'])

    # ---- §4 and Table 3
    R.section('§4 and Table 3: filtered counts')
    R.check('smallest vocabulary (FR)', '33,746', min(vocab.values()))
    R.check('largest vocabulary (DE)', '88,389', max(vocab.values()))
    table3 = [
        ('Single-word lemmas', lambda l: vocab[l],
         ['64,467', '43,885', '35,703', '33,746', '65,149', '35,706', '88,389']),
        ('Homophone clusters', lambda l: hp[l]['cluster_count'],
         ['861', '9', '106', '1,612', '124', '176', '144']),
        ('Words in clusters', lambda l: hp[l]['words_involved'],
         ['1,788', '18', '212', '3,316', '248', '354', '289']),
        ('Homophone rate (%)', lambda l: rate[l],
         ['2.77', '0.04', '0.59', '9.83', '0.38', '0.99', '0.33']),
        ('Near-homophone pairs', lambda l: L[l]['near_homophones']['pair_count'],
         ['293', '174', '180', '118', '194', '180', '140']),
        ('Palindromes', lambda l: L[l]['palindromes']['count'],
         ['55', '20', '16', '11', '39', '31', '10']),
        ('Homographs', lambda l: L[l]['homographs']['count'],
         ['21,260', '17,021', '14,933', '14,529', '19,888', '14,409', '24,428']),
        ('Homonyms', lambda l: L[l]['homonyms']['count'],
         ['7,855', '4,948', '4,727', '5,741', '5,990', '4,974', '5,060']),
        ('Polysemes', lambda l: L[l]['polysemes']['count'],
         ['18,484', '15,218', '13,427', '13,025', '17,770', '12,788', '22,772']),
    ]
    for label, get, papers in table3:
        for lang, paper in zip(PAPER_LANG_ORDER, papers):
            R.check(f'{label}, {lang.upper()}', paper, get(lang))

    # ---- §5.1
    R.section('§5.1: homophone density')
    R.check('FR rate ÷ IT rate', '240', rate['fr'] / rate['it'])
    italian = sorted(' / '.join(c) for c in L['it']['homophones']['examples'])
    paper_italian = sorted(['meta / metà', 'calamita / calamità', 'chassis / châssis', 'metro / métro',
                            'raion / rayon', 'secretaire / secrétaire', 'para / parà', 'papa / papà',
                            'antigenico / antigienico'])
    R.check('the nine Italian clusters', ', '.join(paper_italian), ', '.join(italian))
    fr_sets = cluster_sets(detail['fr']['homophones'])
    en_sets = cluster_sets(detail['en']['homophones'])
    for lang, sets, words in [('fr', fr_sets, 'sain/saint/sein'), ('fr', fr_sets, 'pain/peint/pin'),
                              ('en', en_sets, 'right/rite/wright/write'), ('en', en_sets, 'cent/scent/sent')]:
        R.check(f'{lang.upper()} {words} in one cluster', 'yes', any(set(words.split('/')) <= s for s in sets))

    # ---- Table 4 and §5.2
    R.section('Table 4 and §5.2: CLEARPOND validation')
    for lang, paper in zip(cp_langs, ['10.481', '5.484', '3.025', '2.606', '2.605']):
        need_cp(f'CLEARPOND mean PTAN, {lang.upper()}', paper, lambda lang=lang: ptan[lang])
    for lang, paper in zip(cp_langs, ['9.83', '2.77', '0.33', '0.38', '0.59']):
        R.check(f'homophone rate (%), {lang.upper()}', paper, rate[lang])
    if ptan is not None:
        test = correlation_test([ptan[l] for l in cp_langs], [rate[l] for l in cp_langs])
    need_cp('Pearson r', '0.992', lambda: test['r'])
    need_cp('r²', '0.984', lambda: test['r2'])
    need_cp('t(3)', '13.43', lambda: test['t'])
    need_cp('p', '0.00089', lambda: test['p'])
    need_cp('Spearman ρ', '0.60', lambda: spearman([ptan[l] for l in cp_langs], [rate[l] for l in cp_langs]))
    for lang, paper in [('en', '0.998'), ('es', '0.994'), ('de', '0.992'), ('nl', '0.992'), ('fr', '0.976')]:
        need_cp(f'leave-one-out r, dropping {lang.upper()}', paper,
                lambda lang=lang: cp_r(rate, [l for l in cp_langs if l != lang]))
    need_cp('r with both FR and EN dropped (n = 3)', '−0.656', lambda: cp_r(rate, ['de', 'nl', 'es']))
    low = ['es', 'de', 'nl']
    R.check('spread of ES/DE/NL homophone rates (pp)', '0.27', max(rate[l] for l in low) - min(rate[l] for l in low))
    need_cp('spread of ES/DE/NL CLEARPOND sizes', '0.42', lambda: max(ptan[l] for l in low) - min(ptan[l] for l in low))
    need_cp('the two methods order ES/DE/NL differently', 'yes',
            lambda: sorted(low, key=lambda l: rate[l]) != sorted(low, key=lambda l: ptan[l]))

    # accent
    if have_sens:
        gb, us = accent['en-gb'], accent['en-us']
        gb_rate = 100 * gb['words'] / accent['vocab']
        us_rate = 100 * us['words'] / accent['vocab']
    need_sens('EN rate under en-gb (%)', '2.77', lambda: gb_rate)
    need_sens('EN rate under en-us (%)', '2.36', lambda: us_rate)
    need_sens('change (pp)', '−0.41', lambda: us_rate - gb_rate)
    need_sens('relative change', '15%', lambda: 100 * (gb_rate - us_rate) / gb_rate)
    need_sens('accent-invariant clusters', '674', lambda: accent['n_shared'])
    need_sens('accent-invariant share of en-gb clusters', '78%', lambda: 100 * accent['n_shared'] / gb['clusters'])
    need_sens('clusters only under en-gb', '187', lambda: accent['n_gb_only'])
    need_sens('clusters only under en-us', '62', lambda: accent['n_us_only'])

    def in_list(clusters, pair):
        return any(set(pair.split('/')) <= set(c) for c in clusters)
    for pair in ['air/heir', 'alms/arms', 'aural/oral', 'acicula/acicular']:
        need_sens(f'en-gb-only example {pair}', 'yes', lambda pair=pair: in_list(accent['gb_only'], pair))
    for pair in ['board/bored', 'balm/bomb', 'airing/erring']:
        need_sens(f'en-us-only example {pair}', 'yes', lambda pair=pair: in_list(accent['us_only'], pair))
    need_sens('EN still second-highest under en-us', 'yes',
              lambda: sorted(PAPER_LANG_ORDER, key=lambda l: us_rate if l == 'en' else rate[l])[-2] == 'en')
    need_sens('next language after EN (PT) rate (%)', '0.99', lambda: rate['pt'])
    need_sens('EN under en-us more than double PT', 'yes', lambda: us_rate > 2 * rate['pt'])
    if ptan is not None and have_sens:
        R.check('CLEARPOND r with en-gb', '0.992', cp_r(rate))
        R.check('CLEARPOND r with en-us', '0.986', cp_r({**rate, 'en': us_rate}))
    else:
        R.skip('CLEARPOND r with en-gb / en-us', '0.992 / 0.986', 'needs --clearpond and `sensitivity`')
    need_sens('en-gb clusters not surviving the accent change', '22%', lambda: 100 * accent['n_gb_only'] / gb['clusters'])
    need_sens('membership churn, in total', '29%',
              lambda: 100 * (accent['n_gb_only'] + accent['n_us_only']) / gb['clusters'])

    # validation that falsified the pipeline
    if have_sens:
        de_pre_f6 = 100 * sens['f6_off_de']['words'] / sens['f6_off_de']['vocab']
    need_sens('DE homophone rate before F6 (%)', '6.88', lambda: de_pre_f6)
    if ptan is not None and have_sens:
        R.check('CLEARPOND r before F6', '0.76', cp_r({**rate, 'de': de_pre_f6}))
    else:
        R.skip('CLEARPOND r before F6', '0.76', 'needs --clearpond and `sensitivity`')
    need_sens('DE case-variant clusters before F6', '2,881', lambda: sens['f6_off_de']['case_only_clusters'])
    need_sens('DE clusters before F6', '3,032', lambda: sens['f6_off_de']['clusters'])

    # ---- Table 5 and §5.3
    R.section('Table 5 and §5.3: verb polysemy')
    vp = {lang: verb_polysemy(detail[lang]['homographs']['all_matches']) for lang in ('en', 'es', 'fr')}
    for lang, verbs, mean, top, top_n in [('en', '4,518', '3.6', 'break', '59'),
                                          ('es', '2,909', '5.4', 'cortar', '70'),
                                          ('fr', '3,079', '5.7', 'donner', '105')]:
        R.check(f'{lang.upper()} polysemous verbs', verbs, vp[lang]['table5_verbs'])
        R.check(f'{lang.upper()} mean senses each', mean, vp[lang]['table5_mean_senses'])
        R.check(f'{lang.upper()} most polysemous verb', top, vp[lang]['table5_most_polysemous'])
        R.check(f'{lang.upper()} its verb senses', top_n, vp[lang]['table5_most_polysemous_senses'])
    R.check('EN polysemous verbs ÷ ES', '1.6', vp['en']['table5_verbs'] / vp['es']['table5_verbs'])

    def median(xs):
        xs = sorted(xs)
        n = len(xs)
        return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) / 2
    for lang, paper in [('en', '2'), ('es', '3'), ('fr', '3')]:
        R.check(f'{lang.upper()} median senses per homograph', paper,
                median([len(m['senses']) for m in detail[lang]['homographs']['all_matches']]))
    for lang, paper in [('es', '3'), ('en', '2')]:
        R.check(f'{lang.upper()} median senses, all-noun homographs', paper,
                median([len(m['senses']) for m in detail[lang]['homographs']['all_matches']
                        if all(s['pos'] == 'n' for s in m['senses'])]))
    need_sens('ES polysemous verbs with F4 disabled', '2,949',
              lambda: sens['es_f4_off_any_verb_polysemy']['table5_verbs'])
    need_sens('ES mean senses each with F4 disabled', '5.3',
              lambda: sens['es_f4_off_any_verb_polysemy']['table5_mean_senses'])

    # ---- Table 6 and §5.4
    R.section('Table 6 and §5.4: fan-in')
    rows = M['clusters']
    reliable = {pos: [r for r in rows if r['pos'] == pos and r['en_word_density'] >= MIN_EN_WORD_DENSITY]
                for pos in ('v', 'n')}
    fanin = {pos: {l: sum(r['ratios'][l] for r in reliable[pos]) / len(reliable[pos]) for l in FANIN_LANGS}
             for pos in ('v', 'n')}
    by_pos = M['summary_by_lang_by_pos']
    R.check('verb clusters after the reliability filter', '184', len(reliable['v']))
    R.check('noun clusters after the reliability filter', '552', len(reliable['n']))
    R.check('verb clusters selected', '187', sum(1 for r in rows if r['pos'] == 'v'))
    table6 = {'pt': ('0.694', '0.136', '0.572'), 'it': ('0.720', '0.183', '0.710'),
              'es': ('0.754', '0.164', '0.622'), 'nl': ('0.799', '0.217', '0.925'),
              'fr': ('0.855', '0.224', '0.601'), 'de': ('1.047', '0.349', '1.114')}
    for lang, (v, sd, n) in table6.items():
        R.check(f'{lang.upper()} verb fan-in', v, by_pos['v'][lang]['mean_fanin_ratio'])
        R.check(f'{lang.upper()} verb sd', sd, by_pos['v'][lang]['stdev'])
        R.check(f'{lang.upper()} noun fan-in', n, by_pos['n'][lang]['mean_fanin_ratio'])
    def sd(xs):
        m = sum(xs) / len(xs)
        return math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1))
    # from the unrounded ratios: the stored 3-decimal sds would round twice
    sds = [sd([r['ratios'][l] for r in reliable[pos]]) for pos in ('v', 'n') for l in FANIN_LANGS]
    R.check('smallest sd, verbs and nouns', '0.14', min(sds))
    R.check('largest sd, verbs and nouns', '0.35', max(sds))
    de_below_fr = sum(1 for r in reliable['v'] if r['ratios']['de'] < r['ratios']['fr'])
    R.check('verb clusters where DE < FR', '50', de_below_fr)
    R.check('as a share of verb clusters', '27%', 100 * de_below_fr / len(reliable['v']))
    R.check('Spearman ρ, verb vs noun ordering', '0.60',
            spearman([fanin['v'][l] for l in FANIN_LANGS], [fanin['n'][l] for l in FANIN_LANGS]))
    all_nouns = [r for r in rows if r['pos'] == 'n']
    R.check('noun clusters selected', '1,003', len(all_nouns))
    R.check('largest sd over all noun clusters', '12.5',
            max(sd([r['ratios'][l] for r in all_nouns]) for l in FANIN_LANGS))
    R.check('largest single noun ratio', '258', max(max(r['ratios'].values()) for r in all_nouns))
    R.check('noun clusters removed by the reliability filter', '451', len(all_nouns) - len(reliable['n']))
    asterid = next(r for r in rows if r['root_lemma'] == 'asterid dicot genus')
    R.check('asterid dicot genus: concepts', '321', asterid['concept_count'])
    R.check('asterid dicot genus: English common-noun lemmas', '1', asterid['en_word_count'])
    size = [vocab[l] for l in FANIN_LANGS]
    R.check('r(lexicon size, verb fan-in)', '+0.79', pearson(size, [fanin['v'][l] for l in FANIN_LANGS]))
    R.check('r(lexicon size, noun fan-in)', '+0.99', pearson(size, [fanin['n'][l] for l in FANIN_LANGS]))
    no_de = [l for l in FANIN_LANGS if l != 'de']
    R.check('r(lexicon size, noun fan-in) without DE', '0.99',
            pearson([vocab[l] for l in no_de], [fanin['n'][l] for l in no_de]))
    normalised = {l: fanin['v'][l] / (vocab[l] / vocab['en']) for l in FANIN_LANGS}
    R.check('size-normalised verb fan-in, DE (now lowest)', '0.764', normalised['de'])
    R.check('size-normalised verb fan-in, FR (now highest)', '1.634', normalised['fr'])
    R.check('DE lowest and FR highest after normalising', 'yes',
            min(normalised, key=normalised.get) == 'de' and max(normalised, key=normalised.get) == 'fr')
    need_sens('DE noun fan-in with F3 applied to German', '0.000', lambda: sens['de_fanin_with_f3']['n']['mean_fanin_ratio'])
    R.check('DE verb fan-in with the F3 exemption', '1.047', fanin['v']['de'])
    need_sens('DE verb fan-in with F3 applied to German', '1.045', lambda: sens['de_fanin_with_f3']['v']['mean_fanin_ratio'])

    # ---- §6
    R.section('§6: discussion')
    R.check('DE homograph rate', '27.6%', 100 * L['de']['homographs']['count'] / vocab['de'])
    R.check('EN homograph rate', '33.0%', 100 * L['en']['homographs']['count'] / vocab['en'])
    R.check('F4 removals, smallest (ES)', '11,714', min(L[l]['filter_stats']['f4_dropped'] for l in FANIN_LANGS))
    R.check('F4 removals, largest (DE)', '35,892', max(L[l]['filter_stats']['f4_dropped'] for l in FANIN_LANGS))
    R.check('r(hand-curated share, verb fan-in)', '0.024',
            pearson([share[l] for l in FANIN_LANGS], [fanin['v'][l] for l in FANIN_LANGS]))
    R.check('r(hand-curated share, noun fan-in)', '−0.568',
            pearson([share[l] for l in FANIN_LANGS], [fanin['n'][l] for l in FANIN_LANGS]))

    # ---- §4 annotation sheets
    R.section('§4: annotation sheets')
    pool_size = {'homophones': lambda l: hp[l]['cluster_count'],
                 'near_homophones': lambda l: L[l]['near_homophones']['pair_count'],
                 'palindromes': lambda l: L[l]['palindromes']['count']}
    for lang in ANNOTATION_LANGUAGES:
        for cat in ANNOTATION_CATEGORIES:
            item = f'outputs/annotation/{lang}_{cat}.tsv items'
            pool = pool_size[cat](lang)
            if pool < ANNOTATION_N:
                # a category smaller than the sample is taken in full
                item += f' (only {pool} exist, all sampled)'
            expected = str(min(pool, ANNOTATION_N))
            path = os.path.join(out_dir, 'annotation', f'{lang}_{cat}.tsv')
            if not os.path.exists(path):
                R.skip(item, expected, 'run `annotation`')
                continue
            with open(path, encoding='utf-8') as f:
                R.check(item, expected, sum(1 for _ in f) - 1)

    md = R.markdown()
    with open(os.path.join(out_dir, 'paper_results.md'), 'w', encoding='utf-8') as f:
        f.write(md + '\n')
    write_json(os.path.join(out_dir, 'paper_results.json'),
               [{'section': t, **r} for t, rows in R.sections for r in rows])
    print('\n' + R.summary())
    for r in R.rows():
        if r['status'] in ('close', 'DIFFERS'):
            print(f"  {r['status']:<7}  {r['item']}: paper {r['paper']}, reproduced {r['reproduced']}")
    print(f"details: {os.path.join(out_dir, 'paper_results.md')}")


# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------

def cmd_all(args):
    for step in (cmd_install, cmd_detect, cmd_sensitivity, cmd_annotation, cmd_report):
        step(args)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument('--out-dir', default=DEFAULT_OUT_DIR,
                        help='where outputs are written and read (default: outputs/ next to program.py)')
    hybrid_dir = argparse.ArgumentParser(add_help=False)
    hybrid_dir.add_argument('--hybrid-dir',
                            help='use local copies of the hybrid wordnets (<lang>_hybrid.xml or .zip) '
                                 'instead of downloading them')
    clearpond = argparse.ArgumentParser(add_help=False)
    clearpond.add_argument('--clearpond',
                           help='use local copies of the five CLEARPOND databases (a folder of the '
                                '.zip downloads or extracted .txt files) instead of downloading them')
    sub = parser.add_subparsers(dest='command', required=True)

    sub.add_parser('install', parents=[common, hybrid_dir], help='download and install the seven lexicons into wn')
    sub.add_parser('check', parents=[common], help='verify software versions and installed lexicons')
    p = sub.add_parser('detect', parents=[common], help='main run: filters F1-F6, all detectors, fan-in matrix')
    p.add_argument('--no-fanin', action='store_true', help='skip the fan-in matrix (the slowest step)')
    sub.add_parser('sensitivity', parents=[common], help='re-runs with one setting changed (accent, F3-F6)')
    p = sub.add_parser('annotation', parents=[common], help='seeded annotation sheets (paper §4)')
    p.add_argument('--languages', nargs='+', default=ANNOTATION_LANGUAGES)
    p.add_argument('--n', type=int, default=ANNOTATION_N, help='items per language and category')
    p.add_argument('--seed', type=int, default=ANNOTATION_SEED)
    sub.add_parser('report', parents=[common, clearpond], help='every figure in the paper, checked against the text')
    p = sub.add_parser('all', parents=[common, hybrid_dir, clearpond],
                       help='install, detect, sensitivity, annotation and report, in order')
    p.set_defaults(no_fanin=False, languages=ANNOTATION_LANGUAGES, n=ANNOTATION_N, seed=ANNOTATION_SEED)

    args = parser.parse_args()
    args.out_dir = os.path.abspath(args.out_dir)
    # wn 0.9.4 cannot open its database until its folder (~/.wn_data) exists
    os.makedirs(wn.config.data_directory, exist_ok=True)
    {'install': cmd_install, 'check': cmd_check, 'detect': cmd_detect, 'sensitivity': cmd_sensitivity,
     'annotation': cmd_annotation, 'report': cmd_report, 'all': cmd_all}[args.command](args)


if __name__ == '__main__':
    main()
