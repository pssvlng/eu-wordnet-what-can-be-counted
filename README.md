# What Can Be Counted Over Aligned Wordnets?

This repository reproduces every figure in the paper *What Can Be Counted Over
Aligned Wordnets? An Artefact Taxonomy and a Portability Criterion*.

[program.py](program.py) computes the figures from seven wordnets aligned to the
same 120,053 Interlingual Index (ILI) concepts: English and six hybrid wordnets for
Italian, Spanish, French, Dutch, Portuguese and German. It downloads all its inputs
itself. As its last step it compares each figure with the value printed in the paper
and lists the results in `outputs/paper_results.md`.

## What you need

| | Version used for the paper |
|---|---|
| Operating system | Ubuntu 22.04 (any Linux with espeak-ng should work) |
| Python | 3.10.12 |
| [`wn`](https://github.com/goodmami/wn) | 0.9.4 (the only third-party Python package) |
| [espeak-ng](https://github.com/espeak-ng/espeak-ng) | 1.50 |

You also need an internet connection for the downloads, about 1.3 GB of disk
(the wordnet database plus the outputs) and 2 GB of memory. A full run takes
about 35 minutes.

Use these exact versions. espeak-ng in particular decides every phoneme string, so a
different release can change the homophone figures. `python3 program.py check` warns
when a version differs.

## Running it

Install the software:

```sh
sudo apt install espeak-ng            # Ubuntu 22.04 installs version 1.50
python3 -m pip install wn==0.9.4
```

Then, from the repository folder, run:

```sh
python3 program.py all
```

This installs the lexicons, computes everything and checks the result against the
paper. It ends with a summary like this:

```text
229 figures match the paper, 0 are within one unit of its last printed digit, 0 differ, 0 skipped.
details: .../outputs/paper_results.md
```

All output goes to `outputs/` next to `program.py`, which is created if needed.
To write elsewhere, add `--out-dir <folder>` to any command.

## The steps

`all` runs these steps in order. Each can also be run on its own:

| Command | What it does | Time |
|---|---|---|
| `python3 program.py install` | Downloads the seven lexicons and installs them into `wn`. Skips any already installed. | 4 min |
| `python3 program.py check` | Checks the software versions and the installed lexicons. | seconds |
| `python3 program.py detect` | Main run: filters F1–F6, every detector for all seven languages, cognates, and the fan-in matrix. | 12–16 min |
| `python3 program.py sensitivity` | Re-runs with one setting changed: English under the `en-us` voice, each filter switched off in turn, and German fan-in with F3 applied. Needs the output of `detect`. | 8 min |
| `python3 program.py annotation` | Draws the seeded annotation samples. Needs the output of `detect`. | seconds |
| `python3 program.py report` | Downloads CLEARPOND, computes every figure in the paper from the outputs above, and compares each with the printed value. | under a minute |

## Inputs

All inputs are downloaded automatically and kept in `wn`'s download cache
(`~/.wn_data/downloads/`), so repeated runs do not download them again.

| Input | Used for | Source | Licence |
|---|---|---|---|
| English WordNet 2020 (`ewn:2020`) | the English hub | [english-wordnet](https://github.com/globalwordnet/english-wordnet), through `wn` | CC BY 4.0 |
| Hybrid wordnets `hyit`, `hyes`, `hyfr`, `hynl`, `hypt`, `hyde`, version 0.1 | the six other languages | Bergh et al. (2025), from [open-european-wordnets-hybrid](https://github.com/pssvlng/open-european-wordnets-hybrid) | GPL-3.0 |
| CLEARPOND (Marian et al. 2012) | the external validation of §5.2 | [clearpond.northwestern.edu](https://clearpond.northwestern.edu/) | see its website |

**Lexicons.** `wn` keeps installed lexicons in a database under `~/.wn_data/`.
Other lexicons in the same database do no harm; the program selects these seven by
id and version. The hybrid wordnets are fetched from a fixed commit of their
repository (`95a69f6`), and each file is checked against the SHA-256 checksum of
the file the paper used, so later changes to that repository cannot alter the
results.

**English WordNet needs one adjustment.** English WordNet 2020 contains 2,573
concepts that it proposes for the Interlingual Index but that have no ILI
identifier yet. The hybrid wordnets refer to these concepts as `in_i1` to
`in_i2573`, numbered in the order they appear in the English file. `install` gives
the downloaded English file the same numbering before adding it. Without it, those
2,573 concepts would not be aligned across languages and every figure would shift
slightly. If you have installed `ewn:2020` before with `wn.download('ewn:2020')`,
that copy lacks this numbering; `install` stops and tells you how to remove it
first: `python3 -c "import wn; wn.remove('ewn:2020')"`.

**CLEARPOND.** The program uses column 29 of each of the five language databases,
which holds that language's own `PTAN` (phonological neighbours, all types). It
checks this against the header file in each download.

**Local copies.** To work from files you already have, pass `--hybrid-dir <folder>`
(to `install` or `all`) for the hybrid wordnets, as `<lang>_hybrid.zip` or
`<lang>_hybrid.xml`, and `--clearpond <folder>` (to `report` or `all`) for the
CLEARPOND `.zip` files or their extracted `.txt` files.

## Comparing with the paper

`outputs/paper_results.md` has one table per paper section, giving the paper's value,
the reproduced value and how they compare:

- **✓ match:** identical at the precision the paper prints.
- **≈ close:** within one unit of the paper's last printed digit, for example from
  rounding.
- **✗ differs:** anything else.
- **– skipped:** an input is missing, for example CLEARPOND when it cannot be
  downloaded.

## Where each result comes from

| Paper | Command | Output |
|---|---|---|
| §2.1: 120,053 shared concepts, inferred-prefix check | `detect` | `linguistic_anomalies.json` → `alignment` |
| Table 1 shares | `report` | computed from the base counts of Bergh et al. (2025), which are inputs, not measurements |
| Table 2: F4 removals | `detect` | `linguistic_anomalies.json` → `languages.<lang>.filter_stats` |
| Table 2: F3, F5, F6 effects; §3.2: F4 split, F4 switched off, German capitalisation | `sensitivity` | `filter_sensitivity.json`, `f4_sensitivity.json` |
| Table 3, §5.1 | `detect` | `linguistic_anomalies.json`, `<lang>.json` |
| Table 4, §5.2 correlations | `report` | CLEARPOND plus `linguistic_anomalies.json` |
| §5.2 accent sensitivity | `sensitivity` | `accent_sensitivity_en.json` |
| §5.2 German before F6 | `sensitivity` | `filter_sensitivity.json` → `f6_off_de` |
| Table 5, §5.3 | `detect`, `sensitivity` | `en.json`, `es.json`, `fr.json`, `filter_sensitivity.json` |
| Table 6, §5.4, §6.3 | `detect`, `sensitivity` | `concept_collapse_matrix.json`, `filter_sensitivity.json` → `de_fanin_with_f3` |
| §4 annotation samples | `annotation` | `annotation/<lang>_<category>.tsv` |

## Figures that need a note

These notes give the exact settings behind figures that the paper states briefly,
and explain how the phonemes are produced.

- **Table 2, F3 "≈9×".** This compares Spanish homophone clusters under the softer
  capitalisation rule that was tried first (keep a capitalised lemma if a lowercase
  twin exists) with F3. It was measured when F3 was tightened, before F4–F6 existed,
  so `sensitivity` runs both rules with F4–F6 off: 3,264 against 354 clusters, 9.2×.
  Under the full protocol the comparison is not meaningful, because F6 merges the
  same `Cola`/`cola` pairs again.
- **§3.2, F4 split (77%/23% for French, 75%/25% for German).** This counts every
  single-word form identical to an English lemma of the same concept, including
  capitalised ones, so before F3. A form counts as "alongside genuine translations"
  when its synset has another single-word lemma that is not an English match. For
  French the total is therefore 32,336 forms, not the 23,803 that F4 removes after F3.
- **§3.2, "applying F3 would remove ~75% of [German] vocabulary".** This is
  measured without F4 (75.1%). With F4 applied the share is 71.7%.
- **§4, annotation samples.** The sheets cover English and German, 50 items per
  category, except German palindromes, of which only 10 exist. Use
  `python3 program.py annotation --languages en it es fr nl pt de` for all seven
  languages. The seed is fixed (`--seed 20261016`), so the same items are drawn each time.
- **Phonemisation in batches.** The program sends espeak-ng 1,000 words per call,
  as the paper's runs did. In this mode espeak-ng transcribes about 0.1% of words
  slightly differently than when given one word at a time, depending on the
  neighbouring words: it may drop a final phoneme or attach part of the next word.
  The output is deterministic for a given word list, so the figures reproduce
  exactly. Transcribing word by word would move no homophone rate by more than
  0.02 percentage points.

## Output files

All in `outputs/`, about 320 MB in total.

| File | Contents |
|---|---|
| `linguistic_anomalies.json` | Summary per language: vocabulary, filter counts, the count and examples for each category, cross-lingual cognates, alignment checks. |
| `<lang>.json` | Every candidate per category for one language, with glosses (40–53 MB each). |
| `concept_collapse_matrix.json` | Fan-in ratios for all 1,190 concept clusters, with per-POS summaries. |
| `accent_sensitivity_en.json` | English homophones under `en-gb` and `en-us`, with the clusters unique to each. |
| `f4_sensitivity.json` | French and German homophone rates with and without F4. |
| `filter_sensitivity.json` | The other single-setting re-runs listed above. |
| `annotation/*.tsv` | Annotation sheets with blank `correct` and `note` columns. |
| `paper_results.md`, `paper_results.json` | Every paper figure next to its reproduced value. |

Homographs, homonyms, polysemes, heteronyms, contronyms, doublets and cognates are
computed and released but, as the paper explains, are not comparable across
languages (Class II and III).
