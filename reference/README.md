# reference: what the program is checked against

Nothing in this folder is part of the Lean program: `lake build` and
`lake test` never use Python. The folder answers one question: **what is the
right answer for this text?** This file says how each check works, how to
run it and how to read what it prints. [`CLAIMS.md`](../CLAIMS.md), in the
root of the repository, has what the checks found, with their numbers,
beside what is proven and what is trusted.

Every statement of this folder about another program is about one version of
it: RDKit 2024.03.3, partialsmiles 2.0, and Open Babel 3.1.1 as the Python
package `openbabel-wheel` 3.1.1.23 brings it (an unofficial build, whose
library reports itself as 3.1.0). `requirements.txt` fixes these versions.
This project owes much to the people who make these programs: without their
work it could not have been checked at all.

The files of this folder are under the Apache License 2.0, as the whole
repository is, or, at your option, under the MIT License (`LICENSE-MIT` in
this folder). The second choice is there because some of the scripts import
Open Babel: its licence, the GNU General Public License version 2, is
generally held to be incompatible with the Apache License 2.0. The 100 SMILES
texts of the NCI file in `test_cases.py` are not this project's to license:
see "The data" below.

## What is here

| File | What it is |
|---|---|
| `model.py` | `SPEC.md` as a Python program: the reader with every error message, both spellings, the chosen form, the printed layout and the filter. It can be run like `app`. |
| `others.py` | What three other programs read from a text: RDKit, Open Babel and partialsmiles. And a few small things that several checks share. |
| `sources.py`, `fetch.py` | Where the fetched files come from, with their checksums; `fetch.py` fetches those that are missing and verifies all of them. |
| `check_spec.py` | The examples and claims of `SPEC.md` against the model, RDKit, Open Babel and the OpenSMILES text. |
| `check_corpus.py` | The model against RDKit on the 62,099 real SMILES texts. |
| `check_random.py` | `SPEC.md` and the model under attack, with random texts and random `Mol`s. |
| `check_stereo.py` | The stereo facts that the model stores, with the reader alone: against Open Babel's own record, and against coordinates in space that RDKit builds. |
| `check_canonical.py` | The chosen form of the model: against its definition, on other numberings and spellings of the same molecule, and against RDKit's own canonical text. |
| `test_cases.py` | What the tests of the Lean program are run on: the SMILES texts that `SPEC.md` quotes, further texts written for the tests, 100 real texts, `Mol`s written out by hand, and `Mol`s of test texts with their atoms numbered differently. |
| `check_tests.py` | Writes the expected results of those tests, as the model gives them, into `TestData.lean`, and checks that the file is up to date. |
| `check_direct.py` | The Lean program against RDKit and Open Babel themselves, on the real texts, without the model. |
| `check_filter.py` | The filter of the Lean program against a search written for RDKit, without the model. |
| `check_app.py` | The Lean program against the model, text by text, for about 1.2 million questions. |
| `requirements.txt` | The Python packages, with exact versions. |
| `downloads/` | The fetched files. Not kept in Git; `fetch.py` recreates it. |

There are nine checks. Five are about the model and never start the Lean
program: `check_spec.py`, `check_corpus.py`, `check_random.py`,
`check_stereo.py` and `check_canonical.py`. `check_tests.py` is about the
expected results of the Lean tests. Three ask the Lean program, and build
it first (`lake build app answers`): `check_direct.py`, `check_filter.py`
and `check_app.py`. `app` is the program. `answers` is a second small
program, a tool of these checks (`Answers.lean`): it gives what
`VeriMol.run` gives, the function that is the whole program, for up to a
thousand lists of arguments in one start.

"Worked out by hand" and "written out by hand" mean in these files: written
down from `SPEC.md`, and not worked out by the model or by the Lean program.

## What the program is checked against, and the part of each

1. **`SPEC.md`** says what the program must do. It is the only source that
   decides.
2. **The model** is `SPEC.md` worked out a second time, in another language.
   The Lean program and the model must give the same answer for every text. If
   they differ, one of them is wrong, or `SPEC.md` is unclear.
3. **RDKit**, with its clean-up (its sanitization) switched off, reports what
   a text says, atom by atom. It is the judge for real texts, except for the
   differences that `SPEC.md` lists (sections 11.2 and 12.4). For the filter it
   is asked with its clean-up on.
4. **Open Babel** is a second, independent reader. It reads every real text
   beside RDKit (`check_direct.py`), it is asked where the model and RDKit
   differ, and its own record of what the stereo marks say is what the
   stored stereo facts are held against (`check_stereo.py`).
5. **partialsmiles** is asked only whether a text is grammatical.
6. The **OpenSMILES specification** is the text of the standard.

[`SPEC.md`](../SPEC.md) and `CLAIMS.md` stand in the root of the repository.

### What agreement with the model shows, and what it does not

A mismatch with the model always means something. No mismatch means less:
the model and the Lean program were both written from the same `SPEC.md` by
the same AI coding assistant, so a misreading that both share shows no
mismatch. Against that, the model is checked against RDKit and Open Babel,
and two checks leave the model out: `check_direct.py` holds the Lean program
against RDKit and Open Babel themselves, and `check_filter.py` holds its
filter against RDKit.

## Setting it up

Once, in the project folder:

```
python3 -m venv .venv
.venv/bin/python -m pip install -r reference/requirements.txt
.venv/bin/python -I reference/fetch.py
```

The first line needs a Python that has the `venv` module; the checks were run
with Python 3.9. The exact version of RDKit that the second line asks for has
no package for Python 3.13 or newer, so that line fails there: use Python 3.9
to 3.12 (for example with `python3.12` in the place of `python3`). `fetch.py`
prints one line per file, each with `ok`, and ends with exit code 0. A line
with `BAD` means that a file could not be fetched or is not the one that was
recorded; the script then ends with exit code 1.

## Using it

```
.venv/bin/python -I reference/model.py 'CC(=O)O'             # what `app 'CC(=O)O'` must print
.venv/bin/python -I reference/model.py canonical 'OCC'       # what `app canonical 'OCC'` must print
.venv/bin/python -I reference/model.py filter perfluoro 6 'CC(=O)O'    # the same for the filter

.venv/bin/python -I reference/check_spec.py                  # about fifteen seconds
.venv/bin/python -I reference/check_corpus.py                # about two minutes
.venv/bin/python -I reference/check_random.py                # about two minutes
.venv/bin/python -I reference/check_stereo.py                # about three minutes
.venv/bin/python -I reference/check_canonical.py             # about six minutes
.venv/bin/python -I reference/check_tests.py                 # a few seconds
.venv/bin/python -I reference/check_tests.py --write         # writes TestData.lean anew, then checks
.venv/bin/python -I reference/check_direct.py                # about two minutes
.venv/bin/python -I reference/check_filter.py                # less than a minute
.venv/bin/python -I reference/check_app.py                   # about twelve minutes
.venv/bin/python -I reference/check_app.py --every-start     # `app` is started for every question: hours
```

The times are those of one desktop machine. The longer checks start up to
eight worker processes. Every check but `check_spec.py`, `check_random.py`
and `check_tests.py` takes `--limit` and a number, for a quick look at a
sample, and refuses an argument that it does not know. Put a SMILES text in
single quotes: inside double quotes a shell can change a text that holds a
`$`. The option `-I` makes Python ignore everything outside this project's
environment. The fetched files are data from the internet, so they are only
ever read as data, and Python is never started from inside `downloads/`.

Every check ends with exit code 1 if it found something that `SPEC.md` does
not explain, and it prints such a finding in CAPITALS (`check_spec.py` and
`check_tests.py` print `FAIL`). A count of nothing is no success: the checks
ask that the counts which carry them are large enough, so that a reader that
refused every text would not pass with nothing compared. The random choices
are fixed, so every run tries the same texts.

### Reading the output of `check_spec.py`

One line per check, `PASS` or `FAIL`, with the section of `SPEC.md` it belongs
to; the lines marked 10 are about theorems of `CLAIMS.md`. Run it after
every change to `SPEC.md` or to the model.

### Reading the output of `check_corpus.py`

For every text the script asks three things:

- **reader.** The `Mol` of the model against what RDKit reads with its
  clean-up off, atom by atom.
- **spelling** (the lines `as it is:`). Each of the two spellings of
  `SPEC.md`, section 9, is read back by the model, which must return exactly
  the same `Mol`, and by RDKit, which must read exactly that `Mol` too. With
  its clean-up on, RDKit must also find the same arrangement in space as in
  the text that was read, wherever it can compare the two.
- **numbers** (the lines `renumbered:`). The same after the atoms were
  renumbered at random; this is not asked for RDKit's random spellings
  (below). The renumbering is written out by the rule for a stored mark
  (`test_cases.py`), and the model's own way of putting the atoms into a new
  order must give the same `Mol`.

For a text with stereo marks the renumbered `Mol` is also written, in the
plain spelling, with the mark of each ring bond at the closing ring number
and at both ends. And `@` and `@@` are swapped on purpose in the written
text, which RDKit must notice in nine cases of ten.

The script prints a count for every outcome, for three groups of texts: the
real ones, three random spellings by RDKit of each real text with stereo
marks that RDKit reads with its clean-up on, and a small list of texts with
notation that real data hardly contains. Where the model and RDKit count
other hydrogens at an atom, a table lists the cases by kind of atom, with
Open Babel's count beside the two. The script does not itself hold a
refusal, or other hydrogens at a bare atom, against the lists of `SPEC.md`:
it counts them, without capitals. `check_random.py` and `check_direct.py`
hold them against the lists.

### Reading the output of `check_random.py`

Four attacks on claims of `SPEC.md`, A to D, each with a count of what
happened.

- **A, the grammar.** Every text of the grammar of `SPEC.md`, sections 4 and
  12.2, must be read, or refused for what it says, and no text outside that
  grammar may be read. The script writes the grammar out a second time, as a
  recogniser that shares no code with the model.
- **B, the first problem.** Nothing inside a text may be wrong before the
  reported position (`SPEC.md`, section 6): the text cut off just before that
  position must have no problem inside, and adding anything behind the text
  must not change the report. Set aside are the texts whose report is one of
  the end of the text, or one of the five about stereo marks that are looked
  for last; and where a `%` lacks its two digits, nothing is added behind
  the text.
- **C, RDKit.** Where the model and RDKit, with its clean-up off, part ways
  on a text, it must be in one of the ways that `SPEC.md`, sections 11.2 and
  12.4, list. Only the atoms and the bonds are compared. The random texts
  are made from a fixed set of pieces, so this attack cannot find a kind of
  difference that needs a piece which is not in the set.
- **D, the round trip.** What theorems 11 and 12 of `CLAIMS.md` say of the
  Lean program is tried on the model, where nothing is proven: 100,000 small
  random `Mol`s without stereo facts, and 100,000 in which an atom or a
  double bond that can have a stereo fact gets one at random (the output
  says how many of them hold one). Wherever a spelling gives a text, reading
  it must return exactly the `Mol`. For the `Mol`s without stereo facts
  RDKit must read that `Mol` from the text as well, apart from a mass number
  0, which it does not keep, and with a lowercase symbol exactly where
  `SPEC.md`, section 9, asks for one. In each spelling at least 40,000 of
  each 100,000 `Mol`s must get a text, so that a writer which refuses nearly
  everything fails, and at least 10,000 of the second 100,000 must hold a
  stereo fact. A second part makes 3,000 `Mol`s near the limit of 99 ring
  numbers (`SPEC.md`, section 9.4): the writer must give a text exactly when
  a count that the script makes from `SPEC.md`, without the model's writer,
  says so, and the limit must be met from both sides, in each spelling by at
  least 200 `Mol`s that need exactly 99 ring numbers and 200 that need
  exactly 100.

### Reading the output of `check_stereo.py`

`check_corpus.py` compares the stereo facts with RDKit through the writer,
and `check_random.py` only reads back what the model itself wrote. A model
that took clockwise for anticlockwise in reading and in writing alike would
pass both; theorems 11 and 12 of `CLAIMS.md` have the same limit. This check
uses the reader alone, and compares what it stores in two ways:

- **Part 1, Open Babel's own record.** After it has read a text, Open Babel
  holds a record of what each stereo mark says. The script translates the
  record into the words of `SPEC.md`, section 12.1. It must be what the model
  stores, for every atom and every double bond of every text that the model
  reads, and neither of the two may have a fact that the other lacks.
- **Part 2, coordinates in space.** RDKit builds coordinates for a text, and
  the script measures on them the orientation of each atom and the geometry
  of each double bond. This reaches fewer atoms than part 1: a text with
  more than 90 atoms, hydrogens not counted, gets no coordinates; RDKit
  builds none for some other texts; and an atom or a double bond is compared
  only where RDKit gives it the same label (R or S, E or Z) from the text
  and from its coordinates. In return this part needs no translation of a
  program's record.

The output has six groups of counts. In the two groups of part 2, every
atom and every double bond with a stereo fact stands in exactly one line, so
the lines say what was compared, what was left out, and why.

Then two wrong models are tried, each on the first 300 texts: one whose
reader decides between the two orientations the other way round, and one in
which every stored geometry is exchanged for the other. Each part must
report every atom and every double bond that it compares in them.

The script fails if the model stores something else than the record says or
than was measured; if one of the model and Open Babel has a stereo fact that
the other lacks, or RDKit gives a label from the text where the model stores
no fact; if a wrong model is not reported in full; or if a whole run compared
fewer atoms and double bonds than 16,000 and 1,200 against Open Babel's
record, or 14,000 and 1,150 on coordinates, or left more than 25 texts
unread. From one machine to another the counts of part 2 can differ by a few.

### Reading the output of `check_canonical.py`

This check is about the chosen form of a `Mol` (`SPEC.md`, section 3.2), which
the command `canonical` writes. It uses the model's search and as little
else of the model as it can: the key of a numbering is written out in the
script again, straight from `SPEC.md`. For every real text that the model
reads it prints counts under five letters, and then a sixth part for made-up
texts:

- **A, the definition.** For a `Mol` of at most 7 atoms, the key of every
  numbering is worked out one by one. The chosen form must have the least of
  these keys, and every numbering with that key must give the same `Mol`.
- **B, numbering.** The same `Mol` with its atoms renumbered at random, once,
  must get the same chosen form. The search gives up for no real text
  (`SPEC.md`, section 3.2), and a whole run fails if it does for one.
- **C, spelling.** One random spelling of the molecule by RDKit must get the
  same chosen form. A spelling is left out where the model does not read it,
  where it has other atoms or bonds or fewer stereo marks than the text, and
  where RDKit itself, with its clean-up on, takes it for another arrangement
  in space.
- **D, the text.** The chosen text is read back as the chosen form, which
  has the atoms and bonds of the `Mol` and is its own chosen form. And the
  chosen text has no dot inside a piece of the molecule.
- **E, other molecules.** The texts are sorted into groups twice: by their
  chosen text, and by RDKit's own canonical text for what `rewrite` writes
  for them. The two ways must give the same groups. RDKit is asked with its
  clean-up off, so that it reports what is written, and it is given the
  rewritten text, because it keeps the case of a symbol, which a `Mol` does
  not store. Every hydrogen is made an atom of its own before RDKit is
  asked: with the clean-up off, its canonical text does not always tell an
  atom with a counted hydrogen from the same atom without it. And for every
  text that allows it a wrong answer is made on purpose, the same `Mol` with
  one hydrogen fewer: RDKit's canonical text must be another one.
- **F, near the limit.** Twenty made-up texts, for most of which the search
  holds many beginnings. Each is renumbered at random ten times, and the
  answer must be the same for every numbering: the same chosen form, or the
  search gives up each time. Both answers must occur at least three times.

Then five wrong searches are tried on the first 3,000 texts: one that keeps
only the first of several beginnings with the least entry, one that leaves
the atoms as they are numbered, one that sorts the atoms without looking at
the bonds, one that takes two atoms for twins as soon as they have the same
element, isotope, charge and hydrogens, and one that takes two beginnings
for alike as soon as they have placed the same atoms. Each must be reported
by each of A, B and C.

The script fails if a line in CAPITALS appeared; if fewer texts were
compared under B, C or D than 9 in 10 of those with a chosen text, or under
A fewer than 1,000 in a whole run; if a part did not report a wrong search;
or if a whole run sorted fewer than 61,000 texts into groups under E.

What it does not show: that the model's search is the search of the Lean
program (`check_app.py` compares the two, text by text). And it tries one
renumbering and one spelling for each text, not many: that the chosen form
is the same for every numbering, or the search gives up for every one, is
theorem 26, for the Lean program.

One limit of letter E lies in how it uses RDKit. It asks RDKit with its
clean-up off, which is not the way RDKit is meant to make a canonical text.
Asked so, RDKit 2024.03.3 gives two canonical texts for two numberings of
one real text of the HIV set,
`[Na+].c1ccc([SH+][GeH2+]2[SH+]c3ccccc3[SH+]2)c([SH+][GeH2+]2[SH+]c3ccccc3[SH+]2)c1`.
No two real texts are that molecule, so letter E passes. `check_direct.py`
asks RDKit in a second way where its canonical texts differ (see below).

### Reading the output of `check_tests.py`

One line per check, `PASS` or `FAIL`. The last check says whether
`TestData.lean`, the file with the expected results of the Lean tests, is
exactly what the model gives today. The others say whether the lists of
texts and of `Mol`s in `test_cases.py` follow their rules, which are written
next to the lists; whether the model answers a test text that it does not
read the same behind a command word as alone; whether every place of the
table "What may come next" of `SPEC.md`, section 6, is reached by a test
text; and whether a test text that the table refuses has the answer that
section 6 gives in words.

`lake test` needs no Python, so it cannot run this check. Run it after every
change to `SPEC.md`, to the model or to the test cases. With `--write` the
script first writes `TestData.lean` anew. Do that only after a change that
was meant, and look at `git diff TestData.lean` afterwards: every changed
line is a changed expected answer, or a line that moved.

### Reading the output of `check_direct.py`

This check holds the Lean program against RDKit and Open Babel themselves,
on the real texts. The model is left out, so a misreading of `SPEC.md` that
the model and the Lean program share cannot hide here, as far as these two
programs can judge it. The answers of the Lean program come from `answers`.
In what follows, "must" says when the check passes: it is a demand on this
program, not on the others.

- **reading.** RDKit reads the text with its clean-up off. Its atoms and
  bonds must be those of the `Mol` that the Lean program prints. The
  differences that `SPEC.md`, section 11.2, lists are let through and counted.
  Open Babel reads the text as well: the same atoms, and the same atoms
  bonded. It works out aromatic bonds by its own rules, so a bond that one
  of the two calls aromatic and the other single or double is no difference
  here. A text that the Lean program refuses and RDKit reads is counted, by
  its message; a whole run must find exactly the recorded number of them.
- **writing.** What the Lean program writes for `rewrite` and for `plain`:
  RDKit must read exactly the atoms and the bonds that the Lean program
  printed for the original text, and Open Babel must read the written text
  as it reads the original one.
- **stereo.** For a text with stereo marks: RDKit, with its clean-up on,
  must take the original and each written text for the same molecule,
  stereo included. There is no verdict where its clean-up refuses one of the
  two texts.
- **canonical.** RDKit must read the canonical text as exactly the atoms and
  the bonds that the Lean program reads from it. And it must take the
  rewritten and the canonical text for the same atoms and bonds, hydrogens
  included, numbered differently: by its own canonical text for the two,
  and, where these differ, by a substructure search both ways round. One
  real text needs the second way, the one named under `check_canonical.py`.
- **wrong on purpose.** The script hands five wrong answers to its own
  comparisons, and counts how often each is noticed: a `Mol` with one
  hydrogen more; the text that was written for another molecule; in the
  place of the canonical text, a text with one hydrogen fewer, and a text in
  which a counted hydrogen has become an atom of its own; and the rewritten
  text with its first stereo mark turned round. The last is not always
  another molecule, because RDKit's clean-up takes some marks for marks that
  say nothing: the script counts its three outcomes.

The counts are held in place. A run on all texts must be a run on the 62,099
recorded texts, and every one of its numbers must be the number that the
script records (the table `RECORDED` near its head). When a number changes
because the program or `SPEC.md` was changed on purpose, the recorded number
is changed with it, and so is the document that quotes it. A sample
(`--limit`) has least counts instead.

What it does not show: which numbering a canonical text has, only that it is
the same atoms and bonds. It does not look at the stored stereo facts
(`check_stereo.py` does that, for the model), and it never asks Open Babel
about a canonical text. And it cannot judge the words and the positions of
the error messages.

### Reading the output of `check_filter.py`

This check holds the filter (`SPEC.md`, section 16) of the Lean program
against RDKit, without the model, as `check_direct.py` does. The theorems of
`CLAIMS.md` say that the program does what section 16 defines, and not that
it reads a text as a chemist does: this check looks for places where its
reading of a text, or its search, differs from RDKit's. It asks the Lean
program twice about every text, behind the words `filter perfluoro`: with
the number 6, and with the number 1, where the filter refuses every sound
`Mol` that has a fluorinated carbon atom at all and its message names the
size of the largest perfluorinated group.

RDKit is asked with its clean-up on, as a chemist would use it, and it reads
the text in its own way. A fluorinated carbon atom is, for RDKit, an atom
that fits one pattern, which is section 16.3 written a second time (the
SMARTS `[CX4H0;$(C-F);!$(C-[#1])]`). An atom that meets the five conditions
fits the same pattern without the fluorine atom, `[CX4H0;!$(C-[#1])]`. The
branch carbon atoms are worked out from these with RDKit's own record of
which atoms are bonded. The bonds that do not join two of these atoms are
taken out of a copy of the molecule, and RDKit says which atoms still hang
together. Its largest piece is RDKit's size of the largest group. No code is
shared with the Lean program or with the model: what is shared is the
definition.

- **sound.** For how many texts the filter takes the `Mol` for sound, and,
  for the others, which test fails first.
- **size.** For a sound `Mol`: RDKit's size of the largest group must be the
  size that the filter names. There is no verdict where RDKit's clean-up
  refuses the text.
- **the filter.** With the number 6 the answer must be the one that the size
  calls for, and RDKit must find a group of six or more in no text whose
  `Mol` the filter hands on.
- **other spellings.** 28 compounds, each written by RDKit in 23 more ways:
  with its atoms in 20 random orders, with single and double bonds in the
  place of aromatic ones, with every hydrogen count in square brackets, and
  with every hydrogen as an atom of its own. The filter must give the answer
  for the compound as written to every one of these spellings, except where
  a hydrogen stands as an atom: there it must refuse the `Mol` as not sound.
  Three texts more are written by hand (`BY_HAND`), with a bond symbol `:`
  or lowercase symbols at carbon atoms with four bonds, which RDKit does not
  write itself: the filter must refuse each as not sound, or name no smaller
  size than RDKit's search finds.
- **isomers.** Every isomer of the perfluoroalkyl carboxylic acids and
  sulfonic acids with a group of 1 to 10 carbon atoms: 1,758 texts. For each
  the filter must name the number of carbon atoms of the group, and RDKit's
  search must find the same. So no branch parts a group, wherever it stands
  and whether or not its carbon atom carries fluorine.

The counts are held in place, as in `check_direct.py`: a run on all texts
must give exactly the numbers that the script records (`RECORDED`).

What it does not show: that the rule is the right one. RDKit is asked for
the same pattern, written a second time, so a reading that both share shows
no difference. And it cannot judge the five tests of "sound": for a `Mol`
that the filter refuses as not sound, nothing is compared but the count.

### Reading the output of `check_app.py`

**What is compared.** A question is what stands behind `app` when the
program is called: a text alone, or one of the words `rewrite`, `plain` and
`canonical` and a text, or the words `filter perfluoro`, a number and a
text. An answer is three things: the text for standard output, the text for
standard error, and the exit code. All three must be what the model gives,
character for character. In its output the script calls a question a list
of arguments, `answers` the second program and `app` the program itself.

**Two parts.** The first part asks about every question: it compares what
`answers` gives with what the model gives. The second part starts the
program itself, `.lake/build/bin/app`, once for one question, as a user
does, for a sample of the questions. Starting `app` once for every question
takes hours, because nearly all the time goes into starting the program;
`--every-start` does it.

**What the first part takes for granted.** Three things:

1. `Main.lean` hands its arguments to `VeriMol.run` as they are, prints the
   two texts that it gives, and ends with its exit code. `CLAIMS.md`, under
   "Trusted", says what holds that in place; the second part and the program
   tests of `lake test` look for a mistake there.
2. Both programs hold the same compiled code of Core. The script reads what
   Lake handed to the linker for the two (the files `app.rsp` and
   `answers.rsp` beside the programs) and does not run if the two differ in
   more than their first entry.
3. `answers` gives what `VeriMol.run` gives. A person sees that in
   `Answers.lean`, and `lake test` holds `answers` against the expected
   answers of its program tests.

**What it does not show.** That `app` prints the model's answer for a
question outside the sample. For such a question the check shows that
`VeriMol.run` gives it, inside `answers`; the three things above are what
stands between that and `app`. With `--every-start` the second part starts
`app` for every question.

**The texts.** Seven groups:

| Group | Texts | What they are |
|---|---|---|
| real | 62,099 | the real texts, exactly as they stand in the files |
| damaged | 400,000 | real texts with one to three damages each: a character removed, doubled or swapped with its neighbour, the text cut off, another atom, bond symbol or ring number, a stereo mark turned round, an odd character put in, and so on (the list `DAMAGES` in the script) |
| mixed | 50,000 | a few pieces of SMILES in random order |
| invented | 50,000 | random texts that follow the grammar of `SPEC.md`, with notation that real texts hardly contain: `%` ring numbers, `$` bonds, isotopes, large charges, dots inside branches |
| turned | 20,000 | real texts with stereo marks in which one to three of the marks are turned round, so that the writer gets stereo facts that no real text has |
| near-limit | 400 | texts made up near the limit of the search for the chosen form (`SPEC.md`, section 3.2). The search gives up for 94 of them, and for no text of the other groups that are given to `canonical`: so this group is what compares the program with the model where the search gives up |
| fluorinated | 30,000 | invented compounds for the filter: a skeleton of 1 to 18 atoms, nearly all of them carbon, with up to two rings, and on each carbon atom mostly fluorine; each is written from a random atom, so that a group is entered at any of its atoms |

The real, the invented, the turned and the near-limit texts are also given
behind the words `rewrite`, `plain` and `canonical`. And behind the words
`filter perfluoro` and a number stand the real texts twice, with the numbers
6 and 1; the fluorinated ones, each with a number from 1 to 8; and the
invented, the turned and the near-limit ones with the number 1. With the
number 1 the message of the filter names the size of the largest
perfluorinated group, which the model works out in another way than the
Lean program. That makes 1,234,594 questions, in 25 parts: one for each of
the seven groups alone, one for each of the four groups behind each of the
three words, and six for the filter.

**The sample.** For each of the 25 parts the program itself is started for
about a thousand questions, taken at regular steps, and for the first
question of every kind of answer: 22,186 starts in all. The sample is the
same in every run.

**What it prints.** While it runs, a line after every 50,000 questions of
the first part and after every 5,000 starts of the second. At the end the 25
parts: each line is a kind of answer, with the number of questions that the
model answers so, and in square brackets the number of them for which the
program itself was started. The script ends with `No mismatch` and exit code
0, or with a count in CAPITALS, the questions concerned and exit code 1. A
whole run also makes sure that each of these was the answer to at least one
question, and that the program itself printed each of them at least once:
the 26 messages of the reader (`SPEC.md`, sections 6 and 12.2); the three
errors that `canonical` can give for a `Mol` without stereo facts; and, of
the filter, its six messages and a `Mol` that passes. (Section 16 has a
seventh message, for a `Mol` that is not well formed, which never comes from
the command.) Other messages, such as those with which the writer refuses a
`Mol` for its stereo marks (section 12.3), are compared wherever they come
up, but the script does not ask that each of them does. At its start and at
its end the script prints the checksums (sha256) of the two programs and of
the model, and it fails if one of them changed in between.

**When a start of `answers` goes wrong.** A start must end with exit code 0,
write nothing on its own standard error and print one answer for each
question, within 600 seconds. If one does not, the script says so in
CAPITALS, asks the questions of that start again one by one, and ends with
exit code 1 whatever else it finds: run it again when the machine is less
busy.

**Workers.** The first part starts eight worker processes, unless
`--workers` and a number ask for another number, and never more than the
processor threads that it may use. The second part starts two, so that the
machine stays free for other work.

## The data

| Name | Texts | What it is |
|---|---|---|
| nci5k | 4,900 | The first compounds of the NCI Open Database. RDKit ships the file. |
| hiv | 41,127 | MoleculeNet HIV, from the AIDS antiviral screen of the US National Cancer Institute. Many salts, metals and charges. |
| tox21 | 7,831 | MoleculeNet Tox21, from the US National Institutes of Health. |
| lipophilicity | 4,200 | MoleculeNet Lipophilicity. |
| bbbp | 2,050 | MoleculeNet BBBP. Many stereo marks. |
| clintox | 1,484 | MoleculeNet ClinTox. Drugs, salts, peptides. |
| sider | 1,427 | MoleculeNet SIDER. Marketed drugs. |

The numbers count different texts; the NCI file has 4,999 lines. Together
62,099 different texts, 4,550 of them with stereo marks. The texts are used
exactly as they stand in the files, including the 24 that the program does
not read (`SPEC.md`, sections 11.2 and 12.4). The MoleculeNet files are
fetched from where the DeepChem project hosts them. None of these files is
copied into this repository: `sources.py` records only where each one comes
from and its checksum. Each stays under the terms of its own source, and
these differ from set to set: look them up before you use the data for more
than these checks. The one exception to "not copied", apart from single
texts that are quoted as examples, is the list `NCI_TEXTS` in
`test_cases.py`, with the test data that is made from it in `TestData.lean`:
100 texts of the NCI file, stored so that `lake test` can use real texts
without Python (`NOTICE` in the root of the repository names their source
and its licence).

The OpenSMILES specification is fetched in the same way: version 1.0, as its
repository had it on 2 April 2026. It is under the GNU Free Documentation
License 1.2 and is not copied into this repository either.

## When something changes

- **`SPEC.md` changes:** change `model.py` to match and run the nine checks. If
  a number in `SPEC.md` or in `CLAIMS.md` comes from one of the checks, update
  it.
- **The Lean program changes** (anything under `VeriMol/Core/`, `Main.lean`
  or `Answers.lean`): run `check_direct.py`, `check_filter.py` and
  `check_app.py`. The other checks do not start the Lean program.
- **A theorem about a single text changes** (`VeriMol/Proofs/Read.lean`):
  run `check_spec.py`. It reads the `Mol`s that these theorems write out by
  hand, and holds them against RDKit and Open Babel.
- **A check fails:** do not change the expected answer to make it pass. Find
  out which of the sources is wrong. If it is `SPEC.md`, `SPEC.md` is changed
  first, and then the model and the program.
- **A new version of RDKit or Open Babel:** change `requirements.txt`, run
  the nine checks, and look at every outcome that moved.
