# What is proven, what is tested, what is trusted

[`README.md`](README.md) has the short account of the project, and
[`SPEC.md`](SPEC.md) says what the program does. This file says what is known
about the program, and how it is known: what is proven in Lean, what is
tested and with which numbers, and what has to be trusted.

A `Mol` is the molecular graph of `SPEC.md`, section 3. "Section 9.4" means
that section of `SPEC.md`. "Real texts" are the 62,099 SMILES texts from
seven public collections that the checks run on
([`reference/README.md`](reference/README.md) names them).

Some words of this project, with the usual term beside them. The **chosen
form** of a `Mol` is a canonical form, and the text that `canonical` prints is
a canonical SMILES, for the order of the atoms only (section 3.2). Two `Mol`s
that are **the same molecule, numbered differently** are the same labelled
graph up to a renumbering of the atoms: isomorphic labelled graphs, stereo
included (section 3.1). A **molecule**, where theorem 45 speaks of one (the
type `Molecule`), is all the well formed `Mol`s that are one molecule,
numbered differently, taken as one thing: an isomorphism class of labelled
graphs. **Stereo facts** are what a `Mol` stores about chirality and about the
geometry of double bonds (section 12.1); an atom with a **free place** has
three neighbours and a lone pair in the fourth place. A **spelling** is one
way in which the writer writes a `Mol` as SMILES (section 9). The **model** is
`reference/model.py`, the specification as a Python program. RDKit's
**clean-up** is its sanitization, which `sanitize=False` switches off.
**Core** is the library `VeriMol.Core`, which holds all the logic, and
**Proofs** the library `VeriMol.Proofs`, which holds the theorems. The
**audit** (`Audit.lean`) checks those rules of the project that a machine can
check, while the project is built, and the **ledger** (`Audit/Ledger.lean`) is
its list of the numbered theorems. The **filter** is the command that hands a
`Mol` on only if it is **sound** and a **rule** holds for it (section 16):
sound says of which `Mol`s a rule is asked, a rule is a property of a `Mol`
that is relevant to the safety of a compound, and a **checker** is the
function of the program that works one of the two out.

## Proven

These are statements about the Lean functions. There are 49 theorems with 97
statements: a row of a table below can stand for several statements (each
statement is a `theorem` of its own in Lean, and the ledger and the report of
the build count these 97). Theorems 36 to 44, with 24 of the statements, are
single examples; the other 73 statements hold for every input that they name.
The exact statements stand in the files under `VeriMol/Proofs/`. The ledger
lists them in the order of the tables, and the build checks each of its lines:
that the theorem exists, that the fingerprint of its statement is the recorded
one (see "Trusted"), and that its proof rests on no `sorry` and on no axiom
beyond the three standard ones of Lean.

The definition of "sound" and the rule of the filter, which theorems 46 to
49 are stated with, stand in a folder of their own,
`VeriMol/Proofs/Predicates/`. Six more theorems, about known compounds, are
proven and are not among these counts, because the ledger does not list
them (see "Known compounds", below the tables).

Not every statement is independent of the others. These rows follow from other
rows: theorems 1 and 3 from theorems 2, 4 and 5, with one statement of theorem
49 (`run_filter`) for theorem 1; theorems 13, 14 and 16 from theorems 5, 11
and 12; theorem 15 from theorem 11; theorem 18 from theorems 5, 8, 10 and 19;
theorems 27 and 28 from theorems 20, 23, 24 and 26; theorem 30 from theorems
8, 23 and 29; theorem 31 from theorems 8, 15, 27, 29 and 32; theorem 33 from
theorems 30 and 32; theorem 34 from theorems 5 and 29; theorem 45 from
theorems 5, 8, 11, 15, 20, 23, 24, 26 and 27, together with the definition of
the writer of `canonical` (`writeChosen`) and one helper lemma: the same
molecule, numbered differently, has as many atoms; and theorem 49, apart from
its statement about which texts are a number, from theorems 2, 46 and 48,
together with the definitions of the filter and of the function that is the
whole program. Each is listed because it says something that a reader may look
for.

Where a row speaks of what the program prints and of its exit code, it means
the function that is the whole program, `VeriMol.run`: writing the answer out
is not part of any theorem (section 8; see "Trusted").

### The program

| # | Theorem | Its name in Lean |
|---|---|---|
| 1 | Whatever the arguments, the function that is the whole program (`VeriMol.run`) gives one of two kinds of answer. It succeeds: exit code 0 and nothing on standard error. Or it reports an error in one fixed form: exit code 1, nothing on standard output, and on standard error the line `error: <message>`. | `VeriMol.run_succeeds_or_reports_error` |
| 2 | For every text that the reader reads: the program, given the text alone, prints the printed layout (section 7) of the `Mol` that the reader returns, and ends with exit code 0. Two more statements: the printed layout shows the whole `Mol`, so that two `Mol`s that are printed alike are equal, well formed or not; and so two texts that are read get the same answer from the program, each given alone, exactly when they are read as the same `Mol`. | `VeriMol.run_read`, `VeriMol.Mol.printed_injective`, `VeriMol.run_eq_iff` |
| 3 | The other way round: if the program, given one text alone, ends with exit code 0, then the reader reads that text, and what was printed is the printed layout of its `Mol`. | `VeriMol.read_of_run` |
| 4 | A text that the reader does not read, and that is none of the three command words, gets the reader's problem as the error of the program when it is given alone. A second statement: a list of arguments that is neither one text that is no command word, nor one of the three command words followed by a text, nor the words `filter` and `perfluoro` followed by a number from 1 on and a text, gets the error about the arguments (section 8). | `VeriMol.run_of_read_error`, `VeriMol.run_usage` |
| 5 | A text that the reader does not read gets the same answer behind each of the three command words `rewrite`, `plain` and `canonical`: the reader's problem, as the error of the program. Three more statements, for a text that the reader reads: behind `rewrite`, `plain` and `canonical` the program answers with what the writer of that command gives for the `Mol` of the text (the functions `write`, `writePlain` and `writeChosen`): the text that the writer gives, followed by a line break, or the writer's message as the error of the program. | `VeriMol.run_word_of_read_error`, `VeriMol.run_rewrite`, `VeriMol.run_plain`, `VeriMol.run_canonical` |

- So theorems 2, 4 and 5, with one statement of theorem 49, say what the
  program answers for every list of arguments, in terms of the reader, of
  the three writers and of the filter. A text alone gets the printed layout of
  its `Mol`, or the reader's problem. A command word and a text get what the
  writer of that command gives for the `Mol` of the text, or the reader's
  problem. The words `filter` and `perfluoro`, a number from 1 on and a text
  get what the filter gives (theorem 49). Every other list of arguments gets
  the error about the arguments; one of the three command words alone is
  such a list. The theorems of the parts below say what the reader, the
  writers and the filter give.
- Given a text alone, the program ends with exit code 0 for exactly the texts
  that the reader reads (theorems 2 and 3), and what it prints then shows the
  whole `Mol` (theorem 2).

Not proven:

- **That the printed layout is the one of section 7.** Theorems 2 and 3 speak
  of the layout through the program's own function for it. That this
  function follows section 7 is proven for one `Mol` (theorem 39). Beyond
  that it is tested: what the program prints must be what the model prints.
- **That the first problem of a text is the one that is reported** (section
  6). Theorem 40 has one example of it; the rest is tested.

### The reader

| # | Theorem | Its name in Lean |
|---|---|---|
| 6 | For every element, reading its symbol gives that element back. | `VeriMol.Element.ofSymbol?_symbol` |
| 7 | For every list of tokens, the pieces of a text, that can be spelled: spelling it and cutting the text into tokens again gives the same list. | `VeriMol.cut_spell` |
| 8 | Whatever the text, a `Mol` that the reader returns is well formed. | `VeriMol.read_wellFormed` |
| 9 | For every text that is read: the `Mol` has one atom for each atom among the tokens into which the program cuts the text, in their order. Element, isotope and charge are those of the token. So are the hydrogens of an atom in square brackets. The hydrogens of an atom without square brackets are what the program's own function for rule 7 of section 5 gives for the bonds that the `Mol` has at that atom. | `VeriMol.read_atoms` |
| 10 | A `Mol` that the reader returns has no atom that the writer refuses (section 9.4). | `VeriMol.read_no_refusal` |

- Whatever the reader returns is well formed (theorem 8), also in its two
  lists of stereo facts: every atom with an orientation has four places, and
  every double bond with a geometry is a double bond that can have one.
- Theorem 9 holds for every text that is read. It compares the reader with
  its own first half, the cutting of the text into tokens. What the tokens
  of a text are is said by theorem 7 for the texts that the program spells,
  and by tests for all others.
- Eleven examples say what the reader gives without the writer (theorems 36
  and 38, and the first statement of theorem 39; see "Single examples").

Not proven:

- **Which bonds the `Mol` of a text has,** unless one of the two spellings
  produces that text. Theorem 9 is about the atoms, and it takes the tokens
  of the text, the bonds of the `Mol` and the function for rule 7 as the
  program gives them. For the bonds there are the examples. It is not proven
  that the reader agrees with the OpenSMILES document or with RDKit. That is
  tested.
- **That the reader gives the stereo facts that rules 8 to 10 of section 12.2
  define,** beyond the three examples of theorem 38. Theorems 11 and 12
  compare the reader with the writer only (see "Single examples" below).
  Beside the three examples, two comparisons of `check_stereo.py` use a reader
  alone: the model's, to which `check_app.py` holds the Lean reader (see
  "Tested").

### Reading undoes writing

| # | Theorem | Its name in Lean |
|---|---|---|
| 11 | For every `Mol`, with or without stereo facts: if the spelling with round brackets (sections 9.2 and 12.3), which `rewrite` and `canonical` print, gives a text, reading that text returns exactly that `Mol`. | `VeriMol.read_write` |
| 12 | The same for the plain spelling (sections 9.1 and 12.3), which `plain` prints. | `VeriMol.read_writePlain` |
| 13 | For every text: if `rewrite` or `plain` prints a text for it, reading that text returns the same `Mol` as reading the original. | `VeriMol.run_rewrite_same_mol` |
| 14 | For `rewrite` and for `plain`: rewriting a rewritten text prints the same text again. | `VeriMol.run_rewrite_again` |
| 15 | The writer never gives two different `Mol`s the same text for `rewrite`. | `VeriMol.write_injective` |
| 16 | For `rewrite` and for `plain`, and for two texts that are both written back: the two written texts are the same exactly when the two texts are read as the same `Mol`. | `VeriMol.run_rewrite_eq_iff` |

- The reader and the writer are inverse to each other, between the `Mol`s
  for which the program writes a text and the texts that it writes
  (theorems 11 and 12): whatever text a spelling gives for a `Mol`, reading
  it returns exactly that `Mol`, with its orientations and its geometries.
  A `Mol` that is not well formed gets no text. For a `Mol` without stereo
  facts the plain spelling leaves nothing to what the reader assumes. A bond
  that carries `/` or `\` is written with the mark in the place of its
  symbol, in both spellings, and the reader gives it the order of a missing
  symbol (section 5, rule 5). The spelling with round brackets also uses the
  reader's rules for atoms without square brackets and for missing bond
  symbols (rules 5 and 7). Theorems 11 and 12 cover all of this. So the
  program reads no text back before it returns it: that check would add
  nothing.
- The reader reads the marks that the writer chooses (section 12.3) as the
  stored facts: `@` or `@@` at an atom, for the order in which the spelling
  writes the places of the atom, and `/` or `\` at the bonds that carry a
  mark. And where the writer gives a text, the reader finds no problem in
  it: the five refusals of section 12.3 leave out every `Mol` whose text
  would not be read.
- Two different `Mol`s never get the same text: theorem 15 says it for the
  text of `rewrite` and every two `Mol`s, and theorem 16 for both commands
  and the `Mol`s of two texts. So what `rewrite` and `plain` write depends
  on the `Mol`, not on the molecule. `CCO` and `OCC` are the same molecule
  with its atoms in another order, and they are two `Mol`s (theorem 41). So
  `rewrite` cannot give them one text: it writes `CCO` for the first and
  `OCC` for the second, which the tests show.

Not proven:

- **That a spelling has the form that sections 9 and 12.3 give it:** which
  atoms stand without square brackets, which bond symbols are left out, where
  a round bracket opens, that the smallest free ring number is taken, whether
  a symbol is written in lowercase, and which bonds carry a mark. Theorem 11
  would hold as well for a spelling that used no round brackets and wrote
  every atom in square brackets. Theorem 39 fixes both spellings for one
  `Mol`. For the others the form is tested: what the program writes must be
  what the model writes. A lemma outside the ledger is about one point of the
  form (`VeriMol/Proofs/BracketRules.lean`): the spelling with round brackets
  keeps no list of the round brackets that are open, and for every `Mol` it
  gives the same tokens as a writer that keeps the list and closes round
  brackets in the three places where the rules of section 9.2 close them, and
  that is this writer in everything else (the parents, the ring numbers, the
  atoms, the bond symbols and the marks). The lemma says nothing of where a
  round bracket opens.

### When the writer gives a text

| # | Theorem | Its name in Lean |
|---|---|---|
| 17 | For every `Mol`, with or without stereo facts, and each of the two spellings: the writer gives a text exactly when the `Mol` is well formed, each of its atoms can be written (section 9.4), and its own two functions succeed: the one that chooses the marks for the double bonds (section 12.3), and the one that makes the tokens with them. The theorem does not say in other words when these two succeed. One statement, for both spellings. | `VeriMol.Spelling.write_isOk_iff` |
| 18 | For a text that is read as a `Mol` without stereo facts, `rewrite` and `plain` print a text, or `error: more than 99 ring numbers are needed at the same time`, and nothing else. Two statements: one for both spellings and a `Mol` without stereo facts that the reader returned, and one for the two commands. | `VeriMol.Spelling.write_of_read`, `VeriMol.run_rewrite_of_read` |
| 19 | When a spelling gives a text, and when it answers with the message about ring numbers, said by counting bonds. Seven statements: the list under the table says what each of them says, and how the bonds are counted. | `VeriMol.Spelling.write_isOk_iff_ringNumbers`, `VeriMol.Spelling.write_tooManyRingNumbers_iff`, `VeriMol.Spelling.write_tooManyRingNumbers_sound`, `VeriMol.run_rewrite_tooManyRingNumbers_iff`, `VeriMol.writePlain_isOk_iff_ringNumbers`, `VeriMol.writePlain_tooManyRingNumbers_iff`, `VeriMol.run_plain_tooManyRingNumbers_iff` |

- The theorems of the part before say that a text that comes out is right.
  These say when one comes out. The writer refuses some `Mol`s (sections
  9.4 and 12.3).
- What theorem 17 adds to the writer's own functions for its marks and its
  tokens: for a well formed `Mol` whose atoms can all be written, the tokens
  that a spelling makes can always be turned into text (a helper lemma,
  `Spelling.tokens_spelled`, says it for every `Mol` whose atoms can all be
  written, well formed or not).
- The seven statements of theorem 19, in the order of their names. The first
  three are for both spellings.
  1. For a `Mol` without stereo facts, a spelling gives a text exactly when
     the `Mol` is well formed, each of its atoms can be written (section
     9.4), and behind no atom more than 99 ring numbers are open.
  2. For a `Mol` without stereo facts, a spelling answers with the message
     about ring numbers exactly when the `Mol` is well formed, each of its
     atoms can be written, and behind some atom more than 99 are open.
  3. For every `Mol`, with or without stereo facts, that message is true
     whenever a spelling gives it: more than 99 ring numbers are then open
     behind some atom.
  4. For a text that is read as a `Mol` without stereo facts, `rewrite`
     prints the error about ring numbers exactly when more than 99 are open
     behind some atom of its `Mol`.
  5. The first of these for the plain spelling, with a count that names no
     function of the writer.
  6. The second for the plain spelling, with that count.
  7. The fourth for the command `plain`, with that count.
- The count of theorem 19: go through the atoms in the order of their
  numbers. Behind atom i, a ring number is open for each bond whose first
  atom is atom i or an earlier one, whose second atom comes after atom i,
  and that is written with a ring number. That is every bond but the one
  between an atom and its parent, the earlier atom that it is written next
  to (section 9.2), so the count names the writer's function for the
  parents. In the plain spelling the parent of an atom can only be the atom
  just before it. There the bonds with a ring number are those whose two
  atoms do not follow each other (section 9.1), and the last three
  statements count them so, without the parents. An example for the plain
  spelling, worked out from the count and not one of the statements: the
  `Mol` of section 9.4, a carbon atom as atom 0 with 100 others around it,
  has 99 ring numbers open behind atom 0 and gets a text; with 101 others
  it has 100 and gets the message.

Not proven:

- **Which atom is the parent of which, in other words than the writer's.**
  For the spelling with round brackets, which `rewrite` and `canonical`
  print, theorem 19 counts the ring numbers with the writer's own function
  for the parents (section 9.2). That this function finds the parents as
  that section describes them is tested: what the program writes must be
  what the model writes.
- **When a `Mol` with stereo facts gets a text, in plain words, and with which
  messages it can be refused.** Theorems 18 and 35, and all but one statement
  of theorem 19, are about a `Mol` without stereo facts. The writer has five
  more reasons to refuse a `Mol` with stereo facts (section 12.3); that these
  are all is tested. Each of the five can come for a text that the reader has
  read. Two are about where a spelling writes an atom with a free place:
  `plain` refuses 6 of the real texts for them and `canonical` 2, and
  `rewrite` none (see "Tested"). The three others come from every command that
  writes: section 12.3 has a text that is read for each of them. No real text
  was refused for one of these three.

### The same molecule, numbered differently

| # | Theorem | Its name in Lean |
|---|---|---|
| 20 | "The same molecule, numbered differently" (section 3.1) behaves as "the same" must: it is an equivalence relation. Three statements say so: it holds between every `Mol` and itself; if it holds between `m₁` and `m₂`, it holds between `m₂` and `m₁`; and if it holds between `m₁` and `m₂` and between `m₂` and `m₃`, it holds between `m₁` and `m₃`. A fourth statement says the same thing with the program's own function for a new order (`Mol.arrange`, section 3.2): a well formed `Mol` is another well formed `Mol` numbered differently exactly when it is that one with its atoms put in a new order, for an order that is a permutation of the atom numbers. | `VeriMol.Mol.Renumbered.refl`, `VeriMol.Mol.Renumbered.symm`, `VeriMol.Mol.Renumbered.trans`, `VeriMol.Mol.renumbered_iff_arrange` |
| 21 | If a well formed `Mol` is another well formed `Mol` numbered differently, and no atom got a new number, the two are equal. | `VeriMol.Mol.eq_of_renumberedBy_id` |
| 22 | A well formed `Mol` is fixed by its atoms, by which bonds it has and by which stereo facts it has: two well formed `Mol`s with the same atoms in the same order, the same bonds, the same orientations and the same geometries are equal. For the bonds, the orientations and the geometries, "the same" means that an entry is in the list of the one exactly when it is in the list of the other. | `VeriMol.Mol.eq_of_sameFacts` |

- There is an example each way (theorems 41 and 42), and one each way for
  a `Mol` with stereo facts (theorem 43).
- By theorem 22 the order of the lists of bonds, of orientations and of
  geometries says nothing of its own, because "well formed" allows one order
  only. Theorem 21 rests on the same fact.

### The chosen form

| # | Theorem | Its name in Lean |
|---|---|---|
| 23 | The chosen form of a well formed `Mol` (section 3.2) is the same molecule, numbered differently. | `VeriMol.Mol.renumbered_chosenForm` |
| 24 | The chosen form of a well formed `Mol` is well formed. | `VeriMol.Mol.chosenForm_wellFormed` |
| 25 | The chosen form of a well formed `Mol` has the least key (section 3.2): its key is not greater than the key of any well formed `Mol` that is the same molecule, numbered differently. Two keys are compared entry by entry from the front, and two entries number by number; this is Lean's own order of lists. A second statement: two well formed `Mol`s with the same key are equal, so the least key belongs to one `Mol` only. | `VeriMol.Mol.chosenForm_least`, `VeriMol.Mol.eq_of_key_eq` |
| 26 | Two well formed `Mol`s that are the same molecule, numbered differently, have the same chosen form, or the search gives up for both. | `VeriMol.Mol.chosenForm_eq_of_renumbered` |
| 27 | For a well formed `Mol` that has a chosen form: another well formed `Mol` is the same molecule, numbered differently, exactly when it has that same chosen form. | `VeriMol.Mol.renumbered_iff_chosenForm_eq` |
| 28 | The chosen form of the chosen form of a well formed `Mol` is itself. | `VeriMol.Mol.chosenForm_chosenForm` |

- Theorems 23 to 25, 27 and 28 speak of a `Mol` that has a chosen form: the
  search can give up, and then there is none. All of them are about the
  search as it is, with its two rules (section 3.2).
- These theorems hold for a `Mol` with stereo facts as they are stated. The
  key that theorem 25 speaks of holds the stereo facts (section 3.2), so two
  numberings of one molecule that differ in a stored mark only are told
  apart. Alanine and its mirror image are not the same molecule (theorem
  43), so they get two chosen forms wherever the search finds both (theorem
  27). That it finds them is tested. A molecule that is its own mirror image
  gets one.

### The command `canonical`

| # | Theorem | Its name in Lean |
|---|---|---|
| 29 | If `canonical` prints a text, the original text is read as a `Mol` that has a chosen form (section 3.2); the printed text is what the writer gives for that chosen form, and reading it returns the chosen form. | `VeriMol.run_canonical_is_chosenForm` |
| 30 | If `canonical` prints a text, reading that text returns the same molecule as reading the original, numbered differently. | `VeriMol.run_canonical_same_molecule` |
| 31 | If `canonical` prints a text for one text, it prints that same text for a second text exactly when the two are read as the same molecule, numbered differently. | `VeriMol.run_canonical_eq_iff` |
| 32 | Two texts that are read as the same molecule, numbered differently, get the same answer from `canonical`: the same text, or the same error. | `VeriMol.run_canonical_of_renumbered` |
| 33 | `canonical` prints its own output again when it is given that output. | `VeriMol.run_canonical_again` |
| 34 | A text that `canonical` prints comes back unchanged from `rewrite`: if `canonical` prints a text, then `rewrite` prints that same text for it. | `VeriMol.run_rewrite_of_canonical` |
| 35 | For a text that is read as a `Mol` without stereo facts, `canonical` prints a text or one of three errors, and nothing else: the `Mol` has more than 1,000 atoms; the search gives up; or the writer needs more than 99 ring numbers for the chosen form. The theorem says which answers can come, not when each comes. | `VeriMol.run_canonical_of_read` |

- What `canonical` prints is the chosen form of section 3.2 (theorem 29,
  with theorems 8, 23 and 25): the text that the writer gives for the
  numbering with the least key.
- Where `canonical` prints a text, it is one text for every numbering of the
  molecule (theorems 30 to 33): for such texts `canonical` decides whether
  two texts are the same molecule.
- Theorem 34 does not hold the other way round: `canonical` prints `CCO` for
  `OCC` (theorem 44), and `rewrite` prints `OCC` for it, which the tests
  show.
- Theorems 29 to 34 hold for a `Mol` with stereo facts as they are stated.
  Theorem 35 is about a `Mol` without them.

Not proven:

- **For which molecules the search gives up.** The theorems say what the
  chosen form is where the program works it out. Whether the search gives up
  does not depend on the numbering (theorem 26), and it does not give up for
  ethanol (theorem 44): without that example, all of these theorems could
  hold for a search that always gives up. The rest is counted on the real
  texts (see "Tested").

### Single examples

Lean works out itself what the program gives for each of these texts while
it checks the proof. In theorems 41 to 43 a short proof comes on top: that a
renumbering exists, or that none does. The tests ask the same texts.

| # | Theorem | Its name in Lean |
|---|---|---|
| 36 | Seven examples of what the reader gives. In each theorem the `Mol` that the rules of section 5 give is written out by hand. `CC`: two carbon atoms with three hydrogens each, joined by a single bond. `C=CC#N`: four atoms, a double bond, a single bond and a triple bond. `c1ccccc1`: six aromatic bonds, and one hydrogen at every atom. `[Na+].[Cl-]`: two atoms with their charges, and no bond. `[2H]O[2H]`: two hydrogens with mass number 2 that are atoms of their own. `[NH4+]`: one atom with four hydrogens and the charge +1. `[Mo]$[Mo]`: a quadruple bond. | `VeriMol.read_ethane`, `VeriMol.read_acrylonitrile`, `VeriMol.read_benzene`, `VeriMol.read_salt`, `VeriMol.read_heavyWater`, `VeriMol.read_ammonium`, `VeriMol.read_quadrupleBond` |
| 37 | `C-C` is read as the same `Mol` as `CC`, and `c:1:c:c:c:c:c:1` as the same `Mol` as `c1ccccc1`. | `VeriMol.read_writtenOutSymbols` |
| 38 | Three examples of what the reader gives for a text with stereo marks (section 12.2). Each theorem writes the `Mol` out, with its stereo facts worked out by hand. `N[C@@H](C)C(=O)O`: atom 1 has the orientation `anticlockwise`. `F/C=C/F`: the double bond has the geometry `oppositeSides`. `F/C=C\F`: it has the geometry `sameSide`. | `VeriMol.read_alanine`, `VeriMol.read_transDifluoroethene`, `VeriMol.read_cisDifluoroethene` |
| 39 | Acetic acid, `CC(=O)O`. Six statements: the `Mol` that the text is read as; what the program prints for the text, which is the first example of section 7; the plain spelling of that `Mol`, and its spelling with round brackets; and what `rewrite` and `plain` print for the text. | `VeriMol.read_aceticAcid`, `VeriMol.run_aceticAcid`, `VeriMol.writePlain_aceticAcid`, `VeriMol.write_aceticAcid`, `VeriMol.run_rewrite_aceticAcid`, `VeriMol.run_plain_aceticAcid` |
| 40 | Two examples of a refusal. For `C1CC` the program prints `error: position 1: ring 1 is opened but never closed`. For `CC(C))C(=O)[O-`, which has two problems, it prints the one further left: `error: position 5: ')' has no matching '('`. Each with exit code 1. | `VeriMol.run_refusal_ringNeverClosed`, `VeriMol.run_refusal_twoProblems` |
| 41 | `CCO` and `OCC` are read as two different `Mol`s, and the second is the first numbered differently. | `VeriMol.ethanol_renumbered` |
| 42 | `C1CCCCC1` and `C1CC1.C1CC1` are read as two `Mol`s with the same atoms and as many bonds, and the second is not the first numbered differently. | `VeriMol.cyclohexane_not_renumbered` |
| 43 | Two examples for "the same molecule, numbered differently" with stereo facts. `N[C@@H](C)C(=O)O` and `C[C@H](N)C(=O)O` are read as two different `Mol`s, and the second is the first numbered differently. `N[C@@H](C)C(=O)O` and `N[C@H](C)C(=O)O`, its mirror image, are read as two `Mol`s with the same atoms and the same bonds, and the second is not the first numbered differently. | `VeriMol.alanine_renumbered`, `VeriMol.alanine_not_mirrored` |
| 44 | `canonical` prints `CCO` for `OCC` and for `CCO`. | `VeriMol.run_canonical_ethanol` |

The examples carry weight, because most of the other theorems compare the
program with itself:

- Every command but `filter` has an example that is proven (for the two
  definitions of the filter, see "Known compounds"). Theorem 39 says for one
  text, `CC(=O)O`, what it is read as, what the program prints for it, how
  the two spellings write its `Mol`, and what `rewrite` and `plain` print.
  Theorem 44 does the same for `canonical`, and theorem 40 for two texts that
  are refused. For `rewrite` and `plain`, theorems 18 and 19 say when a text
  comes for a `Mol` without stereo facts, and theorem 39 shows for one `Mol`
  which text it is.
- In theorems 36 and 38 and in the first statement of theorem 39 the `Mol`
  is written out by hand, from the rules of section 5 and, for the stereo
  facts of theorem 38, of section 12.2. RDKit and Open Babel read each of
  these eleven texts with those atoms and bonds, and Open Babel's own record
  of the marks says the same stereo facts (that is tested, not proven).
  Theorem 37 compares two readings; theorem 36 says which `Mol`s those
  are.
- Without theorems 38 and 43, every other theorem could hold for a reader that
  drops the stereo marks of a text, beside a writer that refuses every `Mol`
  with stereo facts. Without theorem 38 alone, they could all hold for a
  reader and a writer that both took clockwise for anticlockwise, or the same
  side of a double bond for opposite sides. The two texts for L-alanine store
  different marks at atom 1: `anticlockwise` (theorem 38) and `clockwise` (a
  test). Theorem 43 says that they are the same molecule all the same, and
  that the mirror image is not. Without it, the first three statements of
  theorem 20 and theorems 21, 41 and 42 could hold for a definition that
  compares the stored marks as they stand, and so takes the two texts for
  L-alanine for two molecules.

### Molecules and canonical texts

Theorem 45 is no single example: its statements hold for every molecule and
for every canonical text. It stands here because it puts theorems of the
parts above together.

| # | Theorem | Its name in Lean |
|---|---|---|
| 45 | **Molecules and canonical texts correspond one to one.** A canonical text is the canonical text of a molecule exactly when it is read as that molecule. A molecule for which the writer of `canonical` gives no text has none. A molecule (the type `Molecule`) is a well formed `Mol`, up to the numbering of its atoms; a canonical text (the type `CanonicalText`) is a text that the writer of `canonical` gives for some `Mol`. Five more statements. Two canonical texts that are read as the same molecule are equal. Two well formed `Mol`s give the same `Molecule` exactly when one is the other numbered differently (section 3.1). The canonical texts are the texts that the command `canonical` prints unchanged. The way from a molecule to its canonical text is the writer of `canonical` (`writeChosen`), asked about any numbering of the molecule. The way back is the reader. | `VeriMol.Molecule.canonicalText_eq_some_iff`, `VeriMol.CanonicalText.molecule_injective`, `VeriMol.Molecule.of_eq_of_iff`, `VeriMol.isCanonicalText_iff_run`, `VeriMol.Molecule.canonicalText_of`, `VeriMol.CanonicalText.molecule_of` |

- A `Mol` numbers its atoms, so one molecule has many `Mol`s. A `Molecule` is
  the molecule itself: all the well formed `Mol`s that are one molecule,
  numbered differently, taken as one thing (a quotient type, in the words of
  Lean; the third statement says when two `Mol`s give the same one). So the
  theorem speaks of molecules where theorems 20 to 34 speak of `Mol`s, or of
  texts, that are the same molecule, numbered differently.
- The first statement, as Lean states it: `molecule.canonicalText = some text`
  exactly when `text.molecule = molecule`, for every molecule and every
  canonical text. It is about canonical texts only: `OCC` is read as ethanol
  as well, and it is not the canonical text of ethanol (theorem 44). The first
  of the two maps gives the canonical text of a molecule, or nothing where
  `canonical` writes no text for it; the second gives the molecule that a
  canonical text is read as. The fifth and the sixth statement say that these
  two are the writer of `canonical` and the reader.
- So the writer of `canonical` and the reader undo each other, between the
  molecules for which `canonical` writes a text and the canonical texts
  (a bijection). From such a molecule to its canonical text and back gives
  the molecule again, and from a canonical text to its molecule and back
  gives the text again. Every canonical text belongs to exactly one
  molecule, and a molecule has at most one canonical text.
- The `Mol`s of this theorem need not come from a text: a molecule is the
  molecule of any well formed `Mol`. Theorem 31 says the like for two texts
  and the command.
- The correspondence is not empty: `CCO` is a canonical text, by theorem 44
  and the fourth statement, and so it is the canonical text of the molecule
  that it is read as, which is ethanol.
- The two types and the two maps stand with the proofs
  (`VeriMol/Proofs/Molecule.lean`), not in Core: they are there to state the
  theorem, and the program runs none of them.
- The canonical texts are defined with the writer of `canonical`
  (`IsCanonicalText`, and with it the type `CanonicalText`). So the
  fingerprints of five of the six statements (all but the third) cover that
  writer as well, with the search, the spelling and the messages that it
  uses: a change to one of these shows as changed lines of the ledger (see
  "Trusted" for what a fingerprint covers). The fingerprints do not cover
  the two maps, nor `Molecule.of`, which gives the molecule of a `Mol`. What
  the maps are is said by the fifth and the sixth statement, through
  `Molecule.of`; when `Molecule.of` gives the same molecule is said by the
  third.

Not proven:

- **Which molecules have a canonical text.** A molecule has none where the
  writer of `canonical` answers with an error: where the search gives up,
  where the `Mol` has more than 1,000 atoms, and where the writer refuses
  the chosen form (sections 3.2, 9.4 and 12.3). The theorem does not say for
  which molecules that is. Of the 62,075 real texts that the program reads,
  62,073 get a canonical text (see "Tested").
- **That a molecule of this theorem is what a chemist calls one molecule.**
  "The same molecule" is about the numbering of the atoms and nothing else
  (section 3.1). `c1ccccc1` and `C1=CC=CC=C1` are two molecules here, each
  with its own canonical text, and so are `C` and `[H]C([H])([H])[H]`; a
  `Mol` can hold several separate pieces, so `[Na+].[Cl-]`, or two molecules
  of cyclopropane written as `C1CC1.C1CC1`, is one molecule here, with one
  canonical text; a mark that tells nothing apart is kept (section 12.4);
  and a `Mol` can be well formed without being a molecule that exists
  (section 3). So two equal canonical texts are the same molecule, and two
  different canonical texts need not be two different compounds.

### The filter

The command `filter` reads a SMILES text and hands the `Mol` on only if the
`Mol` is sound and a rule holds for it (section 16). Whatever passes is
proven to satisfy the rule, and nothing beyond the rule. The filter is made
of four pieces:

1. **Sound.** One definition of which `Mol`s a rule may be asked about
   (`Mol.Sound`, section 16.2).
2. **The rule.** A property that is relevant to the safety of a compound,
   as a short predicate on a `Mol` that says what is meant and not how it is
   found. One rule is built: the `Mol` has no perfluorinated group of `n` or
   more carbon atoms (`Mol.NoFluoroGroup`, section 16.3), for a number `n`
   that is given with the command.
3. **A checker for each of the two.** A function of the program that answers
   yes or no. For the rule it works out the carbon atoms of the groups, and
   then a search spreads from one of them along the bonds.
4. **The filter.** It reads the text, asks once whether the `Mol` is sound,
   asks the checker of the rule, and then hands the `Mol` on or refuses.

The two definitions stand with the proofs, in
`VeriMol/Proofs/Predicates/Sound.lean` and
`VeriMol/Proofs/Predicates/FluoroGroup.lean`: they are written to be read,
and the program runs neither. The checkers and the filter stand in Core
(`VeriMol/Core/Sound.lean`, `VeriMol/Core/FluoroGroup.lean`,
`VeriMol/Core/Filter.lean`).

| # | Theorem | Its name in Lean |
|---|---|---|
| 46 | **Sound, and its checker.** A `Mol` is sound when it is well formed and each of its atoms passes five tests: its element is one of B, C, N, O, P, S, F, Cl, Br and I; it has no mass number; its charge is 0; it has no aromatic bond, or at least two; and its bonds and hydrogens add up to a usual valence of its element, or, for an atom with aromatic bonds, to one below a usual valence (section 16.2). The checker of the program says yes exactly when the `Mol` is sound, for every `Mol`. A second statement: of two well formed `Mol`s that are the same molecule, numbered differently, both are sound or neither is. | `VeriMol.Mol.isSound_iff`, `VeriMol.Mol.Renumbered.sound_iff` |
| 47 | **The rule itself.** Four statements about the rule "no perfluorinated group of `n` or more carbon atoms", and none of them about a program. The carbon atoms of the perfluorinated groups are the fluorinated carbon atoms and the branch carbon atoms, which meet the same five conditions, need not carry fluorine and are bonded to at least three carbon atoms of a group (section 16.3). Such atoms that are linked are linked both ways, and atoms that are linked to a third are linked to each other: so they fall into groups, and a group does not depend on the atom from which it is entered. A group of at least `n` is a group of at least `k`, for every `k` up to `n`: so a smaller number is the stricter rule. And for well formed `Mol`s the rule gives the same answer for every numbering of the atoms of a molecule. | `VeriMol.Mol.FluoroLinked.symm`, `VeriMol.Mol.FluoroLinked.trans`, `VeriMol.Mol.HasFluoroGroup.of_le`, `VeriMol.Mol.Renumbered.noFluoroGroup_iff` |
| 48 | **The checker of the rule is right**, for every `Mol` and every number `n`. The search of the program returns, for an atom, exactly the atoms that are linked to it. The number that the program gives is the size of the largest group: the `Mol` has a perfluorinated group of at least `n` carbon atoms exactly when `n` is at most that number. And the checker says yes exactly when the `Mol` has no perfluorinated group of `n` or more carbon atoms. | `VeriMol.Mol.mem_fluoroGroupOf`, `VeriMol.Mol.le_largestFluoroGroup_iff`, `VeriMol.Mol.hasNoFluoroGroup_iff` |
| 49 | **What passes the filter.** For any rule whose checker says yes, for a sound `Mol`, exactly when the rule holds: the filter hands on a `Mol` exactly when the reader gives that `Mol` for the text, the `Mol` is sound, and the rule holds for it. For the rule that is built: the filter hands on the `Mol` `m` for a text and a number `n` exactly when the reader gives `m` for the text, `m` is sound, and `m` has no perfluorinated group of `n` or more carbon atoms. Four more statements, about the program. Behind the words `filter` and `perfluoro` and a number from 1 on, a text gets what the filter gives: the printed layout of the `Mol`, or the reason of the refusal as the error. Such a number is a text of one or more of the digits `0` to `9` and nothing else, whose number is not 0. The program prints the printed layout of `m` and ends with exit code 0 exactly in the case above. And it ends with exit code 0 exactly when the text is read as a `Mol` that is sound and has no such group. | `VeriMol.filter_eq_ok_iff`, `VeriMol.filterPerfluoro_eq_ok_iff`, `VeriMol.run_filter`, `VeriMol.groupSize?_eq_some_iff`, `VeriMol.run_filter_eq_iff`, `VeriMol.run_filter_exitCode_iff` |

- So whatever passes the filter satisfies the rule, and no `Mol` that is read,
  is sound and satisfies the rule is held back. Theorem 49 holds for every
  text and every number: it is no statement about the texts that were
  tried. As Lean states it:
  `filterPerfluoro n text = .ok m` exactly when `read text = .ok m`,
  `m.Sound` and `m.NoFluoroGroup n`.
- The statement is about the `Mol` that is handed on, the object itself, and
  not about a text for it. So it needs no theorem about another numbering,
  and it does not depend on `canonical` giving a text.
- A "no" has no witness. That a `Mol` has a group of seven carbon atoms can
  be shown by naming the seven. That it has none of six or more is a
  statement about every set of atoms of the `Mol`, and no finite list of
  tests of the search can establish it for every `Mol`. Theorem 48 does: the
  search leaves no atom out. This is its hard half, and the proof follows
  the search step by step, with a bound on the number of steps that is shown
  to be enough.
- Theorem 48 asks nothing of the `Mol`: it holds for every `Mol`, sound or
  not, well formed or not. The first statement of theorem 49 asks less of a
  rule's checker, to be right for sound `Mol`s, and so a later checker may
  rely on soundness.
- A further rule needs three things: a predicate, a checker, and the proof
  that the checker is right for every sound `Mol`. The first statement of
  theorem 49 then says what its filter hands on. Several rules together are a
  rule again, whose checker says yes when each of theirs does.
- The fingerprints of these theorems cover the definitions of `Sound` and
  of the rule, with everything that they are defined with. They do not
  cover the two checkers, the filter and the messages: those are what the
  theorems are about (see "Trusted").

Not proven:

- **That the rule and `Sound` say what is meant.** Both are readings, and no
  theorem says that they are the right ones. The rule reads a wording for
  long chains, perfluoroalkyl carboxylic acids "with 7 or more
  perfluorinated carbons" and perfluoroalkane sulfonates "with 6 or more",
  for any number, for groups of any shape and in any compound (the head of
  `VeriMol/Proofs/Predicates/FluoroGroup.lean` has the source). Section 16.4
  says what that decides, with the examples of section 16.3: one fluorine
  atom on a carbon atom without hydrogen is enough; an oxygen atom between
  two groups parts them, so a perfluoroether acid can pass; a carbon atom
  without fluorine is counted only where three carbon atoms of a group hold
  it; and chlorine, bromine and iodine on a carbon atom are not looked at,
  so a chain of a chlorofluorocarbon is counted. That every carbon atom of a
  perfluoroalkyl group without a ring is counted is tested for the acids
  with a group of up to ten carbon atoms, and not proven (see "Tested").
  `Sound` is five tests that look at one atom at a time (section 16.2): it
  refuses a compound that is written with charges, it does not ask whether
  an aromatic ring can be written with single and double bonds in turn, and
  it takes the usual valences of SMILES, so that a nitrogen atom with five
  single bonds is sound.
- **That a compound which passes is harmless.** No result says that. The
  rule names one pattern of a structural formula.
- **That `SPEC.md` reads a SMILES as chemists do.** Theorem 49 speaks of the
  `Mol` that the reader gives. That this is what the text means is tested
  and not proven (see "Tested" and "Trusted").
- **What is made of the `Mol` afterwards.** The filter hands on a `Mol`, and
  the program prints its layout, which shows the whole `Mol` (theorem 2). A
  printed `Mol` that passed the filter looks like any other printed `Mol`:
  only the exit code of the command says that it passed.
- **Which reason a refusal gives.** Theorem 49 says when a `Mol` is handed
  on. That a refusal names the first test that fails, the right atom and the
  right size is tested against the model and not proven. (The size in the
  message of the rule is the number of which theorem 48 speaks.)
- **Anything about another way of writing a compound, beyond the numbering
  of its atoms.** The same compound with a hydrogen written as an atom of
  its own, or with charges, is another `Mol`, and it is not sound. A ring
  with aromatic bonds and the same ring with single and double bonds in turn
  are two `Mol`s as well; the rule gave both the same answer wherever it was
  tried, and no theorem says so.

### Known compounds

A proof cannot show that a definition says what was meant. So `Sound` and
the rule of the filter are held against six compounds whose answers are
known. Each is one theorem in `VeriMol/Proofs/Compounds.lean`, and says for
one text: the reader reads it, its `Mol` is sound, and the largest
perfluorinated group of the `Mol` has exactly so many carbon atoms (there is
a group of at least that size, and none that is larger).

| Compound | Text | Largest group | Its name in Lean |
|---|---|---|---|
| PFOA, perfluorooctanoic acid | `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F` | 7 | `VeriMol.pfoa_largestGroup` |
| PFHxS, perfluorohexanesulfonic acid | `OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F` | 6 | `VeriMol.pfhxs_largestGroup` |
| PFHxA, perfluorohexanoic acid | `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F` | 5 | `VeriMol.pfhxa_largestGroup` |
| an isomer of PFOA with a branch, perfluoro-6-methylheptanoic acid | `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(C(F)(F)F)C(F)(F)F` | 7, although no chain in it has more than six fluorinated carbon atoms | `VeriMol.isoPFOA_largestGroup` |
| an isomer of PFOA whose branch point carries no fluorine, perfluoro-5,5-dimethylhexanoic acid | `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F` | 7: the carbon atom at the branch is a branch carbon atom, held by three –CF3 | `VeriMol.tertButylPFOA_largestGroup` |
| ibuprofen | `CC(C)Cc1ccc(cc1)C(C)C(=O)O` | none | `VeriMol.ibuprofen_noFluoroGroup` |

- **Where the numbers come from.** The wording for long chains that the
  file of the rule quotes names carboxylic acids "with 7 or more
  perfluorinated carbons", of which PFOA is the smallest, and the paper that
  it is quoted from sets PFHxS, C6F13SO3H, beside PFHxA, C5F11COOH: two
  acids with six carbon atoms each, with six and with five perfluorinated
  carbon atoms. The two isomers follow from its formula for a perfluoroalkyl
  group, which takes branched groups in.
- **In what sense they are proven.** In the sense of the theorems above:
  Lean's kernel checks them whenever the project is built, and once more in
  `lake test`, and `#print axioms` shows for each nothing beyond the three
  standard axioms of Lean. The kernel works each answer out itself: it runs
  the reader on the text, and then the two checkers, which are proven right
  (theorems 46 and 48).
- **What sets them apart.** They are statements about single texts, and the
  ledger has no line for them. So no fingerprint holds their statements in
  place: a change to one of them shows in its file and nowhere else. The
  report of the build counts them among the helper lemmas outside the
  ledger, and says that all of those are proven. The two definitions that
  they speak of are held in place all the same, by the fingerprints of
  theorems 46 to 49.
- **What they do not say.** Each is about one text. For `Sound` and for the
  rule the answer is the same for every numbering of a molecule (theorems 46
  and 47); nothing general is proven about one compound that is written in
  two ways which are no renumbering of each other. And "Not proven" under
  "The filter", above, holds for these statements as well.
- **What it costs.** For such a theorem Lean's kernel runs the reader and
  both checkers. On one desktop machine a statement of this form took half a
  second for ibuprofen, 3.6 seconds and 1.1 GB of memory for a text of 126
  characters with 62 atoms (paclitaxel without its stereo marks), and 17
  seconds and 3.4 GB for a chain of 200 carbon atoms. So a much larger
  molecule is out of reach in this way. The compiled program is not bound
  by that: it asks the filter about a chain of 1,000 fluorinated carbon
  atoms in less than a second. Its answer is then worked out by functions
  that are proven right, and it is not itself a proof that Lean's kernel
  has checked.

## Tested

Tested is less than proven. The specification exists a second time as a Python
program, the model (`reference/model.py`), and the Lean program must give the
model's answer, text by text. The model is a test of `SPEC.md`: it is not Lean
and proves nothing. It was written from the same `SPEC.md` by the same AI
assistant as the Lean program, and the Lean writer follows the model's way of
working, so a misreading that both share shows no mismatch. Against that, the
model is checked against programs that other people wrote, and two checks hold
the Lean program against other programs themselves, without the model:
`check_direct.py` against RDKit and Open Babel for what it reads and writes,
and `check_filter.py` against RDKit for what its filter answers. These can judge
what a text says, what is written and how large the largest perfluorinated
group of a compound is, not the words and the positions of the error
messages: for those the model and `SPEC.md` are the only reference.

RDKit is version 2024.03.3 and Open Babel is version 3.1.1. The checks are
the scripts of the folder `reference/`, and
[`reference/README.md`](reference/README.md) says how each one works, how to
run it and how to read what it prints.

- **`check_app.py`.** The function that is the whole program gives exactly
  what the model gives: the output, the error message and the exit code. For a
  sample, the compiled program prints exactly that.

  *On what, and what came out:* 1,234,594 questions: 612,499 texts alone;
  132,499 of them again behind each of the three command words; and 224,598
  questions to the filter. The texts are the 62,099 real ones, 4,550 of them
  with stereo marks; 400,000 damaged ones; 100,000 random ones; 20,000 real
  texts in which stereo marks are turned round; 400 texts made up near the
  limit of the search for the chosen form, for 94 of which the search gives
  up; and 30,000 invented compounds with fluorine on a skeleton of carbon
  atoms, with rings, branches and other atoms in between, each written from
  a random atom. The real texts, 50,000 of the random ones, the 20,000 and
  the 400 are also asked behind `rewrite`, `plain` and `canonical`. Behind
  the words `filter perfluoro` stand the real texts twice, with the numbers 6
  and 1; the 30,000 invented compounds, each with a number from 1 to 8; and
  the 70,400 others of the groups before, with the number 1. With the number
  1 the filter names the size of the largest perfluorinated group of every
  sound `Mol` that has a fluorinated carbon atom, so these questions compare
  that size, and each of the six messages of section 16 that the command can
  give is among the answers.
  Every question is put to the function, through a second small program
  that answers up to a thousand of them in one start (`Answers.lean`). The
  compiled program itself is started for a sample of 22,186 of them. No
  mismatch.

- **`check_direct.py`.** The function that is the whole program reads the
  atoms and bonds that RDKit reads, atom by atom and bond by bond, asked
  without the model in between. Open Babel reads the same atoms, with the same
  atoms bonded; it works out aromatic bonds by its own rules, so a bond that
  one of the two calls aromatic and the other single or double is not counted
  as a difference. From what the function writes for `rewrite` and for
  `plain`, RDKit reads the atoms and bonds that were read, and Open Babel
  reads the written text as it reads the original one. RDKit takes each
  canonical text for the same atoms and bonds as the rewritten text, hydrogens
  included: 62,072 by its own canonical text, and 1 by a search for each of
  the two inside the other (`reference/README.md` says why).

  *On what, and what came out:* The 62,099 real texts. Of the 62,075 that the
  program reads, RDKit reads 62,070 with exactly the same atoms and bonds, and
  5 with other hydrogens at one to four atoms, in a way that section 11.2
  lists. Open Babel reads all 62,075 with the same atoms and the same atoms
  bonded; in 7,336 of them a bond is aromatic for one of the two and single
  or double for the other. RDKit reads all 62,075 rewritten texts and all
  62,069 texts of the plain spelling as exactly the atoms and bonds that the
  program read from the original text, and each of the 62,073 canonical texts
  as exactly the atoms and bonds that the program reads from that text.
  47,446 of the rewritten texts and 48 of the texts of the plain spelling are
  the original text, character for character: for these, comparing the
  written text with the original can show nothing new.
  The stereo facts are compared through the texts: with its clean-up on, RDKit
  takes the original and the rewritten text for the same molecule, stereo
  included, for 4,517 of the 4,528 texts with stereo marks, and gives no
  verdict for the other 11: its clean-up refuses 9 of these texts as they
  stand, and for 2 it refuses the rewritten text, in which four nitrogen atoms
  have a hydrogen that RDKit does not count (section 11.2). It says the same
  of the original text and the text of the plain spelling for 4,511 texts,
  and of the original and the canonical text for 4,515, each time with no
  verdict for 11 more; the others are the 6 and the 2 texts for which `plain`
  and `canonical` write nothing. Of the wrong answers that the script makes
  on purpose, those about atoms, bonds and hydrogens are noticed every time;
  the rewritten text with one stereo mark turned round is reported as another
  arrangement in space for 4,515 of the 4,528 texts, gets no verdict for 11,
  and is taken for the same molecule for 2. A run on all texts must give
  exactly the numbers that the script records. This check cannot see which
  numbering a canonical text has, and it does not look at the stored stereo
  facts themselves.

- **`check_filter.py`.** What the filter answers is what RDKit finds in the same
  text, asked without the model in between: with RDKit's own reading of the
  text, its clean-up on, with the patterns of section 16.3 written a second
  time, in RDKit's pattern language, with the branch carbon atoms worked out
  from RDKit's own record of the bonds, and with RDKit's own search for the
  atoms that hang together. The theorems say that the program does what
  section 16 defines. This check looks for places where the program's
  reading of a text, or its search, differs from RDKit's.

  *On what, and what came out:* The 62,099 real texts. Of the 62,075 that
  the program reads, the filter takes 52,533 for sound. Of the 9,542 others,
  the first test that fails is the charge for 7,865, the element for 1,631,
  the usual valence for 41 and the mass number for 5. For 52,530 of the
  sound ones, RDKit's search finds a largest perfluorinated group of exactly
  the size that the filter names; the other 3 RDKit's clean-up refuses: each
  has a ring that is written with lowercase symbols and that cannot be
  written with single and double bonds in turn as it stands, which "sound"
  does not ask. 50,758 of the sound ones have no fluorinated carbon atom,
  1,690 a largest group of one carbon atom, 51 of two to five, and 34 of six
  or more. With the number 6 the filter hands 52,499 on and refuses those 34,
  and RDKit finds a group of six or more in none that is handed on. Among
  the `Mol`s that are not sound, RDKit finds such a group in 3, which are
  anions of perfluorinated acids, written with a charge. Then other
  spellings: 28 compounds, each written by RDKit in 23 more ways: its atoms
  in 20 random orders, single and double bonds in the place of aromatic
  ones, every hydrogen count in square brackets, and every hydrogen as an
  atom of its own. The filter gives each of the first 22 spellings the answer
  of the compound as written, and it refuses each of the 18 spellings that
  have a hydrogen as an atom, as not sound. Three texts written by hand,
  with a bond symbol `:` or lowercase symbols at carbon atoms with four
  bonds: two are not sound, and for the third the filter and RDKit find a
  largest group of the same size, six. Then every isomer: for each way to
  join the carbon atoms of a perfluoroalkyl group of 1 to 10 atoms without a
  ring, the carboxylic acid and the sulfonic acid, 1,758 texts in all, among
  them the 39 isomers of perfluorooctanoic acid and the 89 of
  perfluorooctanesulfonic acid. For each of them the filter and RDKit's search
  both name the number of carbon atoms of the group, wherever its branches
  stand, and with the number 6 the filter refuses each of the 1,726 whose
  group has six or more. A run on all texts must give exactly the 32 numbers
  that the script records.
  This check cannot judge whether the rule is the right one: RDKit is asked
  for the same pattern, written a second time. It shows that two programs,
  with two independent readings of the text and two searches, find a largest
  group of the same size with it. And it cannot judge the five tests of
  "sound": for a `Mol` that the filter refuses as not sound, nothing is
  compared but the count.

- **`check_corpus.py`, on reading.** The model reads what RDKit reads, atom
  by atom and bond by bond: element, isotope, charge and hydrogens of every
  atom, and every bond.

  *On what, and what came out:* The 62,075 real texts that the program reads:
  62,070 are read the same, and 5 differ in the hydrogens of one to four
  atoms, in a way that section 11.2 lists. Of the other 24, which RDKit reads,
  16 are refused for the spelling of a stereo centre that RDKit and Open Babel
  read as mirror images of each other (section 12.4), and 8 for other
  notation that the program does not read.

- **`check_corpus.py`, on writing.** RDKit reads every text that the model's
  writer makes as exactly the `Mol` that was written. With its clean-up on,
  it finds the same arrangement in space as in the text that was read,
  wherever it can compare the two.

  *On what, and what came out:* The `Mol`s of the real texts, in both
  spellings, as they are and with their atoms renumbered at random; and three
  random spellings by RDKit of each real text with stereo marks (see "What the
  checks found for stereo marks" below).

- **`check_stereo.py`.** The stereo facts that the model stores are what the
  marks of a text say. This is tested with the reader alone, without the
  writer.

  *On what, and what came out:* The 4,528 real texts with stereo marks that
  the program reads: against Open Babel's own record of the marks, and against
  coordinates in space that RDKit builds (see "What the checks found for
  stereo marks" below).

- **`check_canonical.py`.** The chosen form of the model is the one that
  section 3.2 defines. It stays the same when the atoms are renumbered at
  random and when RDKit spells the molecule in another way. Two real texts
  that have a chosen text get the same one exactly when RDKit gives what
  `rewrite` writes for them the same canonical text. RDKit is asked with its
  clean-up off and with every hydrogen made an atom of its own
  (`reference/README.md` says why).

  *On what, and what came out:* The 62,075 real texts that the program reads.
  Each of the 62,073 that get a chosen text is renumbered once at random; one
  random spelling by RDKit is compared for 62,044 of them. The comparison with
  RDKit's canonical text is made for 62,060 of them, which fall into the same
  60,708 groups both ways; 13 texts with stereo marks are left out of it (see
  below). For the 1,078 `Mol`s among them with at most 7 atoms, the key of
  every numbering is worked out one by one. No chosen text has a dot inside a
  piece of the molecule. The search gives up for none of the real texts, so
  twenty made-up texts near its limit are renumbered ten times each: the
  answer is the same for every numbering, a chosen form or a search that gives
  up. Five wrong searches are tried, and each is reported. And a wrong answer
  is made on purpose for nearly every text, 61,825 of them: the same `Mol`
  with one hydrogen fewer, to which RDKit gives another canonical text each
  time.

- **`check_spec.py`.** The examples and the claims of `SPEC.md`.

  *On what, and what came out:* 278 checks against the model, RDKit, Open
  Babel and the OpenSMILES document; 30 of them are about the filter (section
  16).

- **`check_random.py`.** Four claims of `SPEC.md` under attack: every text of
  its grammar is read or refused for what it says, and no other text is read;
  nothing inside a text is wrong before the reported position; where the model
  and RDKit part ways on a text, it is in a way that `SPEC.md` lists; a
  written text is read back as the same `Mol`.

  *On what, and what came out:* Hundreds of thousands of random and damaged
  texts, made from a fixed set of pieces, some of them with stereo marks;
  100,000 random `Mol`s made without stereo facts, and 100,000 in which an
  atom or a double bond that can have a stereo fact gets one at random, so
  that 22,273 of them hold one; all made without any text, and about six in
  ten of each get a text; and 3,000 `Mol`s near the limit of 99 ring numbers,
  for which the writer must refuse exactly when a count made from `SPEC.md`
  says so. No violation was found. A kind of difference from RDKit that needs
  a piece which is not in the set cannot show here.

- **`check_tests.py`.** The expected results of the Lean tests are what the
  model gives. Every message of the reader (sections 6 and 12.2) has a test,
  with its position. Every place of the table "What may come next" (section 6)
  is reached by a test text, and where that table refuses a test text, the
  expected answer is the one that section 6 gives in words.

  *On what, and what came out:* The 869 test texts (section 11.1 says which
  they are; 48 of them were written for the filter, and 27 more are the
  examples of section 16).

- **`lake test`.** Single functions, and the whole program: as a function, as
  the compiled program, and through the second program that `check_app.py`
  uses.

  *On what, and what came out:* 15,230 tests on Linux; a system without the
  device `/dev/full` leaves one of them out and says so. Their expected
  results come from the model or are worked out by hand, never from the Lean
  program. Of these, 9,290 are about the whole program, 1,356 of them about
  the command `filter` (1,281 put a text to the filter, and 75 try other forms
  of the command); and 781 ask the two checkers of the filter about 207
  `Mol`s: whether each is sound, with the first reason if it is not, and
  which perfluorinated groups it has.

- **What these tests notice, tried with two mistakes.** Two mistakes were
  put into the search for the groups on purpose, one at a time, and the
  tests were run without the proofs. With the first, the search follows a
  bond only towards the atom with the higher number. Each of the 9,290 tests
  of the whole program and each of the 781 tests of the two checkers still
  passes; three hand-written tests of the search fail, and the one that has
  the kernel check the proofs again. `check_filter.py` finds it in 2 of the
  62,099 real texts, and in one of its 28 compounds, a small ring, as
  written and in 13 of the other spellings; none of its 1,758 texts of
  isomers shows it, because their groups have no ring. `check_app.py` finds
  it in 657 of its 1,234,594 questions: those 2 real texts with both
  numbers, and 653 of the 30,000 invented compounds with fluorine. With the
  second, the search may take 1,000 steps, in the place of four for every
  atom of the `Mol` and one more. Every test of `lake test` passes but the
  one that has the kernel check the proofs again, `check_filter.py` passes
  with its recorded numbers, and `check_app.py` finds no mismatch for its
  1,234,594 questions.
  The changed program is wrong all the same: it hands on a chain of 1,001
  fluorinated carbon atoms with the number 1,001. With either mistake,
  proofs of theorem 48 no longer build.
  To repeat the trial, change one line of `VeriMol/Core/FluoroGroup.lean`.
  For the first: in `Mol.spread`, `m.neighbours c ++ todo` becomes
  `(m.neighbours c).filter (c < ·) ++ todo` (`List.filter` is Lean's own
  function, not the filter of this project); the changed program then hands
  on the ring `FC1(F)OC(F)(F)C(F)(F)C(F)(F)C(F)(F)C1(F)F` with the number 6.
  For the second: in `Mol.fluoroGroupAmong`, the bound
  `4 * m.atoms.length + 1` becomes `1000`; the chain is `F`, then `C(F)(F)`
  1,001 times, then `F`. `lake build app` builds the changed program,
  because it leaves the proofs out, and the tests run without the proofs
  when `"VeriMol"` and `"Audit"` are taken out of the line `needs` of the
  test program in `lakefile.toml`. No file of this repository repeats the
  trial.

### What the checks found for stereo marks

The model was run (`check_corpus.py`) on the 62,099 real texts, of which 4,550
carry stereo marks, and on three random spellings by RDKit of each of the
4,541 of those that RDKit reads with its clean-up on: 13,623 texts. A written
text passes when all of these hold: the model reads it back as exactly the
same `Mol`; RDKit, with its clean-up off, reads exactly the atoms and bonds of
that `Mol` from it; and RDKit, with its clean-up on, finds the same
arrangement in space as in the original text, wherever it can compare the two.

| What is read and written | Texts read | Plain spelling | Round brackets |
|---|---|---|---|
| the real texts as they are | 62,075 | 62,069 passed, 6 refused | 62,075 passed |
| the random spellings by RDKit | 13,614 | 13,611 passed, 3 refused | 13,614 passed |
| the real texts, with the atoms renumbered at random before writing | 62,075 | 62,035 passed, 40 refused | 62,035 passed, 40 refused |

- No text failed. The writer refused a `Mol` for three reasons only: a stereo
  centre with a free place would stand without an atom before it, or would be
  written with one ring number and only single bonds (section 12.3), or more
  than 99 ring numbers were needed. The third happens only after renumbering,
  to 34 molecules. The other refusals of section 12.3 did not occur.
- The real texts that are read hold 16,737 atoms with an orientation, 7 of
  them with a free place, and 1,281 double bonds with a geometry. 24 real
  texts and 9 of RDKit's spellings are not read (sections 11.2 and 12.4).
- Marks at ring numbers (section 12.2, rule 8): the renumbered molecules with
  stereo marks were also written, in the plain spelling, with the mark of each
  ring bond at the closing ring number, and at both. All 4,498 texts written
  passed in both forms.
- The renumbering of these checks is written out by the rule for a stored
  mark: an orientation turns round when an odd number of swaps puts the new
  numbers of the neighbours in order, and a geometry when the
  lowest-numbered other neighbour becomes another atom at exactly one of
  the two ends. For all 4,528 `Mol`s with stereo facts it gives the `Mol`
  that the model gives when it puts the atoms into the new order through
  the two functions of section 12.1 (`Mol.orientationOf`,
  `Mol.geometryOf`).
- The checks notice a wrong text: with `@` and `@@` swapped in the written
  text, RDKit finds another arrangement in space for 3,769 of 3,926 real
  texts. For the rest it calls both the same molecule: there the molecule
  is its own mirror image, or the marks say nothing.
- With round brackets, 1,794 of the 4,528 real texts with stereo marks that
  were written came back character for character, and 10,967 of the 13,611
  spellings by RDKit that still carry a mark.

Every comparison above goes through the writer. A model that took clockwise
for anticlockwise in reading and in writing alike would pass them all. So
the stored facts are also compared in two ways that use the reader alone
(`check_stereo.py`):

- **Open Babel's own record.** After it has read a text, Open Babel holds a
  record of what each mark says. Said in the words of section 12.1, the
  record is what the model stores: for all 16,737 atoms with an orientation
  and all 1,281 double bonds with a geometry in the 4,528 real texts with
  stereo marks that are read. Neither of the two has a fact that the other
  lacks.
- **A measurement.** RDKit builds coordinates in space for a text, and the
  orientation and the geometry of section 12.1 are measured on them. For
  all 14,354 atoms and all 1,220 double bonds that were compared, the model
  stores what was measured. This way does not reach every atom. 4,398 texts
  got coordinates. Of the others, 85 have more than 90 atoms, hydrogens not
  counted, and are left out because building coordinates for them takes too
  long; for 36 RDKit built no coordinates; and 9 RDKit refuses when its
  clean-up is on, which building coordinates needs. These texts hold 2,227
  of the atoms and 57 of the double bonds. In a text with coordinates, an
  atom is compared only where RDKit gives it the same label (R or S) from
  the text and from its own coordinates, and a double bond likewise (E or
  Z). Elsewhere the coordinates do not show what the text says: at 156
  atoms and 4 double bonds. Of the 7 atoms with a free place, 2 were
  measured. To the other 5 RDKit gives no label. On another machine the
  counts of this measurement can differ by a few (`reference/README.md`).
- **A wrong model is noticed.** With the helper that decides between the
  two orientations made wrong on purpose, each way reports every atom that
  it compares in the first 300 texts (1,152 and 1,075 atoms). With every
  stored geometry exchanged for the other one, each reports every double
  bond (119 and 106).

For the chosen form (`check_canonical.py`): 4,526 of the 62,073 real texts
that have a chosen text have stereo facts. Left out of the comparison with
RDKit's canonical text are 13 texts with stereo marks: RDKit's canonical text
has fewer marks than the text, or the program does not read it. RDKit's
canonical text leaves out a mark that tells nothing apart, as is usual for a
canonical text, and, in the texts that were tried, a mark at a nitrogen atom
with a free place outside a ring of three. This program stores every mark as
written and does not judge it (section 12.4). One of the 13 is left out only
with the hydrogens made atoms: RDKit's canonical text then has no mark at a
double bond that lies in a ring of five atoms, where the bond exists in one
form only. What is said here of these 13 texts was seen by looking at them:
the script counts them and does not print it.

## Trusted

- **Lean's kernel.** It is the program that checks the proofs.

  *What limits the trust:* It checks every declaration during the build, and
  `lake test` has it check those of Core and Proofs once more, separately from
  the build (`leanchecker`).

- **Three axioms of Lean: `propext`, `Classical.choice`, `Quot.sound`.** Most
  of the proofs use them.

  *What limits the trust:* They are the standard ones. The audit allows no
  other, and the report of every build lists the axioms of each numbered
  theorem.

- **The statements of the theorems.** A proof shows that a statement holds. It
  does not show that the statement says what was meant. A person has to read
  the statements and the definitions they rest on, such as "well formed".

  *What limits the trust:* The ledger records a fingerprint of every
  statement of the 49 numbered theorems, and of the definitions of
  statements and types that it rests on, so neither changes unnoticed by
  accident. The six theorems about known compounds have none (see "Known
  compounds"). A fingerprint is computed from Lean's own numbers for
  expressions, which have 32 bits: a change that is made in order to keep
  the fingerprint can be found by trying, and is not ruled out. The
  functions and the texts of the program that a statement names, such as
  `read` or the words of a message, are not covered; the report of every
  build lists them for each theorem.

- **The Lean compiler and the C compiler.** The theorems are about the Lean
  functions. The compiled program is trusted to do what they do.

  *What limits the trust:* For each of 3,095 lists of arguments, the tests of
  the whole program hold the function and the compiled program against the
  same expected answer; two more tests start the compiled program where it
  cannot write its answer.
  `check_app.py` compares the compiled code of Core with the model for
  1,234,594 questions, inside a second small program, and it starts the
  compiled program itself 22,186 times.

- **`Main.lean`, and that the compiled program answers every text as its
  function does.** The six lines of `Main.lean` hand the arguments to
  `VeriMol.run`, print the result and write out what is still waiting, so that
  a failure to write the answer is not lost. Nothing is proven about input and
  output. And `check_app.py` starts the compiled program for a sample only:
  starting it for every text takes hours.

  *What limits the trust:* The audit holds the six lines in place. It keeps a
  copy of the function `main` that the author has read; the file may declare
  `main` and nothing else; and the build stops unless that `main` is the copy,
  expression for expression (what Lean makes of the text is compared, so a
  comment may change), and is tied to no other code. What a person has to see
  in those lines: that `VeriMol.run` is asked about the arguments as they are;
  that the two texts of the answer are printed, each where it belongs and
  once, and nothing else is; and that the program ends with the exit code of
  the answer. The audit also keeps two lists of the names that `main` may
  mention, and they hold exactly what it mentions: of Core only `VeriMol.run`
  and what it returns, and beyond Core no `if`, no `match` and no comparison.
  So `main` treats every answer alike, and a mistake in it shows on every
  answer of a kind. Both programs hold the same compiled code of Core, and
  `check_app.py` looks at what the build handed over for the two.

- **`SPEC.md`.** It says what is right for this program. That this is what
  SMILES means is not proven.

  *What limits the trust:* It is tested against RDKit and Open Babel on the
  real texts (see "Tested").

- **The checkers: `Audit.lean`, `Tests.lean`, `lakefile.toml`, the second
  program `Answers.lean` and the Python scripts in `reference/`.** Nothing
  checks them. Nor does anything check Lake, Lean's build tool, which decides
  what is built again after a change.

  *What limits the trust:* The audit tests itself on one specimen of every
  violation it looks for. `lake test` holds the second program against the
  expected answers of its tests of the whole program. `check_corpus.py`,
  `check_stereo.py`, `check_canonical.py` and `check_direct.py` make wrong
  answers on purpose in every run and must notice them. `check_app.py` was
  tried on 17 mistakes that were put on purpose into the program, into
  `Main.lean` and into the second program, and reported each one; no file of
  this repository repeats that trial.

## How the claims are kept honest

The program and its proofs were written by an AI assistant, under nine rules
that the author set at the start. The comments in the code and the report of
the build cite the rules by their numbers, as "rule 9". They are not the
rules 1 to 10 by which `SPEC.md` reads a text, which the code cites with
their section.

1. The version of Lean is fixed in the file `lean-toolchain` and is never
   changed.
2. No Mathlib and no other dependencies.
3. All the logic is a library, `VeriMol.Core`, called Core here, of pure and
   total functions on simple data. The file `VeriMol/Core.lean` holds only
   import lines, and the logic stands in the files under `VeriMol/Core/`. No
   input or output, no `partial`, no `unsafe`, no `@[implemented_by]`, no
   `@[extern]`, no `sorry`, no `axiom`, and no operation that can panic.
4. The program, `Main.lean`, does only input and output and asks the library
   for every decision. On bad input it prints `error: ...` and ends with exit
   code 1.
5. The tests are one program, run by `lake test`, without a test framework: a
   test is a name, an actual value and an expected value, compared with `==`.
6. After every change the build and all the tests run, and every error and
   every warning is mended.
7. The author makes every commit to the main line of the project. The AI
   assistant makes none there.
8. The AI assistant explains every step to the author in plain words, with
   the real output of the commands that it names.
9. The theorems are a library, `VeriMol.Proofs`, called Proofs here, with no
   `axiom` and no `native_decide`; `VeriMol/Proofs.lean` holds only import
   lines. `sorry` is allowed only there, only for a theorem that is stated
   and not yet proven, and such theorems are listed. No statement of a
   theorem is changed or weakened without the author's approval. A theorem is
   called proven only when `#print axioms` shows no `sorryAx` and nothing
   beyond `propext`, `Classical.choice` and `Quot.sound`.

What holds the rules in place:

- **The ledger.** `Audit/Ledger.lean` lists every statement of the 49
  numbered theorems, with a fingerprint and whether it is proven or still
  open. The build stops when a line disagrees with the files under
  `VeriMol/Proofs/`, so a statement is not weakened unnoticed by accident
  (see "Trusted" for what a fingerprint covers, and what it does not).
- **The audit.** `Audit.lean` runs whenever the project is built after a
  change. It checks that Core contains no input or output, no unproven
  assumption and none of the escape hatches of Lean that it knows (`partial`,
  `unsafe`, `@[implemented_by]`, `@[extern]`, `@[init]`, `sorry`, axioms);
  that, of Lean's own library, Core mentions only what stands on a list; that
  the program adds no logic of its own; and that the ledger matches the files.
  It prints which theorems are proven and which are open. Apart from that
  list, which lets through only what stands on it, the audit can stop only the
  ways round the rules that are known. It is no proof that a file which was
  written to deceive would be caught: for that a person has to read what
  changes in the program.
- **The tests.** The expected result of a test never comes from the Lean
  program. It comes from the model, or it is worked out by hand (see "Tested",
  `lake test`).
