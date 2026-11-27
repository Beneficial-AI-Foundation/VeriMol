# VeriMol

> **Early research prototype, version 0.1.0.** One example filter with one
> example rule. Under no circumstances should it be relied upon to check
> safety-relevant features of chemical compounds.
> [`RISKS.md`](RISKS.md) says what is asked of users.

![Overview in four stages, from left to right: a chemical compound, from the real world or from a deep generative chemistry model; its machine-readable formats in cheminformatics, among them SMILES; the Lean 4 Mol object that VeriMol reads from the SMILES; and a vericoded, formally verified safety filter based on a safety rule proposed and formalised by a chemist. After the chemist states the rule, an AI writes the algorithmic checker and its proof that it truly checks the rule, and Lean checks the proof. The example rule built so far is "no long perfluorinated group". It is shown on the formula of PFOA (perfluorooctanoic acid): seven of its eight carbon atoms carry fluorine and no hydrogen and are bonded in one chain, and together they form a perfluorinated group of seven, which counts as long. Compounds with perfluorinated groups are PFAS (per- and polyfluoroalkyl substances), known as "forever chemicals" because they hardly break down; PFOA is a long-chain PFAS. A proposed compound is asked three questions (is it read into Lean as a Mol object, is the Mol sound, does the rule hold) before it is handed on to the lab, with the theorem that says so and two compounds: ibuprofen is handed on, and PFOA is refused. Under it stands the foundation: three statements that are proven about the reader and the writer. The figure shows the aim; what is built is one example filter with one example rule, in an early research prototype.](figures/verimol-overview.svg)

**Towards formally verified safety filters for AI-generated molecules.** Generative
chemistry models can propose new and potentially hazardous molecules that could be
(intentionally or unintentionally) misused. Before a proposed molecule is made in a lab,
a filter should check it against safety rules, and the filter should be formally proven to
do exactly what its rules say. VeriMol aims to be a framework for building such filters in
[Lean 4](https://lean-lang.org), a programming language in which theorems
about a program can be stated and proven, and the computer checks every
proof. The filters are to be built by *vericoding*
([Bursuc et al., 2025](https://arxiv.org/abs/2509.22908)): a chemist states a
safety rule as a short formal definition in Lean 4, an AI writes the program that
checks the rule together with a proof that the program indeed checks precisely
the formalised rule for all suitable input molecules, and Lean checks the proof.
"Formally verified" means proven to do what the rule says, for the
molecular graph that the program reads from its input. It does not mean
that the rule is the right one, or that the input compound is read as a chemist
would read it: that is tested, not proven. So far there is one implemented
example filter, based on one associated example rule.

**Why.** One of the key studies that motivate this project is recounted in
"The Dark Side", a book chapter on the dual-use implications of generative
drug discovery ([Ekins, 2024](https://doi.org/10.1201/9781003399346-13); see
also [Urbina et al., 2022](https://doi.org/10.1038/s42256-022-00465-9),
[free full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC9544280/)): what
serves the AI-assisted search for drugs can be turned to harm. Invited in 2021 to
present on the dual-use risks of AI, researchers in drug discovery showed
that their own computational tools could propose tens of thousands of
structural analogues of an extremely toxic synthetic nerve agent.

One possible response is a safety filter that screens the molecules a
generative model proposes. Such a filter can only be as good as (1) the
chemical safety rule it is based on and (2) the algorithmic checker that
decides whether the rule holds for a given molecule. VeriMol aims to provide
a framework that keeps the two apart. The rule is a short formal definition
that a chemist can read and argue with. The checker need not be taken on
trust: an AI writes it from the rule, together with a proof that it says yes
exactly when the rule holds, for every suitable input molecule, and Lean
checks that proof. What such a framework cannot give is a guarantee that the
rule is the right one, which is for chemists to decide, or any protection
against someone who does not run the filter at all. A verified filter is no
more than an auditable commitment by whoever designs and deploys it.

**Warning: not safe, early research prototype, work in progress** (version 0.1.0).
The foundations of this project have not yet settled into their final, scalable shape,
and the architecture as well as the low-level machinery have been coded hastily during
a two-week sprint to create a first blueprint. AI (under human guidance) was used heavily for coding and project scoping.
The general vision, architecture, and functionality of this project may still change substantially. Needless to say, this project
comes without any warranty. Under no circumstances should this project in its current
early form be relied upon to actually check safety-relevant features of chemical compounds.

## From a formal chemical safety rule to a verified filter

A filter is meant to be made and used in five steps; the first step, the stated
safety rule, is arguably the most important one. Whoever drafts it, a person who
knows the chemistry has to read it and answer for it: no formal proof can ever
stand behind that step.

1. **A chemist states a rule.** A rule is a safety-relevant property of the
   structure of a molecule, written as a short formal definition in Lean on
   a `Mol` object, the molecule as a labelled graph (its atoms, and the bonds between them).
   A rule has to be exact: a property that only a learned model can estimate, such as "is
   toxic", cannot be one.

   One example rule that is already built: the molecule has no
   perfluorinated group of `n` or more carbon atoms, for a number `n` that is
   given with the command. Such groups are associated
   with so-called "forever chemicals", because they hardly break down
   (["The example"](#the-example-filter-no-long-perfluorinated-group) says more). Kinds of rules that could
   follow, none of them built:
   - the molecule contains none of a list of substructures;
   - it belongs to none of the families that a regulation defines by a
     common core with variable parts;
   - it shares no substructure of more than *k* atoms with a compound on a
     list;
   - no compound on a list can be reached from it in at most *k* steps of a
     fixed list of transformations, so that a thin disguise of a listed
     compound does not pass.

   Three of those four work from a list, and a list of structures chosen
   because they are dangerous is not a thing to publish: read in one
   direction it is a filter, read in the other it is a map of what to try.
   The intended answer is to keep the list out of the program. The checker is
   public and proven for *every* list — a theorem of that shape carries no
   hazardous content — and the list itself is an input, supplied by whoever
   answers for it. [`RISKS.md`](RISKS.md) sets this out, and says what else
   does and does not belong in this repository.

2. **An AI writes the checker and its proof.** The checker is a program that
   answers yes or no for a suitable, valid `Mol`. The proof shows that it says yes exactly
   when the rule holds, for every `Mol` that the filter asks it about: no
   such `Mol` passes that breaks the rule, and none is turned away that
   satisfies it. Lean checks the proof, so nobody has to take the AI's word
   that its algorithmic checker follows the rule (as would be the case with vibecoded checkers).

3. **The rule is checked against what is known.** A proof cannot show that a
   rule says what was meant. But since the checker is proven to agree with
   the rule, its answer for a known compound is the rule's own answer: known
   compounds must get their known answers, and where one does not, the rule
   is changed and the proof is made again. The answer must not depend on how
   the atoms of a molecule are numbered either; for the rule that is built,
   that must be proven.

4. **The filter asks three questions of every proposal.** A proposal comes
   (currently) as a SMILES, although parsers for other machine-readable molecular formats (InChI, graphs, ...)
   can be added in the future.

   - Is the text read as a molecule (successfully parsed into Lean as a `Mol` object)?

   - Is the `Mol` sound? This is a basic check of chemical validity. The check
     is currently strict on purpose: it also refuses real compounds that are written
     with charges. However, passing this step is no proof that a compound can exist.

   - Does the `Mol` pass the formally verified, algorithmic rule-checker?

5. **The system around the filter acts on the answer.** A refused molecule
   can be withheld, flagged, not decrypted (if somehow encrypted), or
   never synthesised. This part is currently outside of VeriMol.

- **What stays trusted.** That the rule and "sound" say what is meant; that
  a `Mol` is what its SMILES means, which is tested against RDKit and Open
  Babel, two widely used cheminformatics toolkits, and not proven; Lean's
  kernel (the small program that checks the proofs) and compiler; the
  project's own audit, which checks that the program that runs is the one
  of the proofs (no missing proof, no added axiom, no other code put in its
  place, in the ways that it knows of), and which nothing checks; the six
  lines of `Main.lean` that do the input and output (see
  ["Trusted"](#empirically-tested-and-trusted)); and how whoever receives the `Mol` reads it.

- **What is never claimed.** That a molecule which passes is actually harmless.

**Why a proof, and not only tests.** Where molecules are generated faster
than people can look at them, the filter may be the only check. Proposals
are new by design, so many of them lie outside any list of tests. A model
that is trained or steered against a filter is rewarded for whatever the
filter lets through, so it can come to exploit a bug in the filter that
tests would rarely meet. (The same holds for whatever the rule itself lets
through: a proof removes the mistakes of the program, not the limits of the
rule.)

That argument is about what a filter should be, and not a description of what
has been done here. Nobody has yet gone looking for compounds that are as
harmful as the ones this rule is meant to catch and that slip past it. The
known ways past it were found by reading the rule, not by searching for them
([`SPEC.md`](SPEC.md), section 16).

## Try it

You need [elan](https://github.com/leanprover/elan), the installer of Lean 4;
it fetches the exact version, 4.36.0, that the file `lean-toolchain` names.
There are no other dependencies: no Mathlib and no other package. The
project was developed and tested on Linux, and not tried on macOS or
Windows: two of the tests start the program through a Unix shell (`sh`), and
one of them needs the device `/dev/full` and is left out where there is
none. The first `lake test` builds everything and takes a few minutes.

```
git clone https://github.com/Beneficial-AI-Foundation/VeriMol.git
cd VeriMol
lake test                                           # builds everything, checks every proof, runs every test
.lake/build/bin/app 'CC(=O)O'                       # reads acetic acid and prints its Mol
.lake/build/bin/app filter perfluoro 6 'CC(=O)O'    # asks the filter about acetic acid
```

For acetic acid the program prints four atoms and three bonds. The last two
lists hold stereo facts, which say how a molecule is arranged in space, and
are empty here:

```
{ atoms := [
    { element := .C, isotope := none, charge := 0, hydrogens := 3 },
    { element := .C, isotope := none, charge := 0, hydrogens := 0 },
    { element := .O, isotope := none, charge := 0, hydrogens := 0 },
    { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
  bonds := [
    { a := 0, b := 1, order := .single },
    { a := 1, b := 2, order := .double },
    { a := 1, b := 3, order := .single } ],
  orientations := [],
  geometries := [] }
```

The `filter perfluoro` command prints the same eleven lines for it: acetic
acid passes. The next section says what this example filter is actually
doing.

## The example filter: no long perfluorinated group

**What the rule is about.** PFAS, per- and polyfluoroalkyl substances, are
man-made compounds with carbon atoms on which fluorine stands in the place
of every hydrogen atom, and the bond between carbon and fluorine is
extremely strong ([Buck et al., 2011](https://doi.org/10.1002/ieam.258)).
There are thousands of them. They are known as "forever chemicals": most of
them do not break down, and many are found in the blood of people and
animals all over the world. Exposure to some of them may be linked to
harmful effects on health
([EPA](https://www.epa.gov/pfas/pfas-explained),
[ATSDR](https://www.atsdr.cdc.gov/pfas/about/index.html),
[EEA](https://www.eea.europa.eu/en/about/contact-us/faqs/what-are-pfas-and-how-are-they-dangerous-for-my-health)).
Among them, the acids with a long chain of such carbon atoms have been
shown to build up in living things more than their short-chain relatives
(Buck et al., 2011), and several of them are listed in the
[Stockholm Convention](https://www.pops.int/TheConvention/ThePOPs/AllPOPs/tabid/2509/Default.aspx)
on persistent organic pollutants. One example compound is perfluorooctanoic acid (PFOA).

PFOA has eight carbon atoms. Seven of them carry fluorine and no hydrogen,
and they are joined in one chain:

```
HOOC–CF2–CF2–CF2–CF2–CF2–CF2–CF3
     └──── a group of seven ───┘
```

That chain is a *perfluorinated group*, and with seven carbon atoms it is a
long one. To filter out compounds such as PFOA we strive for a chemical rule that states:

> The `Mol` has no perfluorinated group of `n` or more carbon atoms.

- A *fluorinated carbon atom* is a carbon atom with four bonds, none of them a
  double, triple or quadruple bond, at least one of them to fluorine, and with
  no hydrogen on it; what else it is bonded to is not looked at.

- A *branch carbon atom* is such an atom that need not carry fluorine: however,
  at least three of its four bonds must go to carbon atoms that already belong
  to a group.

- A *perfluorinated group* is made of these two kinds of atoms where they are
  joined through the bonds between them, as a chain, branched, or in a ring.
  The number `n` is given with the command.

The rule was chosen as an example because its pattern is public knowledge,
and because it cannot be checked by looking at one atom at a time: it needs
a search through the molecule.

**Sound** is a simple proxy for chemical validity of a compound, and asked before every rule.
Every atom has to pass five tests:

- its element is one of B, C, N, O, P, S, F, Cl, Br and I;
- it has no mass number;
- it has no charge;
- it has no aromatic bond, or at least two;
- its bonds and hydrogens add up to a usual valence of its element (or to
  one below it, for an atom with aromatic bonds).

The chemical soundness check is still very fallible and incomplete, and must
be improved further in the future. Currently, it is little more than a
placeholder.

```
$ .lake/build/bin/app filter perfluoro 6 'CC(C)Cc1ccc(cc1)C(C)C(=O)O' > /dev/null; echo $?
0
$ .lake/build/bin/app filter perfluoro 6 'OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F'
error: the Mol has a perfluorinated group of size 7, and size 6 or more is refused
$ .lake/build/bin/app filter perfluoro 6 'C[N+](=O)[O-]'
error: the Mol is not sound: atom 1 has a charge
```

Ibuprofen is handed on, with exit code 0 (its `Mol` is sent to `/dev/null`
here). PFOA is refused by the rule. Nitromethane, written with charges, is
not sound and does not even get to the rule checker.

**What is proven** (theorems 46 to 49 of [`CLAIMS.md`](CLAIMS.md)): the
checker of soundness says yes exactly when the `Mol` is sound
(`VeriMol.Mol.isSound_iff`); the search behind the rule returns exactly the
atoms of a perfluorinated group (`VeriMol.Mol.mem_fluoroGroupOf`), and the
checker built on it says yes exactly when the rule holds, for every `Mol`
and every `n` (`VeriMol.Mol.hasNoFluoroGroup_iff`); and so, for the filter:

```lean
theorem filterPerfluoro_eq_ok_iff (n : Nat) (text : List Char) (m : Mol) :
    filterPerfluoro n text = .ok m ↔ read text = .ok m ∧ m.Sound ∧ m.NoFluoroGroup n
```

In words: the filter hands on a `Mol` exactly when the SMILES is read as
that `Mol`, the `Mol` is sound, and the rule holds for it. Both definitions
also give the same answer for every numbering of the atoms of a molecule.
They stand in [`VeriMol/Proofs/Predicates/`](VeriMol/Proofs/Predicates/), in
two short files that are written to be read.

**Checked against what is known** (step 3 above). Five known PFAS and
ibuprofen get their known answers, each as one theorem in
[`VeriMol/Proofs/Compounds.lean`](VeriMol/Proofs/Compounds.lean): Lean's
kernel, the small program that has the last word on every proof, runs the
reader and the two proven checkers.

| Compound | Proven |
|---|---|
| PFOA, perfluorooctanoic acid | sound; its largest perfluorinated group has exactly 7 carbon atoms |
| PFHxS, perfluorohexanesulfonic acid | sound; exactly 6 |
| PFHxA, perfluorohexanoic acid | sound; exactly 5 |
| an isomer of PFOA with a branch | sound; exactly 7, although no chain in it has more than 6 |
| an isomer of PFOA whose branch point carries no fluorine | sound; exactly 7: the atom at the branch is a branch carbon atom |
| ibuprofen | sound; no perfluorinated group at all |

Each is about one text. The same compound written another way — with
charges, or with a hydrogen as an atom of its own — is another `Mol`, and
nothing is proven about it.

These six theorems are proven, but they are not among the 97 statements
below, whose wording the project guards against an unnoticed change
([`CLAIMS.md`](CLAIMS.md), "Known compounds"). The filter was also compared
with RDKit, which was asked for the same pattern written a second time: that
holds two searches against each other, and says nothing about whether the
rule is the right one ([`CLAIMS.md`](CLAIMS.md), under "Tested", has the
numbers).

**What the filter does not say.**

- **That a compound which passes is harmless.** The rule names one pattern
  of a structural formula. A PFAS with short groups only passes: when
  groups of six or more carbon atoms are refused (`filter perfluoro 6`),
  PFHxA does, because its largest group has five.
- **That the rule is the right one.** It is a reading, and not the rule of a
  law or of a standard, and no number `n` would make it one: the usual
  wording for long-chain PFAS sets one threshold for sulfonates and another
  for carboxylic acids, where the rule has a single number for every
  compound. With 7 the filter hands on perfluorohexanesulfonic acid, which
  that wording counts as long-chain, and with 6 it refuses
  perfluoroheptanoic acid, which that wording does not.
  An oxygen atom between two groups parts them, so a
  perfluoroether acid can pass however many fluorinated carbon atoms it
  has. One fluorine atom on a carbon atom without hydrogen is enough, also
  where nothing is perfluorinated. And chlorine, bromine and iodine on a
  carbon atom are not looked at, so a chain of a chlorofluorocarbon is
  counted as a perfluorinated group; the definition of PFAS that the OECD
  recommended in 2021 reads such an atom the other way
  ([`VeriMol/Proofs/Predicates/FluoroGroup.lean`](VeriMol/Proofs/Predicates/FluoroGroup.lean),
  the file of the rule, has the reference). [`SPEC.md`](SPEC.md), section 16,
  has the examples and the full list.
- **That "sound" is the right test.** It is narrow on purpose: of the
  62,075 real SMILES that the program reads, the filter refuses 9,542 as
  not sound, most of them for a charge. With the number 6 the proven rule
  refuses 34. So almost every refusal comes from "sound", the part that is
  called a placeholder above, and not from the part that is proven. A
  filter whose work is done by its weakest test is not a filter to rely on,
  which is the point of the warning at the top.
- **What is made of the `Mol` afterwards, and how it is read by a human.**
  A printed `Mol` that passed looks like any other printed `Mol`:
  only the exit code says that it passed.

## The foundation: molecules as Lean objects

A rule is asked of a `Mol`. So every answer of a filter rests on that
object, and on the reader that makes it from a
[SMILES](https://github.com/opensmiles/OpenSMILES), a widely used text
notation for molecules. The writer and the
canonical SMILES belong to the same foundation; the filter uses neither.

Three runs of the program on pent-3-en-2-ol, a small alcohol whose SMILES
needs both kinds of stereo marks: `/` at its double bond, and `@@` at the
carbon atom that carries the OH group.

```
$ .lake/build/bin/app 'C/C=C/[C@@H](C)O'
{ atoms := [
    { element := .C, isotope := none, charge := 0, hydrogens := 3 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .C, isotope := none, charge := 0, hydrogens := 3 },
    { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
  bonds := [
    { a := 0, b := 1, order := .single },
    { a := 1, b := 2, order := .double },
    { a := 2, b := 3, order := .single },
    { a := 3, b := 4, order := .single },
    { a := 3, b := 5, order := .single } ],
  orientations := [
    { atom := 3, orientation := .anticlockwise } ],
  geometries := [
    { a := 1, b := 2, geometry := .oppositeSides } ] }
$ .lake/build/bin/app 'C/C=C/[C@@H(C)O'
error: position 6: '[' is never closed
$ .lake/build/bin/app canonical '[OH][C@H]([CH3])/[CH]=[CH]/[CH3]'
C/C=C/[C@@H](C)O
```

- **Reading.** The first answer is the molecule as a `Mol`: six atoms,
  numbered from 0 in the order of the SMILES, each with its count of
  hydrogens, and five bonds. The last two lists hold what the stereo marks
  say, as facts about the numbered atoms: atom 3 has an orientation, and the
  double bond between atoms 1 and 2 has its neighbours on opposite sides
  (trans). The SMILES says `@@` (clockwise) and the `Mol` says
  `.anticlockwise`: both mean the same arrangement in space, each said for
  its own order of the four things around atom 3 (`SPEC.md`, section 12).
- **An error.** The second input is the first one without its `]`. The
  program names the first problem and its position, counted from 0.
- **`canonical`.** The third input is the same molecule written another way,
  starting from the oxygen. `canonical` puts the atoms into an order that
  depends on the molecule and not on how its atoms were numbered. That is
  proven, wherever `canonical` gives a SMILES.

All the logic is a library, `VeriMol.Core`, of pure and total functions on
simple data; a small command-line program, `app`, does the input and output
around it.

| Command | What it prints |
|---|---|
| `app '<SMILES>'` | the `Mol`, as a Lean object, or one line that says what is wrong with the input and where |
| `app rewrite '<SMILES>'` | the `Mol` written back as a SMILES, in the usual spelling (a *spelling* is one way of writing a `Mol` as a SMILES), or an error where the writer refuses it |
| `app plain '<SMILES>'` | the same in a plain spelling, made for the proofs: no round brackets, every atom in square brackets, every bond written out (`CC(=O)O` becomes `[CH3]-[C]-1=[O].[OH]1`) |
| `app canonical '<SMILES>'` | a canonical SMILES of the molecule: the same one whatever the order of its atoms, and for the order of the atoms only (`c1ccccc1` and `C1=CC=CC=C1` get two); or an error where it gives none |
| `app filter perfluoro 6 '<SMILES>'` | the `Mol`, if it is sound and has no perfluorinated group of 6 or more carbon atoms (any number from 1 on may stand in the place of 6); otherwise the reason why it is refused |

Three ideas that the rest leans on:

- **Stereo facts.** A stereo mark means something only together with the
  order in which a SMILES writes the atoms. So a `Mol` stores the fact
  instead: which atoms have an orientation (chirality), and which double
  bonds have a geometry (cis or trans).
- **The same molecule.** The reader numbers the atoms in the order of the
  SMILES, so `CCO` and `OCC`, both ethanol, are read as two different
  `Mol`s. Two `Mol`s are *the same molecule* when the atoms of one can be
  given new numbers so that the other comes out: they are isomorphic as
  labelled graphs, stereo included.
- **Well formed.** A `Mol` is *well formed* when each bond joins two
  different atoms that exist, no pair twice; its stereo facts stand at atoms
  and bonds that can have them; and the bonds and the stereo facts are
  listed in one fixed order (`SPEC.md`, section 3).

To use it from Lean, put the lines below into a new file in the folder of the
repository, say `Try.lean`, and run `lake env lean Try.lean`. `import VeriMol`
brings the logic with its theorems, `import VeriMol.Core` the logic alone. A
text enters the library as a list of characters (`.toList` makes one from a
`String`):

```lean
import VeriMol

#eval VeriMol.read "CCO".toList      -- prints the Mol of ethanol

example : VeriMol.read "CC".toList = .ok
    { atoms := [ { element := .C, isotope := none, charge := 0, hydrogens := 3 },
                 { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
      bonds := [ { a := 0, b := 1, order := .single } ] } := rfl

#check @VeriMol.read_write                         -- the round trip, as a theorem
#check @VeriMol.filterPerfluoro_eq_ok_iff          -- the theorem of the filter
#print axioms VeriMol.filterPerfluoro_eq_ok_iff    -- what its proof rests on
```

## Key proven theorems

97 statements are proven, and [`CLAIMS.md`](CLAIMS.md) groups them into 49
numbered theorems. Lean's kernel checks them whenever the project is built,
and `lake test` runs it over the compiled files a second time. The build
reports for each of them that it rests on no `sorry` (Lean's word for a
missing proof) and on no axiom beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`). 15 of the statements are about the
filter, and its section above names the main ones; the other 82 are about
the foundation, and about the program as a whole. 24 of these are single
examples, such as what `CC(=O)O` is read as. The key theorems of the
foundation:

| In plain words | In Lean |
|---|---|
| **Round trip (`Mol` → SMILES → `Mol`).** If the writer gives a SMILES for a `Mol`, in either spelling, the reader turns that SMILES back into exactly that `Mol`, stereo facts included. | `VeriMol.read_write`, `VeriMol.read_writePlain` |
| **Bijection (molecules ↔ canonical SMILES).** A canonical SMILES is a unique name for a molecule. Here, a *molecule* is an equivalence class of isomorphic, well-formed `Mol` graphs. Two things to know (see ["Limits"](#limits)): not every molecule has a canonical SMILES, and one compound can be several molecules in this sense. | `VeriMol.Molecule.canonicalText_eq_some_iff` |
| If `canonical` prints a SMILES for one input, it prints that same SMILES for a second input exactly when the two inputs are read as the same molecule. | `VeriMol.run_canonical_eq_iff` |
| Every `Mol` that the reader returns is well formed. | `VeriMol.read_wellFormed` |
| Rewriting never changes what a SMILES says: if `rewrite` or `plain` prints a SMILES, that SMILES is read as the same `Mol` as the original. | `VeriMol.run_rewrite_same_mol` |
| Whatever its arguments, `VeriMol.run`, the whole program as one function, either succeeds or reports an error in one fixed form. | `VeriMol.run_succeeds_or_reports_error` |

The round trip, as Lean states it:

```lean
theorem read_write (mol : Mol) (text : List Char) (h : write mol = .ok text) :
    read text = .ok mol
```

## Empirically tested and trusted

**Tested against RDKit and Open Babel.** `VeriMol.run`, the function that is
the whole program, was run on 62,099 real SMILES from seven public
collections of molecules, and its answers were compared with two widely used
cheminformatics toolkits that are independent of this project:
[RDKit](https://www.rdkit.org), version 2024.03.3, and
[Open Babel](https://openbabel.org), version 3.1.1. It reads 62,075 of the
SMILES; the other 24, which RDKit reads, use notation that the program
leaves out (see ["Limits"](#limits)).

- **Reading.** RDKit, with its sanitization off (`sanitize=False`) so that
  it reports what is written, reads 62,070 of the 62,075 as exactly the
  atoms and bonds of the program's `Mol`. The other 5 differ only in the
  hydrogens of one to four atoms: nitrogens whose bonds add up to four and
  iodines with two bonds (`SPEC.md`, section 11.2). Open Babel reads the
  same atoms and bonds in all 62,075, except that in 7,336 it calls other
  bonds aromatic, by rules of its own.
- **Writing.** RDKit reads every SMILES that `rewrite` and `plain` write as
  exactly the atoms and bonds that the program read from the original, and
  Open Babel reads each as it reads the original. RDKit also takes every
  canonical SMILES for the same atoms and bonds as the rewritten one, in
  whatever order.
- **Stereo.** For the 4,528 SMILES with stereo marks, RDKit, now with its
  sanitization on as in normal use, was asked whether the original and the
  written SMILES are the same molecule, stereo included. It never found
  another arrangement in space:

| Of the 62,075 SMILES that are read | `rewrite` | `plain` | `canonical` |
|---|---|---|---|
| a SMILES is written | 62,075 | 62,069 | 62,073 |
| of the 4,528 with stereo marks: the same molecule to RDKit, stereo included | 4,517 | 4,511 | 4,515 |
| of the 4,528: no verdict, because RDKit's sanitization does not accept one of the two | 11 | 11 | 11 |
| of the 4,528: nothing is written | 0 | 6 | 2 |

**Trusted.** The proofs say that the program does what its definitions say.
What they do not cover has to be trusted:

- **That the definitions say what was meant.** A proof shows that a
  statement holds, not that it is the right statement. So the statements of
  the theorems, and with them the rule of the filter and the definition of
  "sound", have to be read by a person: a checker can be proven right for a
  rule that is not the one that was meant.
- **That a `Mol` is what its SMILES means.** No theorem says that the `Mol`
  which the reader gives is the molecule that a chemist sees in the SMILES.
  A proof needs something exact to be held against, and SMILES is defined
  by a document in prose, the OpenSMILES specification, and in practice by
  the programs that read it. The project's own exact account of the
  notation is [`SPEC.md`](SPEC.md), written from that specification.
  Whether the program reads a SMILES as other programs do is therefore
  tested, not proven: it is the comparison with RDKit and Open Babel above,
  on 62,099 real SMILES.
- **Lean itself.** Its kernel, the small program that checks the proofs,
  and the compilers that turn the proven functions into the program that
  runs.
- **The six lines of input and output** (`Main.lean`). The theorems reach
  as far as `VeriMol.run`, the function that is the whole program. The six
  lines around it hand it the arguments and print its answer, and nothing
  is proven about them.
- **The project's own checking tools:** the audit, which stops the build
  when, for example, a proof is missing or an axiom was added; the test
  program; and the Python scripts that make the comparisons above. Nothing
  checks them.

[`CLAIMS.md`](CLAIMS.md) says for each of these what limits the trust, and
has the rest in full: every theorem with its name, what the theorems do not
say, and every check with its numbers.

## Limits

- **Hardly any chemistry yet.** The reader checks no valences and works out
  no aromaticity, and `canonical` is canonical for the order of the atoms
  only: `c1ccccc1` and `C1=CC=CC=C1` get two canonical SMILES, and so do
  `C` and `[H]C([H])([H])[H]`. Only the filter asks more, with "sound".
- **One filter, with one narrow rule** (see "What the filter does not say",
  above).
- **SMILES only, and not all of it.** Left out on purpose: the wildcard atom
  (`*`), atom classes (`[CH3:1]`), the rarer stereo marks (such as `@TH1`),
  and two ways of writing `@` at an atom with a lone pair that RDKit and
  Open Babel read as mirror images of each other (`SPEC.md`, sections 11.2
  and 12.4).
- **Not every `Mol` gets a SMILES.** The writer refuses some, such as a
  `Mol` that needs more than 99 ring numbers at the same time, and a few
  with stereo facts. `canonical` also refuses more than 1,000 atoms and
  gives up where very many numberings look alike, though for none of the
  real SMILES (`SPEC.md`, sections 3.2, 9.4 and 12.3).
- **Written for proofs, not for speed.** The logic uses lists and structural
  recursion: `canonical` took 20 seconds for a chain of 800 carbon atoms
  (`SPEC.md`, section 3.2). The program takes one SMILES at a time.

## Layout

| Piece | Files | Purpose |
|---|---|---|
| `VeriMol.Core` | `VeriMol/Core/` | all the logic, as pure functions that only compute and neither read nor print: the reader, the writer, the canonical form, the two checkers and the filter |
| `VeriMol.Proofs` | `VeriMol/Proofs/` | the theorems about `VeriMol.Core`. `Predicates/` has the definition of "sound" and the rule of the filter, and `Compounds.lean` the known compounds |
| `app` | `Main.lean` | the program: input and output only |
| `tests` | `Tests.lean`, `TestData.lean` | the tests, run by `lake test`; a script writes the expected results into `TestData.lean` |
| `Audit` | `Audit.lean`, `Audit/Ledger.lean` | the audit, which checks, whenever the project is built after a change, those rules of the project that a machine can check; and the ledger, its list of the 97 statements, each with a fingerprint |
| `answers` | `Answers.lean` | a second small program, for the checks only |
| `reference` | `reference/` | not part of the program: the specification as a Python model, and the checks against it, against RDKit and against Open Babel |

| Document | What it says |
|---|---|
| [`SPEC.md`](SPEC.md) | what the program does and does not do, exactly |
| [`CLAIMS.md`](CLAIMS.md) | what is proven, what is tested and what is trusted, in full |
| [`RISKS.md`](RISKS.md) | the risks of the project and of filters in general, the line of its scope, what is asked of contributors and users, and what to watch for when wiring the filter into something |
| [`SECURITY.md`](SECURITY.md) | how to report a way past a filter, or a hole in the audit, privately |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | the two things to know before opening an issue or a pull request, and what `lake test` must say |
| [`reference/README.md`](reference/README.md) | what the program is checked against, and how to run those checks (they need Python; the Lean program does not) |

These three documents call a SMILES a *text*: they also have to speak of
inputs that are not SMILES.

## How it was made

**Author: Markus Dablander, in interaction with
[Claude Code](https://claude.com/claude-code).** The author chose the goal,
set the rules that the AI worked under, decided which high-level theorems
had to hold, shaped and approved the key formal statements, and approved the
key steps. Claude Code, Anthropic's AI coding assistant, drafted those
statements in Lean and wrote the Lean code, the proofs, the Python tools and
most of the documentation, step by step and under those rules. So the project is
also, in part, an experiment in vericoding.

Four safeguards ([`CLAIMS.md`](CLAIMS.md) has the details):

- **Model.** The Lean program is tested, answer for answer, against a
  Python model of the specification. The same AI wrote both, so the
  independent checks are those against RDKit and Open Babel.
- **Ledger.** A fingerprint fixes the statement of every numbered theorem:
  an accidental change breaks the build.
- **Audit.** Every build checks that the logic only computes: it reads and
  prints nothing, and it uses no `sorry`, no axiom, and no `partial`,
  `unsafe`, `@[implemented_by]` or `@[extern]`. Reading and printing is
  left to `Main.lean`, which must match a copy that the author has read.
- **Tests.** No expected result comes from the Lean program itself.

## Related work

This project is not the first to bring SMILES into Lean, and it does not
claim to be.

- **[LeanSMILES](https://github.com/ATOMSLab/LeanSMILES)**, from the ATOMS Lab
  at UMBC, was public several weeks before this project began. To the best of
  the author's knowledge, the credit for first bringing SMILES as molecular
  graphs into Lean 4 belongs to its authors. Its README (as of November 2026)
  describes a formalisation of molecular representations in Lean, built on
  Mathlib, that goes much further into chemistry than this project currently
  does. The two overlap in the reader, the writer and the canonical SMILES,
  and LeanSMILES has theorems of its own about its canonical SMILES. This
  repository was developed independently: its author learned of LeanSMILES
  only when the reader, the writer and most of the proofs about them were
  written. What exists here is the much smaller project of the two, and its
  subject is narrow for now: reading and writing SMILES, proofs about both,
  and one filter with one rule. The author hopes that the two projects can
  be of use to each other.
- **[MolLean](https://arxiv.org/abs/2610.20459)** (a preprint of October
  2026) is a Lean-based language for checking the steps of chemical reasoning
  by language models.
- **[stereolib](https://github.com/graviterra/stereolib)** is machine-checked
  stereochemistry in Lean 4.
- **Vericoding.**
  [Bursuc et al. (2025)](https://arxiv.org/abs/2509.22908) present a
  benchmark for vericoding, the "LLM-generation of formally verified code
  from formal specifications", with specifications in Dafny, Verus and Lean.
- **Provably safe AI systems.**
  [Tegmark and Omohundro (2023)](https://arxiv.org/abs/2309.01933) argue for
  AI systems that provably satisfy requirements that people have specified,
  and [Dalrymple et al. (2024)](https://arxiv.org/abs/2405.06624) for AI
  systems with high-assurance safety guarantees. A filter with a proven
  check could be seen as a very small step in that direction.

## Acknowledgements

The author thanks the
[Beneficial AI Foundation](https://www.beneficialaifoundation.org), the
author's organisation, for supporting this project.

The project rests on the work of others, with thanks to all of them:

- [Lean 4](https://lean-lang.org)
  ([de Moura and Ullrich, 2021](https://doi.org/10.1007/978-3-030-79876-5_37));
- SMILES itself ([Weininger, 1988](https://doi.org/10.1021/ci00057a005)) and
  the [OpenSMILES specification](https://github.com/opensmiles/OpenSMILES),
  version 1.0, from which `SPEC.md` was written;
- [RDKit](https://www.rdkit.org) and [Open Babel](https://openbabel.org)
  ([O'Boyle et al., 2011](https://doi.org/10.1186/1758-2946-3-33)), against
  which the program is checked, and
  [`partialsmiles`](https://github.com/baoilleach/partialsmiles), a strict
  reader of SMILES, which the checks ask whether a SMILES is grammatical;
- the public collections of molecules that the checks run on: compounds of
  the NCI Open Database, as RDKit ships them, and six data sets of
  MoleculeNet ([Wu et al., 2018](https://doi.org/10.1039/C7SC02664A)), as
  the DeepChem project hosts them.

Their files are not copied into this repository: `reference/fetch.py`
fetches them, and [`NOTICE`](NOTICE) names the one small exception. Where
this project reads a SMILES differently from one of these programs,
`SPEC.md` says so as a difference between two readings, not as a fault of
theirs.

## Licence and citation

Copyright 2026 Markus Dablander. Licensed under the Apache License, Version
2.0: see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The scripts under
`reference/` are not needed to build or to use the Lean program. They may,
at your option, be used under the MIT License instead
([`reference/LICENSE-MIT`](reference/LICENSE-MIT));
[`reference/README.md`](reference/README.md) says why.

To cite the project, use [`CITATION.cff`](CITATION.cff), or "Cite this
repository" on the GitHub page. Questions, corrections and reports of
mistakes are welcome as issues on GitHub — with one exception: a way past a
filter, or a hole in the audit, goes to the private channel of
[`SECURITY.md`](SECURITY.md) first. [`CONTRIBUTING.md`](CONTRIBUTING.md) is
the short version of what to know before opening either an issue or a pull
request. Before citing the project anywhere,
please read ["What is asked of users"](RISKS.md#what-is-asked-of-users) in
[`RISKS.md`](RISKS.md): this is a prototype, and it must not be cited as
assurance that anything has been screened.
