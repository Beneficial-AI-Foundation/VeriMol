# SPEC: what the program does

**Status:** approved by the author. This document is changed only with the
author's approval.

## 1. The program in short

The program reads a SMILES text and turns it into a `Mol`: a labelled molecular
graph that is an ordinary Lean object. It can also write a `Mol` back as SMILES
text.

Reading records what the text says and nothing more: its atoms, with what is
written about each of them, its bonds, and how the molecule is arranged in
space where the text says that with the marks `@`, `@@`, `/` and `\`. It does
not judge whether the molecule makes chemical sense, and it does not repair
anything. Those belong to later work (section 13).

One command does judge. The command `filter` reads a text and hands the `Mol`
on only if it is sound, which asks a usual valence of every atom, and if a
rule holds for it; one rule is built, about perfluorinated groups (section
16). The reader behind it is the same reader, and it still reads what it is
given.

Two texts can be the same molecule with its atoms written in another order.
The command `canonical` writes one chosen text for all of them, except where
the molecule has more than 1,000 atoms, its search gives up or the writer
refuses that text (sections 3.1, 3.2 and 8). It goes no further than that:
`c1ccccc1` and `C1=CC=CC=C1` keep two chosen texts.

The program is meant to read everything in SMILES except the wildcard atom,
atom classes and the rarer stereo marks, and apart from the other points that
section 4.1 lists. Of the stereo marks it reads `@`, `@@`, `/` and `\`.
Sections 4 to 9 describe a text without these four marks first. Section 12
adds them: what they say, how they are read and how they are written.

The reference for the notation is the OpenSMILES specification
(<https://github.com/opensmiles/OpenSMILES>), version 1.0, as its repository
had it on 2 April 2026. Section 4.1 lists the points in which this document
differs from it, and what this document decides where that one leaves a point
open or can be read in two ways.

What is proven about the program, and how it is tested, stands in
`CLAIMS.md` (section 10). Where this document names a theorem by its number,
it is the theorem of that number in the tables under "Proven" there. A
helper lemma is proven as well, and has no number.

## 2. Words used here

| Word | Meaning |
|---|---|
| bare atom | an atom written without square brackets: `C`, `Cl`, `c`. OpenSMILES calls it an atom of the organic subset. |
| bracket atom | an atom written in square brackets: `[NH4+]`, `[13CH4]` |
| lowercase atom | an atom written with a lowercase symbol: `c`, `[nH]`. SMILES writes the atoms of aromatic rings so, and OpenSMILES calls the symbol an aromatic symbol. |
| bond symbol | one of `-` `=` `#` `$` `:` (single, double, triple, quadruple, aromatic) |
| ring number | a digit, or `%` and two digits, written after an atom. The same number after two atoms joins them with a bond. OpenSMILES calls it a ring-closure number. |
| branch | a part of the text in round brackets |
| digit | one of `0` to `9` |
| position | the place of a character in the text, counted from 0 |
| white space | a space, a tab or a line break (line feed, carriage return) |
| chosen form | of all the ways to number the atoms of a molecule, the one that the program picks (section 3.2). The usual term is canonical form, and the text that `canonical` prints is a canonical SMILES, for the order of the atoms only. |
| free place | the fourth place around an atom with three neighbours and no hydrogen of its own, which a lone pair fills (section 12.1) |
| clean-up | RDKit's sanitization, which `sanitize=False` switches off. With its clean-up off, RDKit reports what a text says. |
| sound | of a `Mol`: well formed, with every atom an uncharged atom without a mass number, of an element that may be a bare atom, with no aromatic bond or at least two, whose bonds and hydrogens add up to a usual valence, or to one below it for an atom with aromatic bonds (section 16.2). The filter asks its rule of a sound `Mol` only. |
| fluorinated carbon atom | a carbon atom with four bonds, none of them a double, triple or quadruple bond, at least one of them to a fluorine atom, and with no hydrogen on it (section 16.3) |
| branch carbon atom | a carbon atom with four bonds, none of them a double, triple or quadruple bond, with no hydrogen on it, at least three of whose bonds go to carbon atoms of a perfluorinated group; it need not carry fluorine (section 16.3) |
| perfluorinated group | fluorinated carbon atoms and branch carbon atoms that hang together through the bonds between them (section 16.3) |

## 3. The `Mol`

```lean
inductive Element where
  | H | He | Li | ... | Og          -- all 118 elements, listed in section 15

inductive BondOrder where
  | single | double | triple | quadruple | aromatic

structure Atom where
  element   : Element
  isotope   : Option Nat
  charge    : Int
  hydrogens : Nat

structure Bond where
  a     : Nat
  b     : Nat
  order : BondOrder

inductive Orientation where
  | anticlockwise | clockwise

inductive Geometry where
  | sameSide | oppositeSides

structure AtomOrientation where
  atom        : Nat
  orientation : Orientation

structure BondGeometry where
  a        : Nat
  b        : Nat
  geometry : Geometry

structure Mol where
  atoms        : List Atom
  bonds        : List Bond
  orientations : List AtomOrientation := []
  geometries   : List BondGeometry := []
```

| Field | Meaning |
|---|---|
| `atoms` | the atoms. Atom number `i` is the entry at place `i`, counted from 0. |
| `element` | which element the atom is |
| `isotope` | the mass number if one was written, otherwise `none`. `some 0` and `none` are different. |
| `charge` | the charge, 0 if none was written |
| `hydrogens` | how many hydrogens are attached to the atom without being atoms of their own |
| `bonds` | the bonds |
| `a`, `b` | the numbers of the two atoms the bond joins, the smaller one first |
| `order` | the kind of bond |
| `orientations` | the atoms that have an orientation in space, each with one mark (section 12.1). Empty unless given. |
| `geometries` | the double bonds that have a geometry, each with its two atoms and one mark (section 12.1). Empty unless given. |

The two lists of **stereo facts** stand beside the atoms and the bonds, and
not in them. An `Atom` and a `Bond` are meant to be what any notation for
molecules gives, with or without an arrangement in space. A `Mol` that is
written with `atoms` and `bonds` alone has no stereo facts. Section 12.1 says
what the marks in the two lists mean.

A `Mol` stores facts, not spelling. `C`, `[CH4]` and `[CH4+0]` give the same
`Mol`. So do `C1CC1` and `C2CC2`, `[Fe+2]` and `[Fe++]`, and `CC` and `C-C`:
which ring number is used, how a charge is written, and whether a bond symbol
is written out where a missing symbol means the same bond (section 5, rule
5), are spelling. The case of a symbol is not stored either. It is more than
spelling, though: `c` and `C` give different `Mol`s. What a lowercase symbol
says about the molecule is stored where it shows, in the hydrogens of the
atom and in the order of its bonds (section 5, rules 5 and 7). So a `Mol`
does not say that an atom is aromatic. It says which bonds are aromatic, and
that means: written as aromatic, with no place fixed for single and double
bonds.

A hydrogen that is written as an atom of its own, `[H]`, is an atom like any
other: heavy water, `[2H]O[2H]`, has three atoms. One `Mol` can hold several
separate pieces, as in `[Na+].[Cl-]`.

**The limits of a `Mol`, on purpose.**

- It does not give one molecule one form. The same molecule with its atoms
  numbered differently is a different `Mol` (below). So is the same ring with
  aromatic bonds and with single and double bonds in turn, `c1ccccc1` and
  `C1=CC=CC=C1`. So is the same hydrogen as a count and as an atom of its own,
  `C` and `[H]C([H])([H])[H]`.
- A mass number is stored as the number that is written, whether or not an
  atom of that mass exists: `[0C]`, `[1C]`.
- Unpaired electrons are not stored. They show only as a missing hydrogen:
  `[CH3]` is a carbon atom with three hydrogens.
- A bond has no direction. Where one atom gives both electrons of a bond, as
  to a metal, the bond is a bond like any other, and the spelling that some
  programs have for it is not read (`N->[Fe]`).
- Every atom is an atom of an element. The wildcard `*`, which stands for any
  atom or for an open end, is not read.
- Of the arrangement in space, a `Mol` holds what the marks `@`, `@@`, `/` and
  `\` can say, and it holds it as the text says it: also where a mark tells
  nothing apart, as in `Br[C@H](Br)C` (section 12.4).

Two `Mol`s are equal when they have the same atoms in the same order, the
same bonds in the same order and the same two lists of stereo facts. In a
well formed `Mol` (below) the order of the bonds and of the stereo facts is
fixed, so for two well formed `Mol`s the same atoms in the same order, the
same bonds and the same stereo facts are enough (theorem 22). The same
molecule with its atoms numbered differently is a different `Mol`.

The atom numbers are needed because a bond has to say which two atoms it
joins. Cyclohexane and two molecules of cyclopropane both consist of six
carbon atoms with two hydrogens each and six single bonds; only the atom
numbers in the bonds tell them apart. Whether two `Mol`s are the same molecule
with different atom numbers is a separate question. Section 3.1 says what it
means, and section 3.2 how the program answers it.

A `Mol` is **well formed** when all of these hold:

1. Every bond joins two different atoms that exist: `a < b`, and `b` is less
   than the number of atoms.
2. The bonds are listed in increasing order, by `a` first and then by `b`, with
   no pair of atoms twice.
3. The atoms with an orientation are listed in increasing order, no atom
   twice.
4. Each of them has four places (section 12.1): four neighbours and no
   hydrogen of its own, or three neighbours and at most one hydrogen of its
   own.
5. The double bonds with a geometry are listed in the order of the bonds, no
   bond twice.
6. Each of them is a double bond of the `Mol`, and each of its two atoms has
   one or two neighbours other than the partner.

A `Mol` without stereo facts is well formed when the first two hold.

```lean
-- The atoms that atom number `atom` is bonded to.
def Mol.neighbours (m : Mol) (atom : Nat) : List Nat :=
  m.bonds.filterMap fun bond =>
    if bond.b = atom then some bond.a else if bond.a = atom then some bond.b else none

-- The neighbours of `atom` other than `partner`.
def Mol.otherNeighbours (m : Mol) (atom partner : Nat) : List Nat :=
  (m.neighbours atom).filter (· != partner)

def Mol.hasFourPlaces (m : Mol) (atom : Nat) : Bool :=
  match m.atoms[atom]? with
  | none => false
  | some found =>
    ((m.neighbours atom).length == 4 && found.hydrogens == 0) ||
      ((m.neighbours atom).length == 3 && decide (found.hydrogens ≤ 1))

def Mol.canHaveGeometry (m : Mol) (a b : Nat) : Bool :=
  m.bonds.contains ⟨a, b, .double⟩ &&
    ((m.otherNeighbours a b).length == 1 || (m.otherNeighbours a b).length == 2) &&
    ((m.otherNeighbours b a).length == 1 || (m.otherNeighbours b a).length == 2)

def Mol.WellFormed (m : Mol) : Prop :=
  (∀ bond ∈ m.bonds, bond.a < bond.b ∧ bond.b < m.atoms.length) ∧
  m.bonds.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)) ∧
  m.orientations.Pairwise (fun x y => x.atom < y.atom) ∧
  (∀ x ∈ m.orientations, m.hasFourPlaces x.atom = true) ∧
  m.geometries.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)) ∧
  (∀ x ∈ m.geometries, m.canHaveGeometry x.a x.b = true)
```

### 3.1 The same molecule, numbered differently

A `Mol` numbers its atoms, so one molecule has many `Mol`s: another order of
its atoms gives another `Mol`, unless the two orders cannot be told apart, as
for the two atoms of `CC`. `CCO` and `OCC` are both ethanol, and they are read
as two different `Mol`s: the oxygen is atom 2 in the first and atom 0 in the
second.

`m₂` is **`m₁` numbered differently** when the atoms of `m₁` can be given new
numbers so that `m₂` comes out:

- every atom is the same atom at its new number, with its element, isotope,
  charge and hydrogens;
- two atoms are joined by a bond of some order in `m₁` exactly when the atoms
  at their new numbers are joined by a bond of that order in `m₂`;
- what `m₁` says about the orientation of an atom, for its places in some
  order, `m₂` says about the atom at its new number, for the places at their
  new numbers;
- what `m₁` says about two neighbours of a double bond, on which sides of it
  they lie, `m₂` says about the atoms at their new numbers.

The last two are about the two statements of section 12.1
(`Mol.orientationOf`, `Mol.geometryOf`), and not about the stored marks. A
stored mark is said for the numbering, so it can be another one after a
renumbering.

```lean
def Mol.Joined (m : Mol) (i j : Nat) (order : BondOrder) : Prop :=
  ⟨i, j, order⟩ ∈ m.bonds ∨ ⟨j, i, order⟩ ∈ m.bonds

structure Mol.RenumberedBy (f g : Nat → Nat) (m₁ m₂ : Mol) : Prop where
  forth : ∀ i, i < m₁.atoms.length → f i < m₂.atoms.length ∧ g (f i) = i
  back : ∀ j, j < m₂.atoms.length → g j < m₁.atoms.length ∧ f (g j) = j
  atoms : ∀ i, i < m₁.atoms.length → m₂.atoms[f i]? = m₁.atoms[i]?
  bonds : ∀ i j order, i < m₁.atoms.length → j < m₁.atoms.length →
    (m₁.Joined i j order ↔ m₂.Joined (f i) (f j) order)
  orientations : ∀ atom places, atom < m₁.atoms.length →
    (∀ i, some i ∈ places → i < m₁.atoms.length) →
    m₂.orientationOf (f atom) (places.map (Option.map f)) = m₁.orientationOf atom places
  geometries : ∀ a b x y, a < m₁.atoms.length → b < m₁.atoms.length →
    x < m₁.atoms.length → y < m₁.atoms.length →
    m₂.geometryOf (f a) (f b) (f x) (f y) = m₁.geometryOf a b x y

def Mol.Renumbered (m₁ m₂ : Mol) : Prop :=
  ∃ f g, Mol.RenumberedBy f g m₁ m₂
```

`f` gives every atom number of `m₁` its number in `m₂`, and `g` leads back.
`forth` and `back` say that each of the two undoes the other. So no two atoms
get the same new number, and every atom of `m₂` is the new place of an atom of
`m₁`.

What this definition is, and what it is not:

- It is a definition, not a program. It says that a renumbering exists, not
  how to find one. The chosen form of section 3.2 decides it, wherever the
  program works the chosen form out (theorem 27).
- It covers the numbering and nothing else. `c1ccccc1` and `C1=CC=CC=C1` are
  not the same molecule in this sense, and neither are `C` and
  `[H]C([H])([H])[H]` (see the list above).
- It behaves as "the same" must (theorem 20): it holds between every `Mol`
  and itself; it holds both ways round; and it holds through a third `Mol`.
- It is meant for well formed `Mol`s. For them, a renumbering that gives no
  atom a new number changes nothing: the two `Mol`s are equal (theorem 21).
  For a `Mol` that is not well formed the definition looks at less than is
  stored. Its clause about the bonds does not look at a bond to an atom that
  does not exist, and it does not tell a bond that is listed twice, or listed
  with its two atoms exchanged, from the same bond listed once in the usual
  way. The two clauses about the stereo facts take the neighbours of an atom
  from the list of bonds as it stands: at an atom with an orientation, or at
  a double bond with a geometry, a bond that is listed twice or that leads to
  an atom which does not exist can make a difference.
- Two examples are proven, one each way. `CCO` and `OCC` are the same
  molecule, numbered differently (theorem 41). `C1CCCCC1` and `C1CC1.C1CC1`,
  cyclohexane and two molecules of cyclopropane, are not, although they have
  the same atoms and as many bonds (theorem 42).
- It tells a molecule from its mirror image where the two are different
  molecules, and it does not compare the stored marks. A molecule that is its
  own mirror image, such as `Br[C@H](Br)C` (section 12.4), is the same
  molecule as that image, numbered differently. `N[C@@H](C)C(=O)O` and
  `C[C@H](N)C(=O)O` are two texts for L-alanine. They are read as two `Mol`s
  that store two different marks for atom 1, because they number its
  neighbours differently. `N[C@H](C)C(=O)O` is the mirror image, and its
  `Mol` has the atoms and the bonds of the first one. Two things are proven
  (theorem 43): the first two are the same molecule, numbered differently,
  and the third is not the same molecule as the first.
- The definition holds no rule for how a stored mark changes when the atoms
  get new numbers. The function of the program that puts the atoms into a new
  order says the stereo facts anew (section 3.2). For well formed `Mol`s the
  two agree, and that is proven (theorem 20): one `Mol` is another numbered
  differently exactly when it is what that function gives for the other and
  for some order that names every atom once. Theorem 23 says it for the
  chosen order.

### 3.2 The chosen form

Of all the `Mol`s that are one molecule, numbered differently, one is its
**chosen form**. The command `canonical` (section 8) writes the chosen form of
the `Mol` that it reads. So if `canonical` prints a text for one text, it
prints that same text for a second text exactly when the two are read as the
same molecule, numbered differently (theorem 31).

**The key of a `Mol`.** A `Mol` has a key: a list with one entry for every
atom, in the order of the atom numbers. The entry of an atom is a list of
numbers.

1. First come the bonds to the atoms with a smaller number, one number for
   each of these atoms, the nearest one first: for atom 3 these are the atoms
   2, 1 and 0, in this order. The number is 0 for a quadruple bond, 1 for a
   triple bond, 2 for a double bond, 3 for an aromatic bond, 4 for a single
   bond, and 5 if the two atoms are not bonded.
2. Then come four numbers that say what the atom is:
   - the place of its element in the list of section 15, counted from 0, so
     5 for carbon and 7 for oxygen;
   - 9 minus its hydrogens, or the hydrogens themselves if they are more
     than 9;
   - 0 if it has no mass number, otherwise its mass number plus 1;
   - for its charge: 0, 2, 4 and so on for the charges 0, +1, +2 and so on,
     and 1, 3, 5 and so on for the charges -1, -2, -3 and so on.
3. In a `Mol` with stereo facts, the entry of the last atom goes on with the
   stereo facts of the `Mol`: one number for every atom, in the order of the
   atom numbers, which is 0 for an atom without an orientation, 1 for
   `anticlockwise` and 2 for `clockwise`; and then one number for every bond,
   in the order of the list of bonds, which is 0 for a bond without a
   geometry, 1 for `sameSide` and 2 for `oppositeSides`. A `Mol` without
   stereo facts has no such numbers in its key.

Two keys are compared entry by entry from the front, and two entries number by
number from the front. At the first difference, the smaller number comes
first. Where one entry is the beginning of the other, the shorter one comes
first.

`OCC` is read with the oxygen as atom 0, and `CCO` with the oxygen as atom 2.
Their keys:

| Atom | `OCC` | `CCO` |
|---|---|---|
| 0 | 7, 8, 0, 0 | 5, 6, 0, 0 |
| 1 | 4, then 5, 7, 0, 0 | 4, then 5, 7, 0, 0 |
| 2 | 4, 5, then 5, 6, 0, 0 | 4, 5, then 7, 8, 0, 0 |

The key of `CCO` comes first, because it begins with 5 and the other with 7.
It is the least of the six numberings of ethanol.

For alanine, `N[C@@H](C)C(=O)O`, the entry of the last atom is 5, 4, 5, 5, 5,
then 7, 8, 0, 0, then 0, 1, 0, 0, 0, 0 for the six atoms, of which atom 1 has
the orientation `anticlockwise`, and 0, 0, 0, 0, 0 for the five bonds.

**The chosen form** of a well formed `Mol` is the well formed `Mol` with the
least key among all those that are the same molecule, numbered differently
(theorems 23 to 25). There is exactly one, because two well formed `Mol`s
with the same key are equal (the second statement of theorem 25).

```lean
def Mol.key (m : Mol) : List (List Nat)
def Mol.chosenForm (m : Mol) : Option Mol

-- `c` comes no later than `c'`: the key of `c` is not greater than the key
-- of `c'`, in Lean's own order of lists.
def Mol.noLaterThan (c c' : Mol) : Prop :=
  c.key ≤ c'.key
```

`Mol.chosenForm` gives `none` where the search gives up (see "When it gives
up" below). The first statement of theorem 25 is stated with
`Mol.noLaterThan`, which stands with the proofs
(`VeriMol/Proofs/Chosen.lean`). Its `≤` is Lean's own order of two lists,
which is the comparison described above. The fingerprint of that statement
(section 10; `CLAIMS.md`, "Trusted", says what a fingerprint covers) covers
this definition and what the key is made of: `Mol.key`, the entry of an atom
(`Mol.entry`), the numbers for an atom and for a bond (`Atom.code`,
`BondOrder.code`), the numbers for the stereo facts (`Mol.stereoCode`), and
the function that puts the atoms of a `Mol` into a new order (`Mol.arrange`),
through which the stereo facts of the last entry are said.

**Why this key.** The entry of an atom begins with its bonds to the atoms just
before it, and a bond comes before no bond. So the least key goes on, whenever
it can, with an atom that is bonded to the atom it has just placed, and of
several such atoms with the one whose bond has the highest order. The chosen
numbering therefore walks through the molecule as a usual text does, and its
spelling with round brackets (section 9.2) usually needs few ring numbers (the
end of this section shows a molecule for which it needs more than 99), and no
dot inside a piece of the molecule: none of the 62,073 chosen texts of the
real texts (section 11.1) has one. The four numbers of the atom decide where
the walk begins and which way it turns where the bonds do not decide: at the
element that comes first in section 15, and among atoms of one element at the
one with the most hydrogens, which is usually an end of the molecule. The
stereo facts come last of all. So they decide only among numberings whose
atoms and bonds give the same key, and the walk of a molecule with stereo
facts is the walk of the same molecule without them.

| Texts | What `canonical` writes |
|---|---|
| `CCO`, `OCC`, `C(O)C` | `CCO` |
| `CC(=O)O`, `OC(=O)C`, `O=C(O)C` | `CC(=O)O` |
| `c1ccccc1O`, `Oc1ccccc1`, `c1cc(O)ccc1` | `c1ccccc1O` |
| `[Na+].[Cl-]`, `[Cl-].[Na+]` | `[Na+].[Cl-]` |
| `CC(C)(C)C`, `C(C)(C)(C)C` | `CC(C)(C)C` |
| `O=C=O` | `C(=O)=O` |
| `FC(F)(F)C(F)(F)F` | `C(C(F)(F)F)(F)(F)F` |
| `N[C@@H](C)C(=O)O`, `C[C@H](N)C(=O)O` | `C[C@@H](C(=O)O)N` |
| `N[C@H](C)C(=O)O`, the mirror image | `C[C@H](C(=O)O)N` |
| `F/C=C/F`, `F\C=C\F`, `C(\F)=C/F` | `C(=C\F)/F` |
| `F/C=C\F` | `C(=C/F)/F` |

The chosen text is one text for the molecule. It is not always the text a
chemist would write: the rows of `O=C=O`, of `FC(F)(F)C(F)(F)F` and of the two
difluoroethenes start at a carbon atom, because carbon comes before oxygen and
fluorine in section 15. And it is chosen among the numberings of one `Mol`
only: `c1ccccc1` and `C1=CC=CC=C1` keep two chosen texts (section 3.1).

**A new order.** Putting the atoms of a `Mol` into a new order gives the atoms
and the bonds their new numbers, and says the stereo facts anew: the new mark
of an atom is what the `Mol` says for its places in the order of their new
numbers, and the new mark of a double bond is what the `Mol` says for the
neighbours of its two atoms that have the lowest new numbers (the two
statements of section 12.1). For a well formed `Mol` and an order that names
every atom once, the result is well formed, and it is the same molecule,
numbered differently (theorem 20, with the helper lemma
`Mol.renumbered_arrange` of `VeriMol/Proofs/Chosen.lean` for "well formed";
theorems 23 and 24 say both for the chosen order).

**How it is found.** The program does not try every numbering. It fills the
places of the new numbering one after the other. A beginning is a numbering
of which only the first places are filled. In every round, each beginning
that the search holds is extended by every atom that is not in it yet, and of
all these extensions it holds those whose new entry is the least. A beginning
with a larger entry can never become the numbering with the least key. After
the last round every numbering that it holds has the least key, and all of
them give the same `Mol`. Two rules, which follow, let it hold fewer
beginnings than there are with the least key.

**Atoms that can be exchanged.** Two atoms are **twins** when they have the
same element, isotope, charge and hydrogens, each is bonded to every third
atom exactly as the other is, and neither takes part in a stereo fact. An atom
takes part in a stereo fact when it has an orientation, when it is an atom of
a double bond with a geometry, or when it is a neighbour of such an atom.
Exchanging two atoms that are bonded alike can turn a stereo fact round: the
two bromine atoms of `Br[C@H](Br)C` are bonded alike, and exchanging them
gives the `Mol` of `Br[C@@H](Br)C`. So they are no twins. The two oxygen atoms
of `O=C=O` are twins, and so are the three fluorine atoms at one carbon atom
of `FC(F)(F)C(F)(F)F`, and the six nitrogen atoms of `N[Co+3](N)(N)(N)(N)N`.
Two twins may be bonded to each other, as the two atoms of `CC` are.
Exchanging two twins of a well formed `Mol` gives the same `Mol` (the helper
lemma `Mol.renumberedBy_swapOf` of `VeriMol/Proofs/Chosen.lean`). Without
care, the search would hold every order of them: 720 beginnings for the six
nitrogen atoms alone. So it places twins in the order of their numbers. Behind
its entry, an extension gets one more number: 1 if a twin of its new atom with
a smaller number is not placed yet, and 0 otherwise. Where two entries are
equal, the 0 comes first. This loses no chosen form: theorems 23 to 28 are
about the search as it is, with this rule.

**Beginnings that are alike.** In many molecules whole groups of atoms can be
exchanged for one another: the two ions of
`OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO`, and the four arms of each. The atoms of
two such groups are no twins, because their neighbours differ. The search
then comes to the same atoms in one order and in another. Two beginnings of
the same length are **alike** when they have placed the same atoms, and every
atom that is not placed yet is bonded to the atom at each place of the one
exactly as to the atom at that place of the other: by a bond of the same
order, or not at all.

Take the ring `C1CCCCC1`, with its atoms numbered 0 to 5 round the ring. The
beginnings 0, 1 and 1, 0 have placed the same atoms, and they are not alike:
atom 2 is bonded to the second place of the one and to the first place of
the other. The beginnings 0, 1, 2, 3, 4 and 4, 3, 2, 1, 0 are alike: the one
atom that is left, atom 5, is bonded to the first and to the last place of
both. The kind of bond counts as well. In `C=1=[C](=[C])[C]1` the beginnings
0, 3 and 3, 0 have placed the same atoms, and atom 1 is bonded to both places
of both: by a double bond to atom 0 and by a single bond to atom 3. So they
are not alike, and only the second of them leads to the least key:
`canonical` writes `[C]1=C=[C]1=[C]`.

For a `Mol` without stereo facts, whatever is put behind one of two
beginnings that are alike can be put behind the other, and every atom gets
the same entry behind both, with the same number for its twins. Such an entry
says only how the atom is bonded to each place before it, and what the atom
is; and the number for its twins depends only on which atoms are placed. So
of the beginnings that are alike the search holds only the first. Going round
the ring of `C1CCCCC1` it holds up to 12 beginnings, one for each atom to
start at and each way round; when the ring is closed, all of them have placed
the same six atoms, and it holds one. The rule for beginnings that are alike
loses no chosen form either: theorems 23 to 28 are about the search as it is,
with both rules.

A `Mol` with stereo facts has no such rule. The entry of its last atom says
the stereo facts of the whole numbering (point 3 above), and those can
differ for two beginnings that are alike.

**When it gives up.** The two rules do not find every case in which two
beginnings lead to the same `Mol`, and the search holds every beginning that
they leave. When a round would leave more than 1,000 beginnings, the search
gives up, and `canonical` answers
`error: the chosen form is not worked out: too many numberings of this molecule look alike`,
with exit code 1. Whether it gives up does not depend on how the atoms are
numbered (theorem 26).

The beginnings are counted after those that are alike are taken out.
`[N][N][N]1[N][N][N][N]1` is a ring of five atoms with a tail of two, and all
seven atoms are the same. After four rounds there are 18 beginnings with the
least key: the paths of four atoms, each in both directions. The two
directions along the four ring atoms that do not carry the tail are alike,
so the search holds 17. So 17 are counted, not 18: with a limit of 17 in
the place of 1,000 the search would not give up here.

Two texts show where the limit lies. Nine molecules of ethane,
`CC.CC.CC.CC.CC.CC.CC.CC.CC`, get a chosen text, and ten,
`CC.CC.CC.CC.CC.CC.CC.CC.CC.CC`, do not. The two atoms of one molecule are
twins, so each molecule is walked in one way. Two beginnings that have placed
the same molecules in another order are alike, and two that have placed
different molecules are not. So after four of the nine molecules the search
holds one beginning for each choice of four, which are 126. With the first
atom of a fifth molecule they are 126 times 5, which is 630, and no round
holds more. Of ten molecules there are 210 choices of four, and with the
first atom of one of the six others that makes 1,260: the search gives up.
It gives up in the round in which the beginnings become too many, also where
fewer would be left at the end: when all ten molecules are placed, all
beginnings are alike, and one would be left.

For a `Mol` with stereo facts, only the rule for twins keeps the search
small. The three rings of `C1CCCCC1.N1NNNN1.O1OOOO1` have 12, 10 and 10
numberings with the least key. Without a stereo fact that does no harm: the
ways round a ring are alike once the ring is closed, the search never holds
more than 12 beginnings, and the text gets a chosen text. Put alanine beside
the rings, `C1CCCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O`, and the search gives
up: the `Mol` has a stereo fact, so the rule for beginnings that are alike
is not used, and the search would hold 12 times 10 times 10 beginnings,
which is 1,200. With a ring of five atoms in the place of the first,
`C1CCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O`, they are exactly 1,000, no round
of the search holds more, and the text gets a chosen text.

A small text is enough for that. Six molecules of ethane beside one molecule
with a stereo fact, `CC.CC.CC.CC.CC.CC.C[C@H](N)O`, make the search give up.
The molecules of ethane are placed first, and in every order: after four of
them the search holds 6 times 5 times 4 times 3 beginnings, which is 360.
Each goes on with the first atom of one of the two molecules of ethane that
are left, or with the first atom of the seventh molecule, and that makes
1,080. With five molecules of ethane the search holds 240 beginnings at
most, and the text gets a chosen text.

Of the 62,075 real texts that are read, the search gives up for none.

The time grows fast with the number of atoms, about as its cube: the search
has a round for every atom, a round tries every atom that is not placed yet,
for every beginning that it holds, and every try works out an entry with one
number for each atom placed before. On one desktop machine a chain of 200
carbon atoms took 0.3 seconds, one of 400 took 2.6 seconds and one of 800 took
20 seconds. No check prints these times, and on another machine they are other
times. They are the times of chains, for which the search holds two
beginnings, one from each end. Where it holds many, the same number of atoms
takes far longer (see "The limit holds the memory down, and not the time"
below).

**More than 1,000 atoms.** `canonical` does not work out the chosen form of a
`Mol` with more than 1,000 atoms. It answers
`error: the chosen form is not worked out: more than 1000 atoms`, with exit
code 1, before the search begins. The reason is the memory: for atoms that are
twins of one another the program keeps a table that grows with the square of
their number, and without a limit one long text can take all the memory of a
machine. The limit is a rule of the command and not of the chosen form: the
chosen form is defined for every well formed `Mol`, `Mol.chosenForm` has no
such limit, and theorems 23 to 28 do not know it. A `Mol` of exactly 1,000
atoms is still searched. And the atoms are counted before the search is asked:
take the ten molecules of ethane, on which the search gives up, and put a dot
and a chain of 981 carbon atoms behind them. The text has 1,001 atoms, and it
gets the answer about the atoms.

**The limit holds the memory down, and not the time.** For a `Mol` with stereo
facts the search counts the beginnings that a round would leave before it
makes them. For a `Mol` without stereo facts it goes through them one by one
and stops at the 1,001st that is alike to none before it. So the round in
which it gives up needs little memory as well. To tell which beginnings are
alike, the search keeps a list for each beginning that it has taken in the
round, at most 1,000 lists: such a list says for every atom whether it is
placed, and if not, how it is bonded to the places. But a text of at most 1,000
atoms can still take very long: every round does its work once for each
beginning that the search holds, and it can hold 1,000. And where many atoms
are twins of one another, every try also looks through the twins that are
placed already. That the memory stays small was seen on texts that were made
to be hard. No check measures it, and nothing is proven about it.

The writer can refuse the chosen form, as it can refuse any `Mol` (section
9.4). Often the chosen numbering needs few ring numbers, because it follows
the molecule: the ladder of section 9.4, which `rewrite` refuses, gets a
chosen text. But it can also need more than the text that was read. Take a
ladder of 102 rungs with one rail of carbon and one of nitrogen: `C1NN2C1`,
then `C1N2N2C1` written 49 times, then `C1N2NC1`. The text has 406 characters
and 204 atoms. It goes down the ladder rung by rung, with two ring numbers
open at a time, and `rewrite` and `plain` write it. The chosen numbering
takes the carbon atoms first, from one end of their rail to the other, and
then the nitrogen atoms the other way back. So 101 of the 102 rungs get a
ring number, and all of them are opened before the first one closes:
`canonical` answers
`error: more than 99 ring numbers are needed at the same time`. It is one of
the test texts (section 11.1).

The writer has more reasons to refuse a `Mol` with stereo facts (section
12.3), and the chosen numbering can meet one that the text avoided.
`CC1CCC2CC[S@+]12` is read, and `rewrite` writes it back. In its chosen
numbering the sulfur would be written with exactly one ring number, and
`canonical` answers
`error: a stereo centre with a free place would be written with one ring number and only single bonds`.
Of the real texts, 2 get this answer.

Before it counts the atoms and before it searches, `canonical` asks whether
the `Mol` is well formed, as the writer does (section 9.4). No text gives a
`Mol` that is not (theorem 8).

## 4. Which texts are read

The grammar of a text without the stereo marks `@`, `@@`, `/` and `\`, which
section 12.2 adds. It is the grammar of OpenSMILES, restated, with the
differences that section 4.1 lists:

```
smiles        ::= chain?
chain         ::= branched_atom ( bond? branched_atom | '.' branched_atom )*
branched_atom ::= atom ringbond* branch*
branch        ::= '(' ( bond | '.' )? chain ')'
ringbond      ::= bond? DIGIT | bond? '%' DIGIT DIGIT
bond          ::= '-' | '=' | '#' | '$' | ':'
atom          ::= bracket_atom
                | 'B' | 'C' | 'N' | 'O' | 'P' | 'S' | 'F' | 'Cl' | 'Br' | 'I'
                | 'b' | 'c' | 'n' | 'o' | 'p' | 's'
bracket_atom  ::= '[' isotope? symbol hcount? charge? ']'
isotope       ::= DIGIT+
symbol        ::= one of the 118 element symbols of section 15
                | 'b' | 'c' | 'n' | 'o' | 'p' | 's' | 'se' | 'as'
hcount        ::= 'H' DIGIT?
charge        ::= '+' | '++' | '+' DIGIT DIGIT? | '-' | '--' | '-' DIGIT DIGIT?
```

In words:

- The whole text is the SMILES. White space is not allowed anywhere. An empty
  text is allowed and gives a `Mol` without atoms.
- Ring numbers come directly after their atom, before any branch of that atom.
- A branch is never empty. It may start with a bond symbol or with a dot.
- Inside square brackets, an element symbol of two letters wins over one of
  one letter: `[Co]` is cobalt.
- A hydrogen atom cannot have a hydrogen count: `[HH]` is not read. OpenSMILES
  requires this.

Not read, each with a clear error (section 6):

| Not read | Examples |
|---|---|
| the stereo classes that are written with letters (section 12.4) | `C[C@TH1](F)(Cl)Br` |
| the wildcard atom | `*C`, `[*]` |
| atom classes | `[CH3:1]` |
| reactions, query patterns (SMARTS), extensions that individual programs add | `CC>>CO`, `N->[Fe]`, `[te]` |

### 4.1 Where this document differs from OpenSMILES

| Point | OpenSMILES | This document |
|---|---|---|
| white space | ends the SMILES; what follows it is ignored | is an error |
| the wildcard atom `*` and atom classes, as in `[CH3:1]` | part of the notation | not read |
| stereo marks | part of the notation | `@`, `@@`, `/` and `\` are read (section 12), and not the rarer forms (section 12.4): the stereo classes written with letters; `@` or `@@` at an atom that does not have four places, which OpenSMILES uses as a short form at an atom with five or six neighbours, as in its example `C[Co@](F)(Cl)(Br)(I)S`, and at the middle atom of `C=C=C`; and `/` and `\` along several double bonds in a row, as in its example `F/C=C=C=C/F`. Three more kinds of texts with these marks are refused (section 12.2): a mark that takes part in the geometry of no double bond, which OpenSMILES treats as invalid and lets a reader ignore on request; and two spellings of an atom with a free place, which OpenSMILES leaves open or which programs read differently. |
| element symbols | 114 | those 114 and Nh, Mc, Ts and Og, which were named later |
| lowercase atoms | must form rings in which single and double bonds can alternate | not checked. Later work can check it for the aromatic bonds of a `Mol` (section 13). A lowercase atom without an aromatic bond cannot be told from an uppercase one with the same hydrogens: `c-c` and `[CH2][CH2]` give one `Mol` (section 3). So only a reader could report it. |
| hydrogens of a bare lowercase atom | no rule is given | rule 7 of section 5 |
| an aromatic bond `:` at a bare uppercase atom | it does not say what an aromatic bond counts when the bonds of such an atom are added up for its hydrogens | the bond counts 1 there, as a single bond does (rule 7 of section 5): `C:C` has 3 hydrogens at each atom |
| the order inside square brackets | its grammar fixes the order: the stereo mark, then the hydrogens, then the charge. Its section on the standard form gives other orders as valid, though not as the standard form: `[C-H3]` and `C[CH@](Br)Cl` are its examples | the grammar is followed: `[C+H]` and `C[CH@](Br)Cl` are not read |
| the digits of a hydrogen count | "a number"; whether more than 9 hydrogens are possible is put there as a question | one digit, as in its grammar: `[CH10]` is not read |
| ranges | charges from -15 to +15 and isotopes up to 999 must be read | every charge of one or two digits and every isotope is read |

Everything else is meant to follow OpenSMILES, including what it forbids: a
hydrogen count on a hydrogen atom, a ring number behind a branch or behind a
dot, a ring bond whose two ends name different bonds, two bonds between the
same two atoms, and an atom bonded to itself.

## 5. How a text becomes a `Mol`

Rules 1 to 7 are those of a text without stereo marks. Rules 8 to 10, for the
marks, stand in section 12.2. They add the stereo facts and change nothing in
the atoms and the bonds that rules 1 to 7 give.

1. **Numbering.** Atoms are numbered from 0 in the order in which they are
   written.
2. **Atoms.** For a bracket atom, isotope, hydrogens and charge are what is
   written; a missing hydrogen count or charge means 0, and `H` alone means 1
   hydrogen. `[13C]` and `[013C]` are the same. `+` and `-` alone mean +1 and
   -1; `++` and `--` mean +2 and -2. Whether the symbol is lowercase is not
   stored. It counts in rules 5 and 7, and nowhere else.
3. **Bonds along the text.** An atom is bonded to the atom written before it,
   unless a dot stands between them. The first atom of a branch is bonded to
   the atom the branch hangs on, unless the branch starts with a dot. After a
   branch, the text continues from the atom the branch hangs on.
4. **Ring bonds.** Two ring numbers with the same value join their two atoms.
   `%05` and `5` are the same value. Once a number is closed it can be used
   again. A ring bond may join atoms on two sides of a dot: `C1.C1` is ethane.
5. **Bond order.** A written bond symbol gives the order: `C=CC#N` has a
   double bond, a single bond and a triple bond. Without a symbol the bond is
   aromatic if both atoms are lowercase, and single otherwise. So biphenyl
   needs its `-`: `c1ccccc1-c1ccccc1`. A symbol may also be written where a
   missing one means the same bond: `c:1:c:c:c:c:c:1` is read as `c1ccccc1`
   is. A ring bond may carry its symbol at either end or at both; at both
   ends the symbols must be the same.
6. **Storing.** Every bond is stored with the smaller atom number first, and
   the bonds are sorted. So the result is always well formed.
7. **Hydrogens of bare atoms.** They are worked out as follows.
   1. Add up the bonds of the atom: single 1, double 2, triple 3, quadruple 4,
      aromatic 1.
   2. Take the smallest normal valence of the element that is at least this
      sum. If there is none, the atom has 0 hydrogens.
   3. Otherwise the hydrogens are that valence minus the sum. A lowercase atom
      gets one fewer, but never fewer than 0.

| Element | B | C | N | O | P | S | F, Cl, Br, I |
|---|---|---|---|---|---|---|---|
| Normal valences | 3 | 4 | 3, 5 | 2 | 3, 5 | 2, 4, 6 | 1 |

Examples: `C` has 4 hydrogens. In `CC(=O)O` the atoms have 3, 0, 0 and 1. In
`c1ccccc1` every atom has 1. In pyridine, `c1ccncc1`, the nitrogen has 0.

Steps 1 and 2 and the table are from OpenSMILES, which gives no rule for
lowercase atoms. With "one fewer", rule 7 gives exactly the hydrogens that Open
Babel 3.1.1 counts: this was tried for every bare symbol with every combination
of up to four bonds (single, double, triple, quadruple and aromatic), 2,016
cases in all. With its clean-up off, RDKit 2024.03.3 counts differently in five
situations (section 11.2). They are rare: of the 62,075 real SMILES texts that
are read, RDKit counts other hydrogens in 5.

## 6. Errors

An error is one line of the form

```
error: position 3: <what is wrong>
```

and the program ends with exit code 1.

The text is gone through once, from left to right, and the first problem that
is met is reported. So nothing inside the text is wrong before the reported
position, apart from a problem with its stereo marks of the kind that is
looked for last (below). A problem that only shows at the end of the text,
such as a `(` that is never closed, comes after every problem inside the text.
`CC(C))C(=O)[O-` has two problems, and the report is
`position 5: ')' has no matching '('`. The four messages of the end of the
text are checked only when the whole text is gone through, in the order of the
last table of this section. So one of them can be reported while something
before its position is left open as well: `C1(C.` gets position 4, for the
dot, and its `(` and its ring number are never closed. Five of the seven
problems with the stereo marks of a text (section 12.2, the last five rows of
its table) are looked for last of all, when the text has no other problem. So
`F[C@H2]Cl)` is reported for its `)`, at position 9, although its carbon atom
cannot be a stereo centre.

Each step takes the next atom, symbol or number from the text. It must be
readable (characters and bracket atoms), and then it must be allowed at its
place (structure).

**Characters and bracket atoms.** The inside of a pair of square brackets is
gone through from left to right as well. A `[` without a `]` behind it is
reported at once, whatever follows it. The position is that of the character
named, unless the table says otherwise.

| Message | Examples, with the position |
|---|---|
| `white space is not allowed` | `C C` (1) |
| `the wildcard atom is not read` | `*C` (0) |
| `atom classes are not read` | `[CH3:1]` (4) |
| `an element symbol is expected here` | `[]` (1), `[13]` (3), `[Xx]` (1), `[te]` (1) |
| `a hydrogen atom cannot have a hydrogen count` | `[HH]` (2) |
| `'[' is never closed` (position of the `[`) | `C[NH3` (1) |
| `'%' must be followed by two digits` (position of the `%`) | `C%1CC%1` (1) |
| `'X' cannot be read here`, for any other character that does not fit | `CX` (1), `H` (0), `CL` (1), `[CH10]` (4), `[Fe+++]` (5) |

A character that does not fit, and that no other row of the table covers (a
`[` without a `]`, a `%` without two digits, a hydrogen count on a hydrogen
atom), gets the first of these messages that applies:
`white space is not allowed`; `the wildcard atom is not read` for `*`;
`atom classes are not read` for a `:` inside square brackets; and otherwise
`'X' cannot be read here`. So an `@` outside square brackets, as in `C@`, and
a third `@` in them, as in `[C@@@]`, get `'@' cannot be read here`. One place
is different: where square brackets must name their element, everything but
white space and `*` gives `an element symbol is expected here`.

**Structure.** What may come next depends on what was read last:

| Read last | May come next |
|---|---|
| nothing yet | an atom, or the end of the text |
| a dot | an atom |
| `(` | an atom, a bond symbol, a dot |
| a bond symbol after `(` or `)` | an atom |
| a bond symbol after an atom or a ring number | an atom, a ring number |
| an atom or a ring number | an atom, a bond symbol, a ring number, `(`, `)`, a dot, the end of the text |
| `)` | an atom, a bond symbol, `(`, `)`, a dot, the end of the text |

A `)` also needs a branch that is still open. Anything else gives one of the
messages below. The position is that of the atom, symbol or number that is out
of place, unless the table says otherwise. A ring number written with `%` has
the position of the `%`.

| Message | Examples, with the position |
|---|---|
| `an atom is expected here` | `=C` (0), `(C)C` (0), `C..C` (2), `C()C` (2), `C(=)C` (3) |
| `an atom or a ring number is expected here` | `C==C` (2), `C=(C)C` (2), `C=.C` (2), `C=)` (2) |
| `a ring number must come before the branches of its atom`, for a ring number after `)`, with or without a bond symbol in between | `C(C)1CC1` (4), `C(C)=1CC1` (5) |
| `')' has no matching '('` | `C)C` (1) |
| `an atom cannot be bonded to itself` | `C11` (2), `C=1-1` (4) |
| `the two ends of ring 1 name different bonds` | `C=1CC-1` (6) |
| `these two atoms are already bonded` | `C1C1` (3), `C12CC12` (6) |
| `the text ends after a bond symbol` (position of that symbol) | `C=` (1) |
| `the text ends after a dot` (position of the dot) | `C.` (1) |
| `'(' is never closed` (position of the `(`) | `C(C` (1), `C(C(C` (3), `C1(C` (2) |
| `ring 1 is opened but never closed` (position of the number) | `C1CC` (1), `C1C0` (1) |

An atom may always come. When the table of what may come next does not let
something else come, the message is:

- for a ring number after `)`, with or without a bond symbol between them:
  `a ring number must come before the branches of its atom`;
- for anything else after a bond symbol that follows an atom or a ring
  number: `an atom or a ring number is expected here`;
- for anything else: `an atom is expected here`.

A `)` is held against the table first. Only if the table lets it come is it
checked for an open branch. So `C=)` gets
`an atom or a ring number is expected here`, although no branch is open. If
the table does not let the text end, the message is the one of the end of the
text for what was read last: a bond symbol, a dot or a `(`.

The three ring messages in the middle are checked in the order of the table.
`C=1-1` closes ring 1 at the atom that opened it, and with another bond
symbol than the one it was opened with: two of these messages fit, and it
gets the first. The last four messages, which belong to the end of the text,
are checked in the order of the table as well: `C1(C` leaves a `(` and a ring
number open, and the `(` is reported. For an unclosed `(` it is the last one
opened, as in `C(C(C`. For an unclosed ring number it is the first one
opened, whatever its number: in `C1C0` that is ring 1 and not ring 0.

## 7. What is printed

A `Mol` is printed in one fixed layout, which is also valid Lean: put on lines
of its own in a Lean file where a `Mol` is expected, it is that `Mol`. Behind
other code on the same line Lean refuses it, because `bonds` must not stand
further left than `atoms`.

```
$ app 'CC(=O)O'
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

With stereo facts:

```
$ app 'C[C@H](F)/C=C/Cl'
{ atoms := [
    { element := .C, isotope := none, charge := 0, hydrogens := 3 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .F, isotope := none, charge := 0, hydrogens := 0 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .C, isotope := none, charge := 0, hydrogens := 1 },
    { element := .Cl, isotope := none, charge := 0, hydrogens := 0 } ],
  bonds := [
    { a := 0, b := 1, order := .single },
    { a := 1, b := 2, order := .single },
    { a := 1, b := 3, order := .single },
    { a := 3, b := 4, order := .double },
    { a := 4, b := 5, order := .single } ],
  orientations := [
    { atom := 1, orientation := .clockwise } ],
  geometries := [
    { a := 3, b := 4, geometry := .oppositeSides } ] }
```

- One atom, one bond, one orientation and one geometry per line, each
  indented by four spaces, with a comma after every line but the last of its
  list.
- All four lists and every field are always shown, in this order.
- An isotope is printed as `some 13`, a negative charge as `-1`.
- An empty list is printed as `[]` on the line of its name: a `Mol` without
  atoms starts with `{ atoms := [],`, and one without stereo facts ends with
  `  orientations := [],` and `  geometries := [] }`.
- The output ends with a line break.

## 8. Commands

| Typed | What happens |
|---|---|
| `app '<SMILES>'` | The text is read. On success the `Mol` is printed and the exit code is 0. Otherwise the error is printed and the exit code is 1. |
| `app rewrite '<SMILES>'` | The text is read and written back in the usual spelling, with round brackets (section 9.2), followed by a line break. Errors as above, and the writer can refuse the `Mol` (sections 9.4 and 12.3). |
| `app plain '<SMILES>'` | The same in the plain spelling (section 9.1). |
| `app canonical '<SMILES>'` | The text is read, and the chosen form of its `Mol` (section 3.2) is written in the usual spelling, followed by a line break. Two texts that are read as the same molecule, numbered differently, get the same answer (theorem 32). Errors as above; three more can come: a `Mol` of more than 1,000 atoms is refused, the search can give up (section 3.2), and the writer can refuse the chosen form (sections 3.2, 9.4 and 12.3). |
| `app filter perfluoro 6 '<SMILES>'` | The filter (section 16). The text is read. If its `Mol` is sound and has no perfluorinated group of 6 or more carbon atoms, the `Mol` is printed as in the first row and the exit code is 0. Otherwise the error is printed, with the reason, and the exit code is 1. In the place of 6 any number from 1 on may stand (section 16.1). |
| anything else | `error: expected a SMILES text, or one of the words rewrite, plain and canonical followed by a SMILES text, or the words filter perfluoro followed by a number from 1 on and a SMILES text`, exit code 1 |

"Anything else" includes no argument at all, one of the words `rewrite`,
`plain` and `canonical` with no text behind it, two arguments of which the
first is none of these three words, three arguments, more than four, and
four arguments that are not the words `filter` and `perfluoro`, a number from
1 on and a text. One argument alone that is none of the three words is
always taken for a text: `app filter` answers
`error: position 0: 'f' cannot be read here`. Theorems 2, 4, 5 and 49 say
which answer each row gives, for every list of arguments: they say it of the
function that is the whole program, in terms of the reader, of the three
writers (those of `rewrite`, `plain` and `canonical`) and of the filter.

The `Mol` and the rewritten text go to standard output. Errors go to standard
error.

An error message repeats a character that cannot be read as it is, also one
that a terminal does not show, such as a form feed. An argument that is not
text (bytes that are not valid UTF-8) is not a SMILES text: Lean hands the
program the replacement character U+FFFD where such bytes stand, and the
program reports that character. The model, a Python program (section 11.1),
sees such a byte in another way, so the two are not compared on such an
argument.

The OpenSMILES document asks more of a canonical SMILES than this command
gives. There a SMILES is canonical when it follows that document's standard
form and, in addition, always has the atoms of a molecule in the same order.
`canonical` gives the second only, and only where it finds a chosen form
(section 3.2). It writes in the spelling of `rewrite`: `O=C=O` gets
`C(=O)=O`, and `C1=CC=CC=C1` keeps its alternating bonds.

Sometimes the answer cannot be written to standard output: the disk is full,
the output is closed, or the answer goes into a pipe whose reader has gone.
Then the program ends with exit code 1, and Lean writes one line of its own
on standard error. The line begins with `uncaught exception:` and gives the
reason from the system, for example `invalid argument` for an output that is
closed. The reason is about the output, not about the SMILES text, and the
line is not one of the messages of section 6. Part of the answer may have
been written before. Exit code 0 means that the whole answer was handed on.
It does not mean that someone read it: if the reader of a pipe goes away
after the answer is in the pipe, nobody notices. The model of section 11.1 is
only asked for its answers, so none of this is compared with it.

On a command line the text stands in single quotes. Inside double quotes a
shell such as bash can change a text that holds a `$`, which is the symbol of
the quadruple bond, before the program is started: bash passes `[Mo]$[Mo]` on
as `[Mo]0`. The program then answers the text that it was given, and not the
one that was typed.

## 9. The writer

The writer turns a `Mol` into text. It writes the atoms in the order of their
numbers, so that reading the text gives every atom its number back. Every bond
is written once, in one of two ways: **by position**, when an atom stands next
to an earlier atom, or with a **ring number**.

The writer knows two spellings.

- The **plain spelling** (9.1) is made to be proven, not to be read. It has no
  round brackets, every atom stands in square brackets and every bond has its
  symbol, or a mark in its place (12.3). So nothing in it depends on what a
  reader assumes, apart from the order of a bond that carries a mark (rule
  8). Like the spelling with round brackets it keeps the numbering of the
  atoms, whatever that is, and refuses only the `Mol`s of sections 9.4 and
  12.3. It is what `plain` prints. That reading its text returns the `Mol`
  is theorem 12.
- The **spelling with round brackets** (9.2) is the usual one: branches in
  round brackets, atoms without square brackets where that is safe, and no
  bond symbol where a reader assumes it. It is what `rewrite` and
  `canonical` print. Theorem 11 says the same of it.

Sections 9.1 and 9.2 describe the two spellings for a `Mol` without stereo
facts. Section 12.3 adds the marks of a `Mol` that has them.

In square brackets an atom is written the same way in both spellings: its
isotope, if it has one; its symbol; `H` if it has one hydrogen, and `H` with
the number if it has two to nine; `+` or `-` if its charge is +1 or -1, and
the sign with the number for any other charge that is not 0. Examples:
`[13CH4]`, `[NH4+]`, `[Fe+2]`, `[O-]`, and the `[nH]` of pyrrole (see the next
paragraph).

**Lowercase.** In both spellings the symbol of an atom is written in lowercase
when one of its bonds is aromatic and its element has a lowercase symbol
(section 4): B, C, N, O, P, S, Se and As. Otherwise it is written as the
element's own symbol. So the writer decides the case of a symbol from the
bonds, and a text need not come back with the letters it had. `C:C` comes back
as `[cH3][cH3]`, `c-c` as `[CH2][CH2]`, and `[nH]` alone as `[NH]`. In
pyrrole, `c1cc[nH]c1`, the `[nH]` has two aromatic bonds and stays. RDKit
reads each of these rewritten texts as the `Mol` that was written. Open Babel
works out aromatic bonds by its own rules and takes none that lies in no ring:
it reads `C:C` with a single bond and `[cH3][cH3]` with a double bond. So for
a text with `:` at an atom in uppercase, Open Babel can read the rewritten
text as another molecule than the original. No real text has the symbol `:`.

### 9.1 The plain spelling

For every atom, in the order of the atom numbers:

1. If it is not the first atom: when it is bonded to the atom just before it,
   the symbol of that bond is written; otherwise a dot is written.
2. The atom is written in square brackets.
3. For each of its bonds to an atom other than the one just before it and the
   one just after it, in the order of the other atom's number, a ring number
   is written. A bond to a later atom takes the smallest ring number from 1 to
   99 that is not in use, with the symbol of the bond in front. A bond to an
   earlier atom is closed with the number it was given, without a symbol.

Ring numbers 1 to 9 are one digit, 10 to 99 are `%` and two digits.

A branch is therefore written with a ring number. A ring number does not have
to close a ring: it only says that the two atoms carrying it are bonded.
Isobutane, `CC(C)C`, is written `[CH3]-[CH]-1-[CH3].[CH3]1`:

| Written | Meaning |
|---|---|
| `[CH3]` | atom 0 |
| `-[CH]` | atom 1, with a single bond to atom 0 |
| `-1` | ring number 1 opens a single bond from atom 1 to an atom that comes later |
| `-[CH3]` | atom 2, with a single bond to atom 1 |
| `.` | the next atom is not bonded to atom 2 |
| `[CH3]1` | atom 3. Ring number 1 closes: atom 3 is bonded to atom 1. |

So atom 1 has three neighbours, as in `CC(C)C`. The reader returns the same
`Mol` for both texts.

### 9.2 The spelling with round brackets

It differs from the plain spelling in three points.

**Round brackets.** An atom may also stand next to an atom further back in the
text. While writing, the writer keeps a **path**: the atoms from which the
text can still go on. They are the atom just written, the atom it stands next
to, the atom that one stands next to, and so on.

For every atom, in the order of the atom numbers:

1. Among the atoms of the path that it is bonded to, the one written last
   becomes its **parent**. The atom is written next to its parent. The path is
   then cut back to the parent and goes on with the new atom.
2. If it is bonded to no atom of the path, all open round brackets are closed
   and, unless it is the first atom, a dot is written. The path starts again
   with this atom.
3. To get back to the parent, every round bracket that was opened after the
   parent and is still open is closed. A `(` is written before the atom if a
   later atom has the same parent. Then come the bond symbol, if it is
   written, and the atom.
4. Its bonds that are not written by position get ring numbers, as in the
   plain spelling.

At the end of the text all open round brackets are closed.

The closing in rule 2 and the closing at the end of the text never have
anything to close, and rule 3 closes one round bracket at most. In front of an
atom, a round bracket is open at an atom of the path, other than the one
written last, exactly when that atom is the parent of this atom or of a later
one; and an atom that has left the path is the parent of no later atom. So
when the text comes back to a parent, the innermost open round bracket is the
one of that parent, and rule 3 closes exactly that one. In front of an atom
without a parent, and at the end of the text, none is open. The Lean program
writes its round brackets by these facts and keeps no list of the open ones.
It is proven that this changes no text (a helper lemma,
`VeriMol/Proofs/BracketRules.lean`; `CLAIMS.md` says what the lemma covers and
what it does not). The model follows the rules as they stand.

**Bare atoms.** An atom is written bare, without square brackets, when all of
these hold:

1. its element is one of B, C, N, O, P, S, F, Cl, Br and I;
2. it has no isotope and no charge;
3. its hydrogens are exactly what rule 7 of section 5 gives a bare atom with
   its bonds, for the case in which the writer writes its symbol (see
   "Lowercase" above);
4. its bonds add up to at most the smallest normal valence of its element, or
   to exactly one of its normal valences;
5. none of its bonds is aromatic, or it is written in lowercase. So an atom of
   F, Cl, Br or I with an aromatic bond keeps its square brackets: `F:C` comes
   back as `[F]:[cH3]`.

Conditions 1 to 3 make sure that reading the bare atom gives the same atom
back. Conditions 4 and 5 keep the square brackets in the situations in which
this program and RDKit count the hydrogens of a bare atom differently (section
11.2). `Cl[I]Cl` is written as it stands: in `ClICl` this program would read
the iodine without a hydrogen, but RDKit with one.

**Bond symbols.** The symbol of a bond is left out when it is the one a reader
assumes (section 5, rule 5): aromatic between two atoms that are written in
lowercase, and single between any other two. So the `-` of
`c1ccccc1-c1ccccc1` stays.

| Text read | Plain spelling | With round brackets |
|---|---|---|
| `CC(C)C` | `[CH3]-[CH]-1-[CH3].[CH3]1` | `CC(C)C` |
| `CC(=O)O` | `[CH3]-[C]-1=[O].[OH]1` | `CC(=O)O` |
| `c1ccccc1O` | `[cH]:1:[cH]:[cH]:[cH]:[cH]:[c]1-[OH]` | `c1ccccc1O` |
| `C:C` | `[cH3]:[cH3]` | `[cH3][cH3]` |
| `c-c` | `[CH2]-[CH2]` | `[CH2][CH2]` |
| `[Na+].[Cl-]` | `[Na+].[Cl-]` | `[Na+].[Cl-]` |

Round brackets help only when the atom numbers follow the molecule, as they do
when the reader made the `Mol` from a usual text. For another numbering this
spelling needs dots and ring numbers too: propane with its atoms numbered end,
end, middle is `C1.CC1`.

### 9.3 What the program writes

For `plain` the program writes the plain spelling, and for `rewrite` the
spelling with round brackets. Where a spelling refuses a `Mol`, its command
refuses it (sections 9.4 and 12.3). `canonical` writes the chosen form of the
`Mol` in the spelling with round brackets (section 3.2).

No text is read back before it is returned: that reading it returns the same
`Mol`, with its stereo facts, is proven for both spellings (theorems 11 and
12), so such a check would add nothing. Whatever text `rewrite` or `plain`
prints is read as the `Mol` of the original text (theorem 13).

`rewrite` writes every real text that is read, all 62,075, and none needs a
dot inside a piece of its molecule. 47,446 of them come back character for
character. Many of the others differ only in their ring numbers: which number
is used, or the order of two numbers at one atom.

### 9.4 What the writer refuses

The writer refuses a `Mol` that it cannot spell, with an error instead of a
text. For a `Mol` without stereo facts these are all its reasons; section
12.3 has the others.

- it is not well formed (`the Mol is not well formed`);
- an atom has more than 9 hydrogens, or a charge beyond +99 or -99
  (`an atom has more than 9 hydrogens, or a charge beyond +99 or -99`);
- a hydrogen atom has hydrogens of its own
  (`a hydrogen atom has hydrogens of its own`);
- its spelling needs more than 99 ring numbers at the same time
  (`more than 99 ring numbers are needed at the same time`). Each of the
  two spellings needs its own number of them, so the two can differ in this.
  Take the text made of `C`, then `(C)` written 100 times, then `C`: one
  carbon atom with 101 others around it, and nothing else. `rewrite` writes it
  back, and `plain` refuses it. It is one of the test texts. With `(C)`
  written 99 times `plain` writes the text as well: it takes the smallest free
  ring number each time, and so it uses every number from 1 to 99.

The writer asks in this order: first whether the `Mol` is well formed; then
its atoms, one after the other, and the first atom that cannot be written
gives the message (of the two reasons about an atom, the one about hydrogens
and charge is asked first); and the ring numbers last. So a `Mol` that is not
well formed gets that message whatever its atoms are, and the message about
an atom comes before the ring numbers are counted, wherever the atom stands.
For `canonical` the atoms are those of the chosen form, in its order.

A `Mol` that the reader returned is never of the first three kinds: it is well
formed (theorem 8), and the reader cannot read what the next two describe
(theorem 10). So for a text that was read as a `Mol` without stereo facts,
`rewrite` and `plain` can refuse with one message only (theorem 18). They
then print
`error: more than 99 ring numbers are needed at the same time` and end with
exit code 1. Theorem 19 says when: the message comes exactly when, behind
some atom, more than 99 bonds wait for their second atom with a ring number.
These are the bonds that begin at that atom or before it and end behind it,
apart from those that are written without a ring number: for `plain` the
bonds that join two atoms that follow each other, and for `rewrite` the bond
of an atom to its parent (section 9.2). The same theorem says that the
message is true whenever a spelling gives it, for a `Mol` with stereo facts
as well, and so also where `canonical` prints it for a chosen form. With the
real texts it never came.

"Needed" means needed by these two spellings, not by the `Mol`. Each spelling
fixes where every atom and every ring number is written (sections 9.1 and
9.2), and another text for the same `Mol` can need fewer. A text can draw a
ladder of 100 rings with round brackets nested 100 deep, and with one ring
number open at a time: `C(` written 100 times, then `CC1`, then `)C11` written
99 times, then `)C1`. It has 602 characters, 202 atoms and 301 bonds. The
reader reads it. Both spellings need 100 ring numbers for its `Mol`, so
`rewrite` and `plain` refuse it. It is one of the test texts.

## 10. What is proven, and how it is tested

`CLAIMS.md` has both: every theorem about the program, with its number and
its name in Lean; what the theorems say together, and what they do not say;
every check, with its numbers; and what has to be trusted. The exact Lean
statements stand in the files under `VeriMol/Proofs/`, and the ledger,
`Audit/Ledger.lean`, lists them, each with a fingerprint of its statement.

## 11. What the program is compared with

The Lean program is compared with a second program that follows this
document, and with other programs that read SMILES. Section 11.1 names them.
Section 11.2 lists where this program and RDKit read a text differently.
`CLAIMS.md` says what the comparisons found.

### 11.1 The reference material

The folder `reference/` holds what the program is checked against. None of
it is part of the program, and `lake test` does not need it.

| What | Its part |
|---|---|
| `reference/model.py` | This document as a Python program: the reader with every error message, the stereo facts, both spellings with their marks, the chosen form, what the program writes, the printed layout and the filter. The Lean program must give the same answer as the model, text by text. |
| RDKit 2024.03.3 | With its clean-up switched off it reports what is written. It judges the reader atom by atom. It reads each text that the writer makes from the real texts, and from the random `Mol`s of the checks that have no stereo facts, as the `Mol` that was written, apart from a mass number 0, which it does not keep. It does not read every text that the writer can make so: a mass number from 65,536 on comes back as another number, or the text is refused (section 11.2). For the filter it is asked with its clean-up on: the size of the largest perfluorinated group that a search written for it finds in each real text is held against the size that the filter names (section 16). |
| Open Babel 3.1.1 (as the Python package `openbabel-wheel` 3.1.1.23 brings it; `reference/README.md`) | A second, independent reader. It is asked where the model and RDKit disagree. Beside RDKit it reads every real text, and what the program writes for it with `rewrite` and `plain`. And its own record of the stereo marks is what the stored stereo facts are held against. |
| partialsmiles 2.0 | A strict reader. Here it is asked only whether a text is grammatical SMILES. |
| the OpenSMILES specification | The text this document was written from: version 1.0, as its repository had it on 2 April 2026. |
| 62,099 real SMILES texts | Seven public collections: the 4,900 different texts of the extract of the NCI Open Database that RDKit ships, and the MoleculeNet sets HIV, Tox21, Lipophilicity, BBBP, ClinTox and SIDER. |

Every fetched file has a recorded checksum. `reference/README.md` says how to
fetch the files and how to run each check.

The tests that `lake test` runs use the SMILES texts that this document
quotes as examples (every quoted text that is read, and every text that is
given with the position of its problem), further texts written for the
tests, and 100 of the NCI texts. `reference/test_cases.py` lists them, and
`reference/check_tests.py` writes their expected results, as the model gives
them, into `TestData.lean`.

### 11.2 Where this program and RDKit differ

RDKit is asked with its clean-up switched off (`sanitize=False`), so that it
also reports what is written. There are three kinds of difference. The lists
below were compared with 344,672 random and damaged texts, and no other kind
turned up among them. Those texts are made from a fixed set of pieces, which
holds a piece for every kind that is named here, in the tables and in the
paragraph below them. A kind of difference that needs yet another piece
cannot show among them.

**Both read the text, but differently.** These are the exceptions to "the
reader agrees with RDKit, atom by atom" that were found:

| Text | This program | RDKit |
|---|---|---|
| `[0C]` | isotope 0 is kept (OpenSMILES tells an isotope of 0 from no isotope) | no isotope: an isotope of 0 stands for "none given" |
| `CN(C)(C)C` | a bare nitrogen whose bonds add up to 4 has 1 hydrogen | 0 |
| `FP(F)(F)(F)(F)F` | a bare phosphorus whose bonds add up to 6 has 0 hydrogens | 1 |
| `CIC` | a bare iodine whose bonds add up to 2 or 4 has 0 hydrogens | 1 |
| `C:C` | an aromatic bond of an uppercase atom counts 1: 3 hydrogens each | it counts one and a half: 2 each |
| `c` | a lowercase atom gets one hydrogen fewer also when it has no aromatic bond: 3 | it does not: 4 |

For atoms with up to four bonds the five rows about hydrogens are all that
was found: in the 2,016 cases of section 5 (rule 7), RDKit counts differently
only in these five situations, and Open Babel counts as this program does in
all of them. The spelling with round brackets never writes a bare atom in one
of the five situations (section 9.2). In every written text that was tried,
RDKit read the hydrogens as this program does.

**This program reads the text, RDKit does not.** All four are within the
grammar of OpenSMILES, which puts no limit on the digits of a mass number.

| Text | What it is |
|---|---|
| `[013C]` | an isotope that starts with 0: isotope 13 |
| `C%01CC1` | a ring number written with `%0`: ring number 1 |
| `C(.C)C` | a branch that starts with a dot |
| a mass number of 20 digits | This program keeps the number that is written, however long it is (section 4.1). RDKit refuses one of that length, and so does Open Babel. One of the test texts has it. |

**This program refuses the text, RDKit reads it.**

| Text | What it is |
|---|---|
| `C C` | white space. RDKit reads `C` and ignores the rest, as OpenSMILES says. |
| `[HH]`, `[CH10]` | a hydrogen count on a hydrogen atom, or one of two digits |
| `C=1CC-1` | a ring bond whose two ends name different bonds. RDKit keeps the symbol that is written first: here a double bond, and a single one for `C-1CC=1`. |
| `C(C)1CC1` | a ring number behind a branch |
| `[te]`, `[si]` | lowercase symbols that OpenSMILES does not have |
| `*`, `[CH3:1]` | the wildcard atom and atom classes |
| `N->[Fe]` | `->` and `<-`, which RDKit writes for bonds to metals |
| `[C+100]` | a charge of three digits. Open Babel reads it too. |
| `C~C` | `~`, which stands for any bond in the pattern language SMARTS |
| `Cé`, `C²` | a character from outside ASCII. RDKit reads `C` and ignores the rest, as it does behind white space. |

The differences in texts with stereo marks stand in section 12.4.

Known as well, and in no table because no test text shows them: a mass number
from 65,536 to 2,147,483,639, of which RDKit keeps the remainder after
division by 65,536 (for the mass number 65,549 it reports 13), while it
refuses every larger one, as the row of 20 digits says; a charge with a zero
in front, which this program reads and RDKit refuses; an atomic number in
square brackets behind `#`, and a ring number in round brackets behind `%`,
which RDKit reads and this program does not; and the old names of the
elements 110 to 118, from Uun to Uuo, which RDKit reads and this program
does not.

What the program does with the 62,099 real texts, of which 4,550 carry stereo
marks:

- 62,075 texts are read: 57,547 without stereo marks and 4,528 with. For
  62,070 of them RDKit reads exactly the same atoms and bonds. In the other 5
  a bare atom has other hydrogens, in one of the situations of the first
  table above.
- 24 texts are refused, although RDKit reads them: 16 have a stereo centre
  with a free place in the second of the two spellings that rule 9 refuses,
  with one ring number and only single bonds (section 12.2), 5 have two
  direction marks in a row (section 12.4), 2 contain `[te]` and 1 contains
  `*`.

## 12. Stereo marks

The marks `@`, `@@`, `/` and `\` say how a molecule is arranged in space:
which of two mirror images an atom with four different neighbours is, and on
which sides of a double bond the neighbours of its two atoms lie. The program
reads them, stores what they say in the `Mol`, and writes them back. This
section adds them to sections 3 to 9: what is stored (12.1), the rules for
reading (12.2) and for writing (12.3), and what is not covered (12.4).

What is proven about the stereo facts, and how they were checked, stands in
`CLAIMS.md`. In short: both spellings are read back as exactly the `Mol` that
was written, with its stereo facts (theorems 11 and 12). No theorem says that
the reader gives the stereo facts of rules 8 to 10 for every text: there are
three examples (theorem 38). Beyond them it is tested: what the Lean program
stores is what the model of section 11.1 stores, and for the real texts that
is what Open Babel's own record of the marks says, and what is measured on
coordinates in space that RDKit builds, wherever that can be compared.

### 12.1 Two lists of stereo facts, and two statements

The marks are spelling: what a mark means depends on the order in which the
text writes the atoms. The `Mol` stores the fact instead, said with atom
numbers, in two lists beside its atoms and its bonds (section 3 has the
definitions). `orientations` lists the atoms that have an orientation, and
`geometries` the double bonds that have a geometry, each with one mark:
`anticlockwise` or `clockwise` for an atom, `sameSide` or `oppositeSides`
for a double bond.

**Orientation of an atom.** An atom with an orientation has four places around
it. Its neighbours fill three or four of them. If there are only three, the
fourth place holds the atom's own hydrogen, or stays free if it has none. The
**fixed order** of the places is: that fourth place first, and then the
neighbours in increasing atom number. Seen from the first place towards the
atom, the other three follow each other anticlockwise or clockwise. That is
the stored mark.

**Geometry of a double bond.** `a` and `b` are its two atoms, the smaller
number first, as in a `Bond`. Take, for each of the two, the lowest-numbered
neighbour other than the partner. The stored mark says whether these two
neighbours lie on the same side of the double bond or on opposite sides.

So a stored mark is said for one fixed choice, and that choice depends on how
the atoms are numbered. What does not depend on the numbering are **two
statements** (in Lean, two functions), which are worked out from the marks:

```lean
-- A place around an atom: a neighbour, or `none` for the fourth place.
abbrev Place := Option Nat

-- The places of an atom in the fixed order.
def Mol.places (m : Mol) (atom : Nat) : List Place :=
  (if (m.neighbours atom).length = 3 then [none] else []) ++ (m.neighbours atom).map some

-- 0 for the fourth place, and for a neighbour its atom number plus 1.
def placeCode : Place → Nat
  | none => 0
  | some atom => atom + 1

-- The number of pairs of a list that stand in falling order.
def fallingPairs : List Nat → Nat
  | [] => 0
  | x :: rest => (rest.filter (· < x)).length + fallingPairs rest

-- The stored marks.
def Mol.orientationAt (m : Mol) (atom : Nat) : Option Orientation :=
  (m.orientations.find? fun x => x.atom == atom).map (·.orientation)
def Mol.geometryAt (m : Mol) (a b : Nat) : Option Geometry :=
  (m.geometries.find? fun x => x.a == a && x.b == b).map (·.geometry)

-- The first statement.
def Mol.orientationOf (m : Mol) (atom : Nat) (places : List Place) : Option Orientation :=
  match m.orientationAt atom with
  | none => none
  | some stored =>
    if places.Perm (m.places atom) then
      some (stored.turnedIf (fallingPairs (places.map placeCode) % 2 == 1))
    else none

-- The second statement.
def Mol.geometryOf (m : Mol) (a b x y : Nat) : Option Geometry :=
  match m.geometryAt (min a b) (max a b) with
  | none => none
  | some stored =>
    if (m.otherNeighbours a b).contains x && (m.otherNeighbours b a).contains y then
      some (stored.turnedIf
        (((m.otherNeighbours a b).head? == some x) != ((m.otherNeighbours b a).head? == some y)))
    else none
```

`turnedIf` gives the other mark if its argument is true, and the same mark
otherwise. `places.Perm l` says that `places` holds the entries of `l` in
some order.

- **`m.orientationOf atom places`**: seen from the first of `places` towards
  `atom`, the other three follow each other so. `places` are the four places
  of the atom in any order. The answer is the stored mark if an even number
  of swaps leads from the fixed order to `places`, and the other mark if an
  odd number does. Whether that number is even or odd is counted as the
  number of pairs of `places` that stand in falling order. `none` if the atom
  has no orientation, or if `places` are not its four places.
- **`m.geometryOf a b x y`**: `x`, a neighbour of `a`, and `y`, a neighbour
  of `b`, lie so to the double bond between `a` and `b`. For the two
  lowest-numbered neighbours the answer is the stored mark, and the other
  neighbour of an atom lies on the other side. `a` and `b` may be given in
  either order. `none` if that bond has no geometry, or if `x` or `y` is no
  such neighbour.

An example. Alanine, `N[C@@H](C)C(=O)O`, is read with the orientation
`anticlockwise` at atom 1 (rule 9 below shows why). The fixed order of the
places of atom 1 is its hydrogen and then the atoms 0, 2 and 3. So
`orientationOf 1 [none, some 0, some 2, some 3]` is `anticlockwise`. For the
order in which the text writes the places, `[some 0, none, some 2, some 3]`,
it is `clockwise`, which is what `@@` says. For three places it is `none`.

Who uses what:

- The reader works the marks out from the text (12.2), and the writer says
  them back for the order in which it writes (12.3). Both turn a mark round
  by counting swaps, as the first statement does.
- "The same molecule, numbered differently" (section 3.1) says that the two
  statements carry over to the new numbers. It does not mention the stored
  marks.
- The function that puts the atoms of a `Mol` into a new order, and with it
  the chosen form (section 3.2), asks the two statements for the new marks.
- A later check, or a reader for another notation, can ask the two
  statements without knowing the fixed order.

Section 3 says what being well formed asks of the two lists.

### 12.2 Reading

The grammar of section 4 grows by the marks:

```
bond          ::= '-' | '=' | '#' | '$' | ':' | '/' | '\'
bracket_atom  ::= '[' isotope? symbol chiral? hcount? charge? ']'
chiral        ::= '@' | '@@'
```

The rules of section 5 stay as they are: the marks change nothing in the
atoms and the bonds that are read. Three rules are added.

8. **Direction marks.** `/` and `\` stand where a bond symbol can stand. The
   bond gets the order it would have without a symbol (rule 5), and also a
   direction. Written at atom X for its bond to atom Y, `/` says that Y lies
   above X, and `\` that Y lies below X. For a bond along the text (rule 3), X
   is the earlier of the two atoms. For a ring number, X is the atom the
   number is written at. So `F/C=C/F`, `F/C=C/1.F1` and `F/C=C1.F\1` say the
   same. A ring bond may carry a mark at both ends if the two say the same,
   which means one `/` and one `\`: OpenSMILES spells cyclooctatetraene
   `C/1=C/C=C\C=C/C=C\1`. Where a ring bond carries a mark at both ends, the
   mark at the number that opens the ring is the one whose position a message
   names. A mark at one end and another bond symbol at the other is an error.
9. **Orientation.** `@` means anticlockwise and `@@` clockwise, for the four
   places of the atom in the order in which the text writes them: first the
   earlier atom it is bonded to along the text (rule 3), if there is one; then
   its own hydrogen or the free place; then its ring numbers in the order
   written; then the later atoms it is bonded to along the text, in the order
   written. The reader restates this for the fixed order of 12.1: if an odd
   number of swaps turns one order into the other, the orientation is the
   opposite one. In `N[C@@H](C)C(=O)O` the text writes the places of atom 1 in
   the order atom 0, hydrogen, atom 2, atom 3. One swap leads to the fixed
   order, so `@@`, clockwise, is stored as `anticlockwise`.

   An atom with `@` or `@@` that does not have four places (12.1) is an
   error. Two more errors are about an atom with a free place:

   - The text bonds it to no earlier atom along the text (rule 3). A ring
     number to an earlier atom does not count: `C1.[S@]1(C)=O` gets this error
     as well. OpenSMILES does not say where the free place then stands, and
     programs disagree: RDKit reads `[S@](C)(=O)CC` as `C[S@](=O)CC`, and Open
     Babel reads it as the mirror image. With an earlier atom the free place
     comes second, as a hydrogen does.
   - Exactly one ring number is written at the atom, and all bonds of the atom
     are single, as at the nitrogen of `C[N@]1CC1C` and at the sulfur of
     `C[S@+]1CCCC1`. Here the programs disagree as well: Open Babel reads the
     free place second, and RDKit reads it the other way round (12.4). So the
     text does not say which of the two is meant, and the program does not
     read the mark. Its writer never writes an atom so (12.3).

   Everywhere else the free place is read second: with no ring number at the
   atom, as in `C[S@+](CC)CCC`, with two, as in `CC1CCC2CC[S@+]12`, and with a
   double bond at the atom, as in `O=[S@]1CC[C@H](C)C1`. There RDKit read every
   text that was tried in the same way, and so did Open Babel wherever it
   keeps the mark (12.4).
10. **Geometry.** A double bond can have a geometry when each of its two atoms
    has one or two neighbours other than the partner. It gets one when, at
    each of its two atoms, at least one bond to such a neighbour carries a
    mark. Two neighbours, one at each atom, are on the same side of the double
    bond when both lie above their atom or both lie below, and on opposite
    sides otherwise. The reader states this for the two lowest-numbered
    neighbours of 12.1: where the marked neighbour is not the lowest-numbered
    one of its atom, the lowest-numbered one lies on the other side.

    Two things are errors. Marks contradict each other when a double bond gets
    a geometry and two neighbours of one of its atoms are marked to the same
    side; OpenSMILES calls such a text invalid. And a mark must not stand
    alone: every mark has to take part in the geometry of at least one double
    bond. In `C/C=CC` only one atom of the double bond has a marked bond, so
    the text does not say which of the two forms is meant. OpenSMILES says
    that the marks always come in pairs.

The errors of the marks, in the form of section 6:

| Message | Examples, with the position |
|---|---|
| `this stereo class is not read`, for `@` followed by `TH`, `AL`, `SP`, `TB` or `OH` (position of the `@`) | `C[C@TH1](F)(Cl)Br` (3) |
| `the two ends of ring 1 name different directions` | `F/C=C/1.F/1` (10) |
| `this atom cannot be a stereo centre` (position of the `@`) | `F[C@H2]Cl` (3), `C[C@](F)(Cl)(Br)I` (3) |
| `a stereo centre with a free place needs an atom before it` (position of the `@`) | `[S@](C)(=O)CC` (2) |
| `a stereo centre with a free place, one ring number and only single bonds is not read` (position of the `@`) | `C[N@]1CC1C` (3), `C[S@+]1CCCC1` (3) |
| `these marks contradict each other` (position of the later of the two marks) | `C/C(\F)=C/F` (4) |
| `this mark has no partner on the other side of a double bond`, for a mark that takes part in no geometry | `C/C` (1), `C/C=CC` (1), `F/C=C=C=C/F` (1) |

The message `the two ends of ring 1 name different bonds` of section 6 also
covers a mark at one end and another bond symbol at the other: `C/1CC=1` (6).
A direction mark is a bond symbol for the table "What may come next" and for
the messages of the end of the text (section 6): `C/` gets
`the text ends after a bond symbol`. Of two marks in a row the second is out
of place: after an atom or a ring number, as in `F\\C=C/F`, it gets
`an atom or a ring number is expected here`, and after `(` or `)` it gets
`an atom is expected here`.

The first message belongs to the characters and bracket atoms of section 6,
and the second to the structure: among the ring messages of section 6 it is
checked after the one about different bonds and before
`these two atoms are already bonded`. `C/1C/1` fits this message and
`these two atoms are already bonded`, and gets this one. The last five are
looked for when the text has no other problem, and of several the one with
the smallest position is reported. For one atom they are asked in the order
of the table.

### 12.3 Writing

Both spellings of section 9 write the atoms and the bonds as they do for a
`Mol` without stereo facts. The marks are added to them.

- **Orientation.** An atom with an orientation is written in square brackets,
  with `@` or `@@`. Both spellings write the places of an atom in this order:
  the earlier atom it stands next to, if there is one; its own hydrogen or
  the free place; its ring numbers, which stand in increasing order of the
  other atom's number; the later atoms that stand next to it, in increasing
  order. The writer compares this order with the fixed order of 12.1, as the
  reader does (rule 9).
- **Which bonds are marked.** For every double bond with a geometry, one bond
  at each of its two atoms: the bond to the lowest-numbered other neighbour
  whose bond can carry a mark. A bond can carry a mark when its order is the
  one a missing symbol means (rule 5).
- **Which mark.** A mark takes the place of the bond symbol. Both spellings
  write every bond at its lower-numbered atom, so `/` says that the
  higher-numbered atom lies above the lower-numbered one. The marks are chosen
  so that reading them gives every geometry back (rule 10), and so that two
  marked bonds at one atom of a double bond with a geometry point to opposite
  sides. Marks that depend on each other form a group. In each group the bond
  that comes first in `bonds` is written `/`, which fixes the others.

`C[C@H](F)/C=C/Cl` is written `C[C@H](F)/C=C/Cl` with round brackets and
`[CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl]` in the plain spelling. A text need not
come back with the marks it had: `F\C=C\F` comes back as `F/C=C/F`, and
`F/C(/F)=C/F`, which marks two bonds at one atom, as `F/C(F)=C/F`.

Besides the cases of section 9.4, the writer refuses a `Mol` with stereo
facts in five cases, each with a message of its own:

- an atom with an orientation and a free place would be written without an
  earlier atom next to it (rule 9):
  `a stereo centre with a free place would be written without an atom before it`;
- such an atom would be written with exactly one ring number while all its
  bonds are single (rule 9):
  `a stereo centre with a free place would be written with one ring number and only single bonds`;
- at one atom of a double bond with a geometry, no bond to another neighbour
  can carry a mark:
  `at one atom of a double bond with a geometry, no bond can carry a mark`;
- the marks would give a geometry to a double bond that has none:
  `the marks would give a geometry to a double bond that has none`;
- no choice of marks gives every geometry:
  `no choice of marks gives every geometry`.

The first two are about where a spelling writes an atom, so the two spellings
can differ in them. `C[S@+](CC)CCC` is read, and `rewrite` writes it back. The
plain spelling writes one of the three bonds of its sulfur with a ring
number, and `plain` answers with the second message.

The writer asks in this order: whether the `Mol` is well formed; its atoms
(section 9.4); which bonds carry a mark, where the last three messages can
come, in the order of the list; and then, atom by atom in the order of their
numbers, whether an atom with an orientation can be written where it stands
(the first two messages, in that order) and whether its ring numbers are free
(section 9.4).

The third and the fourth case are limits of this simple way of choosing the
bonds, and of the rule that only a bond without a symbol can carry a mark.
Both can come for a `Mol` that the reader returned. The text it was read
from shows a choice of marks, but not always one that the writer can use: the
writer writes an atom with an aromatic bond in lowercase (section 9), and a
single bond between two lowercase atoms needs its symbol, so it can carry no
mark. `c1ccccc1/C(:F)=C/F` is read, and both spellings refuse its `Mol` with
the third message. `F/C=C(/c1ccccc1):C=C/C=C/F` is read, and both refuse its
`Mol` with the fourth. Both texts have an aromatic bond written `:` at an
atom outside a ring, which no real text has. With the real texts neither case
occurred (`CLAIMS.md`).

The fifth case can be a limit of the notation itself, which the OpenSMILES
document points out for this very ring. In the ring of
`C/1=C/C=C\C=C/C=C\1` each of the four single bonds carries the mark for the
double bonds on both of its sides. So the marks cannot say every combination
of the four geometries. The `Mol` of that text with the geometry of its
first double bond turned round is well formed, and both spellings refuse it
with the fifth message. It is one of the test `Mol`s.

The fifth case can also come for a `Mol` that the reader returned, where the
text marks other bonds than the writer chooses. `F/C1=C(/F)C(/F)=C1/F` is
read: it marks the four bonds to fluorine. For its second double bond the
writer marks the two single bonds of the ring, each of which stands at an
atom of the first double bond as well. Marked so, the bonds cannot say the
two geometries that the text says, and both spellings refuse the `Mol` with
the fifth message. With the real texts this case did not occur.

### 12.4 Not covered

- The stereo classes written with letters (`@TH1`, `@AL1`, `@SP1`, `@TB1`,
  `@OH1` and so on). They are an error.
- `@` and `@@` at an atom with five or six neighbours, which OpenSMILES reads
  as a short form of two of these classes, as in its example
  `C[Co@](F)(Cl)(Br)(I)S`. Such an atom does not have four places, so the
  mark is an error (rule 9).
- Stereo along several double bonds in a row: the marks in `F/C=C=C=C/F`, and
  `@` on the middle atom of `C=C=C`. Both are an error, by rules 9 and 10.
- Whether a mark says anything. `Br[C@H](Br)C` and `F/C(/F)=C/F` are stored as
  written, although their atom and their double bond exist in one form only.
  `Br[C@H](Br)C` and `Br[C@@H](Br)C` are two `Mol`s, and they are the same
  molecule, numbered differently (section 3.1): exchanging the two bromine
  atoms turns the one into the other. So `canonical` gives both the same
  text, `C[C@@H](Br)Br`, which still carries a mark. Leaving out a mark that
  says nothing belongs to later work on conventions (section 13).
- Stereo that SMILES cannot express.

Known differences from RDKit 2024.03.3, which reads all of these texts:

| Text | This program | RDKit |
|---|---|---|
| `C/C`, `C/C=CC`, `F/C=C=C=C/F` | error | the marks are ignored |
| `C/C(\F)=C/F` | error | the marks are ignored |
| `F/C=C/1.F/1` | error | read as `F/C=C\F` |
| `C/1CC=1` | error | read as `C1=CC1` |
| `F[C@H2]Cl` | error | the mark is ignored |
| `C[C@TH1](F)(Cl)Br` | error | read as `C[C@](F)(Cl)Br` |
| `F\\C=C/F` | error | read |
| `[S@](C)(=O)CC` | error | read as `C[S@](=O)CC` |
| `C[N@]1CC1C`, `C[S@+]1CCCC1` | error | read. Open Babel reads the mirror image of what RDKit reads. |

The last row is the second error of rule 9: an atom with an orientation and a
free place, at which exactly one ring number is written and whose bonds are
all single. Open Babel 3.1.1 reads the free place second there, as in every
other text that was tried in which it keeps the mark. RDKit 2024.03.3 reads it
the other way round. That was seen on 580 texts for small molecules of this
kind (no check of the repository repeats that count): a nitrogen in a ring of
three, sulfur with a charge, phosphorus, arsenic and selenium with a charge.
Where both programs keep the mark, which in these texts is at nitrogen and at
sulfur, they read mirror images of each other. Two of the texts have a second
marked atom, so that the two readings are two different molecules
(`reference/check_spec.py` checks these two): RDKit reads `C[N@]1C[C@H]1C` as
the molecule that Open Babel reads from `C[N@@]1C[C@H]1C`, and
`C[S@+]1CC[C@H](C)C1` as the molecule that Open Babel reads from
`C[S@@+]1CC[C@H](C)C1`. RDKit also writes such texts itself, and reads them
back as the molecule it wrote. So a text of this kind means one arrangement at
that atom to RDKit and the opposite one to Open Babel, and the program refuses
it. 16 of the real texts are refused for such an atom, each time a nitrogen.
And the writer refuses a spelling that would write an atom so (12.3): no text
that this program writes has the form that the two programs read differently.

Where the program reads an atom with a free place, both programs agreed with
it, in every text that was tried, wherever they keep the mark at all.
Neither keeps a mark at every kind of atom: in the texts that were tried,
RDKit kept none at a nitrogen outside a ring of three, and Open Babel none at
phosphorus, arsenic and selenium. For these three elements only RDKit is a
second opinion.

Of the 4,550 real texts with stereo marks, the program refuses 22 that RDKit
reads: the 16 of the last row, 5 that contain two marks in a row, like
`F\\C=C/F`, and 1 that contains `*`. Of the random spellings by RDKit that the
checks make for the texts with stereo marks (`CLAIMS.md`, "What the checks
found for stereo marks"), it refuses 9: 6 contain `->` or `<-`, which RDKit
writes for bonds to metals, and 3 contain `*`.

RDKit's writer leaves out a mark that tells nothing apart, which is the usual
convention: it writes `Br[C@H](Br)C` as `CC(Br)Br`. This program does not judge
marks and writes back the mark that it read; leaving such a mark out belongs
to later work (section 13).

## 13. Not part of this program

Not part of this document, and none of it is needed for the theorems of
`CLAIMS.md`:

- chemistry checks by the reader and the writers: valences, aromatic rings
  that cannot have alternating bonds, aromatic bonds outside rings. The filter
  asks a usual valence of every atom, and no other command does (section
  16.2); what it asks about aromatic bonds is less than these two points;
- bringing a molecule to one convention: written-out hydrogens, aromatic or
  alternating bonds, stereo marks that say nothing;
- one text for a molecule in the sense of a chemist: the chosen form of
  section 3.2 is one text for every numbering of a `Mol`, where the search
  finds it, and it needs the conventions of the point before to become
  one text for every way of writing a molecule;
- further filters, beyond the filter of section 16 and its one rule.

## 14. Left open

- Whether `app` should one day read a file of SMILES texts. Today it takes
  one text from its arguments. Where a check needs the answers to very many
  texts, it asks a second small program, which is a tool of the checks and
  not the program (`CLAIMS.md`). Reading a file would be a new ability for
  `Main`, which only hands the arguments on and prints the answer.

## 15. The element symbols

The 118 symbols that are read inside square brackets, in the order of the
atomic numbers. The Lean type `Element` has one case for each, named like the
symbol.

```
H  He Li Be B  C  N  O  F  Ne Na Mg Al Si P  S  Cl Ar
K  Ca Sc Ti V  Cr Mn Fe Co Ni Cu Zn Ga Ge As Se Br Kr
Rb Sr Y  Zr Nb Mo Tc Ru Rh Pd Ag Cd In Sn Sb Te I  Xe
Cs Ba La Ce Pr Nd Pm Sm Eu Gd Tb Dy Ho Er Tm Yb Lu Hf
Ta W  Re Os Ir Pt Au Hg Tl Pb Bi Po At Rn Fr Ra Ac Th
Pa U  Np Pu Am Cm Bk Cf Es Fm Md No Lr Rf Db Sg Bh Hs
Mt Ds Rg Cn Nh Fl Mc Lv Ts Og
```

## 16. The filter

The command `filter` stands between a proposal for a molecule and whoever is to
act on it. The proposal is a SMILES text. The filter hands on the `Mol` of the
text, and it does so only if that `Mol` is sound and a rule holds for it.
Anything else it refuses, with the reason. One rule is built, under the name
`perfluoro`: the `Mol` has no perfluorinated group of a given size or more.

```
$ app filter perfluoro 6 'CC(=O)O'
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
$ app filter perfluoro 6 'OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F'
error: the Mol has a perfluorinated group of size 7, and size 6 or more is refused
$ app filter perfluoro 6 'C[N+](=O)[O-]'
error: the Mol is not sound: atom 1 has a charge
```

The first text is acetic acid, the second perfluorooctanoic acid, PFOA, and
the third nitromethane, written with charges.

### 16.1 Three questions

The command has four arguments: the word `filter`, the name of the rule, a
number and the text. The number is the size from which a perfluorinated
group is refused. It is written with one or more of the digits `0` to `9`
and nothing else, and it is not 0: `6`, `12` and `006` are such numbers, and
`0`, `00`, `+6`, `6.0` and an argument without a character are not. Four
arguments of any other form get the error about the arguments (section 8).

The filter asks three questions in this order, and the first that is answered
with no gives the error.

1. **Is the text read?** If not, the error is the reader's, with its
   position (sections 6 and 12.2).
2. **Is the `Mol` sound?** Section 16.2. If not, the error names the first
   atom that fails, and what it fails.
3. **Does the rule hold?** Section 16.3. If not, the error names the size of
   the largest perfluorinated group.

If all three are answered with yes, the `Mol` is printed in the layout of
section 7, and the exit code is 0. So the filter prints for a text exactly
what the program prints for the text alone, or an error. The empty text is
read as the `Mol` without atoms (section 4). That `Mol` is sound, because it
has no atom that could fail a test, and it has no group: the filter hands it
on.

What the filter hands on is the `Mol`, and what the command prints is its
printed layout. A printed `Mol` that passed the filter looks like any other
printed `Mol`: that it passed is said by the exit code of the command, and
by nothing on the page.

Soundness is asked once, before the rule, and it is no part of the rule. A
rule is a statement about the structure of a compound, and it says
something about a `Mol` only if the `Mol` can stand for a compound.

### 16.2 Sound

A `Mol` is sound when it is well formed (section 3) and each of its atoms
passes five tests.

1. **Its element** is one of B, C, N, O, P, S, F, Cl, Br and I: the elements
   of the bare atoms (section 4).
2. **It has no mass number.**
3. **Its charge is 0.**
4. **It has no aromatic bond, or at least two.**
5. **Its bonds and hydrogens add up to a usual valence of its element.** The
   bonds are added up as in section 5, rule 7: single 1, double 2, triple 3,
   quadruple 4, aromatic 1. The hydrogens of the atom are added. The usual
   valences are the normal valences of that rule: 3 for B; 4 for C; 3 and 5
   for N and for P; 2 for O; 2, 4 and 6 for S; 1 for F, Cl, Br and I. For an
   atom with aromatic bonds the sum may also be one below a usual valence:
   counted as 1 each, its aromatic bonds leave out its share of the double
   bonds of the ring.

The `Mol` is asked first whether it is well formed. Then its atoms are gone
through in the order of their numbers, each with the five tests in their
order, and the first test that an atom fails gives the message:

| What fails | Message, here for atom 3 |
|---|---|
| the `Mol` is not well formed | `the Mol is not well formed` |
| test 1 | `the Mol is not sound: atom 3 is no atom of B, C, N, O, P, S, F, Cl, Br or I` |
| test 2 | `the Mol is not sound: atom 3 has a mass number` |
| test 3 | `the Mol is not sound: atom 3 has a charge` |
| test 4 | `the Mol is not sound: atom 3 has exactly one aromatic bond` |
| test 5 | `the Mol is not sound: the bonds and hydrogens of atom 3 add up to no usual valence of its element` |

The number is that of the atom in the `Mol`, counted from 0, and not a
position in the text. The first message never comes from the command: a
`Mol` that the reader returned is well formed (theorem 8).

Examples:

- `c1ccccc1`, benzene, is sound. Each of its atoms has two aromatic bonds
  and one hydrogen, which add up to 3, one below 4. So is `C1=CC=CC=C1`,
  where each atom comes out at 4.
- `c1ccncc1`, pyridine, is sound: its nitrogen atom comes out at 2, one
  below 3. `c1cc[nH]c1`, pyrrole, is sound: its nitrogen atom comes out at
  3. `c1ccoc1`, furan, is sound: its oxygen atom comes out at 2.
- `N[C@@H](C)C(=O)O` is sound. Stereo facts are not looked at, beyond what
  "well formed" asks of them.
- `[CH4]` is sound, and it is the `Mol` of `C`: square brackets are spelling
  (section 3).
- `CN(=O)=O`, nitromethane with a nitrogen atom of valence 5, is sound.
  `C[N+](=O)[O-]`, the same compound written with charges, is not: its atom
  1 has a charge. The usual way of writing a compound can fail a test.
- `[Na+].[Cl-]` is not sound: atom 0 is no atom of the ten elements. The
  first test comes before the third.
- `[13CH4]` is not sound: it has a mass number.
- `[H]C([H])([H])[H]` is not sound: its atom 0 is a hydrogen atom. In a
  sound `Mol` every hydrogen is a count on its atom.
- `C:C` is not sound: each atom has exactly one aromatic bond. Neither is
  `FC(F)(F):c1ccccc1`, for its atom 1.
- `CC(F)(F)(F)F` is not sound: the bonds of atom 1 add up to 5.
- `[CH3]`, a carbon atom with three hydrogens and nothing else, is not
  sound: 3 is no usual valence of carbon.
- `C1CC1.C1CC1` is sound: the pieces of a `Mol` need not be connected.

"Sound" is narrow on purpose. It says of which `Mol`s the rule is asked, and
a `Mol` that is not sound is not thereby a wrong one. It is also no proof
that a compound exists: the five tests look at one atom at a time. Whether
the aromatic bonds of a `Mol` close rings, and whether such a ring can be
written with single and double bonds in turn, is not asked. `c1cccc1`, a
ring of five carbon atoms with one hydrogen each, is sound, and no ring of
single and double bonds in turn has that shape. And the usual valences are
those of section 5: `CN(C)(C)(C)C`, a nitrogen atom with five single bonds,
is sound, because 5 is a usual valence of nitrogen.

### 16.3 The rule `perfluoro`

A perfluorinated group is made of carbon atoms of two kinds.

**Five conditions.** Every carbon atom of a perfluorinated group meets all
of these:

- it is a carbon atom;
- no hydrogen is counted on it;
- none of its bonds is a double, triple or quadruple bond: each is a single
  bond or an aromatic bond;
- it has exactly four bonds, so it is bonded to four atoms;
- none of the four is a hydrogen atom.

The fifth condition names hydrogen alone. What else the atom is bonded to is
not looked at: a carbon atom of any kind, oxygen, nitrogen, sulfur, chlorine,
bromine or iodine, for example.

**A fluorinated carbon atom** meets the five conditions, and at least one of
the four atoms that it is bonded to is a fluorine atom.

**A branch carbon atom** meets the five conditions, and at least three of
the four atoms that it is bonded to are carbon atoms of a perfluorinated
group. It stands where a group branches, and it need not carry fluorine
itself: the atom in the middle of (CF3)3C– is one. An atom can be of both
kinds.

**The carbon atoms of the perfluorinated groups** of a `Mol` are its
fluorinated carbon atoms and its branch carbon atoms. They are worked out
from the fluorinated carbon atoms inwards. Every fluorinated carbon atom is
one. Then an atom that meets the five conditions and is bonded to at least
three atoms which are such atoms already is one as well, and this is
repeated until it adds no atom. So a branch carbon atom can be one of the
three that hold the next, and no atom is counted unless fluorinated carbon
atoms stand behind it.

**Linked.** Two carbon atoms of the perfluorinated groups are linked when
one can be reached from the other by going along bonds, from one such atom
to the next. Each of them is linked to itself.

**A perfluorinated group** is one of these atoms together with every atom
that is linked to it. Its size is the number of its atoms: carbon atoms
only, the fluorine atoms are not counted. Each of these atoms belongs to
exactly one group.

**The rule.** With the number 6 behind `perfluoro`: the `Mol` has no
perfluorinated group of 6 or more carbon atoms. If the largest group of the
`Mol` has 6 atoms or more, the filter refuses with

```
error: the Mol has a perfluorinated group of size 7, and size 6 or more is refused
```

where the first number is the size of the largest group of the `Mol`, and
the second is the number of the command, written without zeros in front.

Examples, each with the size of its largest group:

- `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F`, PFOA: 7, a
  chain.
- `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(C(F)(F)F)C(F)(F)F`, an isomer of
  PFOA with a branch: 7. No chain in it has more than six fluorinated carbon
  atoms. The atom at the branch carries one fluorine atom and belongs to the
  group: the rule is about groups, and not about chains.
- `OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F`,
  perfluorohexanesulfonic acid: 6.
- `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F`, perfluorohexanoic acid: 5.
- `FC1(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C1(F)F`, perfluorocyclohexane: 6, a
  ring.
- `Fc1(F)c(F)(F)c(F)(F)c(F)(F)c(F)(F)c1(F)F`, the same ring with its bonds
  written as aromatic: 6. This `Mol` is sound by the five tests. An aromatic
  bond counts as a single bond in the five conditions, so the spelling of a
  bond cannot hide a group.
- `FC(F)(F)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)F`, an ether: 3. Its oxygen atom
  parts a group of three from a group of two. Only bonds between carbon
  atoms hold a group together. So the size is that of the largest single
  group, and not the number of fluorinated carbon atoms of the compound.
- `FC(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F`: 5. The carbon atom in the middle
  carries no fluorine atom. It is a branch carbon atom: the four others are
  fluorinated carbon atoms, and the five are one group.
- `OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F`, an isomer of
  PFOA with such a carbon atom at its branch: 7. Its three –CF3 hold it,
  and it joins them to the chain of three.
- `OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F`, the isomer of
  PFOA with two such atoms side by side: 7. The outer one is held by its
  three –CF3, and the inner one by the outer one and its own two –CF3.
- `Oc1ccc(cc1)C(c1ccc(O)cc1)(C(F)(F)F)C(F)(F)F`, bisphenol AF: 1. The
  carbon atom between its two –CF3 is bonded to two carbon atoms of a group
  only. It is no branch carbon atom, and the two –CF3 are two groups of one.
- `FC(F)(F)C12C3(C(F)(F)F)C4(C(F)(F)F)C1(C(F)(F)F)C1(C(F)(F)F)C2(C(F)(F)F)C3(C(F)(F)F)C41C(F)(F)F`,
  a cube of eight carbon atoms with a –CF3 on each: 1. Each atom of the cube
  is bonded to one –CF3 and to three atoms of the cube. None of the eight is
  a branch carbon atom: they would hold each other only, and no fluorinated
  carbon atoms stand behind three bonds of any of them.
- `FC(F)C(F)(F)F`: 1. The first carbon atom has a hydrogen.
- `FC(F)(Cl)C(F)(F)F`: 2. The first carbon atom has a chlorine atom, and it
  belongs to the group all the same: chlorine, bromine and iodine are not
  looked at.
- `FC(F)(F)C(F)(F)C(F)(F)C(F)(I)C(F)(F)C(F)(F)C(F)(F)F`: 7. The carbon atom
  in the middle carries an iodine atom beside its fluorine atom, and it
  belongs to the group.
- `ClC(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)F`, a piece of
  polychlorotrifluoroethylene: 6. Every carbon atom of this chain carries
  fluorine and no hydrogen, so the chain is one group, although four of its
  atoms carry chlorine: by a formula that has fluorine atoms only, it is no
  perfluoroalkyl group. Here the reading counts more than the name says.
- `FC(F)=C(F)C(F)(F)F`: 1. Two carbon atoms have a double bond.
- `FC(F)(F)C(F)(F)F`: 2.
- `CNCCC(Oc1ccc(cc1)C(F)(F)F)c1ccccc1`, fluoxetine: 1.
- `CC(C)(C)F`: 1. One fluorine atom is enough, also where it is the only
  one of the compound and nothing is perfluorinated.
- `CC(C)Cc1ccc(cc1)C(C)C(=O)O`, ibuprofen: 0. It has no fluorinated carbon
  atom, and the filter hands it on for every number.

The filter asks the rule of a sound `Mol` only. The definitions above are
meant for a well formed `Mol`.

### 16.4 What the filter does not say

- **That a compound which passes is harmless.** The rule names one pattern
  of a structural formula. A compound can be free of it and dangerous for
  any other reason.
- **That the rule is the rule of a law or of a standard.** It is a reading
  of a wording for long chains, by which perfluoroalkyl carboxylic acids
  "with 7 or more perfluorinated carbons" and perfluoroalkane sulfonates
  "with 6 or more perfluorinated carbons" are long-chain (Buck and others,
  2011; `VeriMol/Proofs/Predicates/FluoroGroup.lean` has the source). The
  rule takes such a number for groups of any shape and in any compound, and
  it looks at the group alone. So no one number gives that wording back:
  with 7 the rule holds for the sulfonic acid above, which the wording
  counts as long-chain, and with 6 it does not hold for perfluoroheptanoic
  acid, whose group has six carbon atoms and which the wording does not
  count as long-chain. The examples above show where the reading draws its
  lines. One fluorine atom on a carbon atom without hydrogen is enough, also
  where nothing is perfluorinated, and a carbon atom that carries chlorine,
  bromine or iodine is counted like any other, so the reading takes a chain
  of a chlorofluorocarbon for a perfluorinated group, as in the example with
  four chlorine atoms above: in these two points it counts more than the
  name says. And a carbon atom without fluorine is counted only when three
  carbon atoms of a group are counted before it: not with two, as in
  bisphenol AF above, and not where such atoms would have to hold each
  other, as in the cube above. And an oxygen atom between two groups parts
  them, as in the ether above: a perfluoroether acid passes when each of
  its groups is smaller than the number, however many fluorinated carbon
  atoms it has.
- **That the `Mol` is what the text means to a chemist.** The reader follows
  this document. That this document reads SMILES as other programs do is
  tested and not proven (section 11).
- **Anything about another way of writing the compound.** The same compound
  with a hydrogen written as an atom of its own, or with charges, is another
  `Mol`, and the filter can refuse the one and hand on the other.

What is proven about the filter stands in `CLAIMS.md`, theorems 46 to 49: the
checker of soundness and the search for the groups are right, and the filter
hands on a `Mol` exactly when the text is read as that `Mol`, the `Mol` is
sound, and the rule holds.
