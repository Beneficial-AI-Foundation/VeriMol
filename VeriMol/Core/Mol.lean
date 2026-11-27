import VeriMol.Core.Element

/-!
# The `Mol`: a labelled molecular graph (SPEC.md, section 3)

A `Mol` stores facts, not spelling: its atoms, with what a SMILES text says
about each of them, its bonds, and two lists of stereo facts: the atoms that
have an orientation in space, and the double bonds that have a geometry
(SPEC.md, section 12.1). Two `Mol`s are equal when they have the same atoms in
the same order, the same bonds in the same order and the same two lists of
stereo facts. In a well formed `Mol` the order of the bonds and of the stereo
facts is fixed, so two well formed `Mol`s with the same atoms in the same
order, the same bonds and the same stereo facts are equal
(`Mol.eq_of_sameFacts` in `VeriMol/Proofs/Same.lean`).

The stereo facts stand beside the atoms and the bonds, and not in them: an
`Atom` and a `Bond` are meant to be what any notation for molecules gives, and
the two lists are empty unless a notation fills them.

The case of an atom's symbol is not stored. What a lowercase symbol says
stands in the hydrogens of the atom and in its bonds. A `Mol` says which bonds
are aromatic and not that an atom is: `hasAromaticBond` tells whether one of
the bonds of an atom is aromatic.
-/

namespace VeriMol

/-- The kind of a bond. -/
inductive BondOrder where
  | single | double | triple | quadruple | aromatic
  deriving DecidableEq, Repr

/-- One atom. -/
structure Atom where
  /-- Which element the atom is. -/
  element   : Element
  /-- The mass number if one was written, otherwise `none`. `some 0` and `none`
  are different. -/
  isotope   : Option Nat
  /-- The charge, 0 if none was written. -/
  charge    : Int
  /-- How many hydrogens are attached to the atom without being atoms of their
  own. -/
  hydrogens : Nat
  deriving DecidableEq, Repr

/-- One bond. `a` and `b` are the numbers of the two atoms it joins, the
smaller one first. -/
structure Bond where
  a     : Nat
  b     : Nat
  /-- The kind of bond. -/
  order : BondOrder
  deriving DecidableEq, Repr

/-- How the places around an atom follow each other (SPEC.md, section 12.1). -/
inductive Orientation where
  | anticlockwise | clockwise
  deriving DecidableEq, Repr

/-- On which sides of a double bond two neighbours lie (SPEC.md, section
12.1). -/
inductive Geometry where
  | sameSide | oppositeSides
  deriving DecidableEq, Repr

/-- An atom that has an orientation. The orientation is said for the fixed
order of the atom's places: its fourth place first, if it has three neighbours,
and then its neighbours in increasing atom number. Seen from the first place
towards the atom, the other three follow each other so. -/
structure AtomOrientation where
  atom : Nat
  orientation : Orientation
  deriving DecidableEq, Repr

/-- A double bond that has a geometry. `a` and `b` are its two atoms, the
smaller one first, as in `Bond`. The geometry is said for the lowest-numbered
neighbour of each of the two atoms, the partner aside. -/
structure BondGeometry where
  a : Nat
  b : Nat
  geometry : Geometry
  deriving DecidableEq, Repr

/-- A molecule, or several: the pieces need not be connected. -/
structure Mol where
  /-- The atoms. Atom number `i` is the entry at place `i`, counted from 0. -/
  atoms : List Atom
  /-- The bonds. -/
  bonds : List Bond
  /-- The atoms that have an orientation. Empty unless given. -/
  orientations : List AtomOrientation := []
  /-- The double bonds that have a geometry. Empty unless given. -/
  geometries : List BondGeometry := []
  deriving DecidableEq, Repr

/-- The atoms that atom number `atom` is bonded to. In a well formed `Mol` they
stand in increasing order. -/
def Mol.neighbours (m : Mol) (atom : Nat) : List Nat :=
  m.bonds.filterMap fun bond =>
    if bond.b = atom then some bond.a else if bond.a = atom then some bond.b else none

/-- The neighbours of `atom` other than `partner`. -/
def Mol.otherNeighbours (m : Mol) (atom partner : Nat) : List Nat :=
  (m.neighbours atom).filter (· != partner)

/-- Whether atom number `atom` has four places around it: four neighbours and
no hydrogen of its own, or three neighbours and at most one hydrogen of its
own. Only such an atom can have an orientation. -/
def Mol.hasFourPlaces (m : Mol) (atom : Nat) : Bool :=
  match m.atoms[atom]? with
  | none => false
  | some found =>
    ((m.neighbours atom).length == 4 && found.hydrogens == 0) ||
      ((m.neighbours atom).length == 3 && decide (found.hydrogens ≤ 1))

/-- Whether atom `atom` has a free place: three neighbours and no hydrogen of
its own. -/
def Mol.hasFreePlace (m : Mol) (atom : Nat) : Bool :=
  (m.neighbours atom).length == 3 &&
    (match m.atoms[atom]? with
      | some found => found.hydrogens == 0
      | none => false)

/-- Whether the atoms `a` and `b` are joined by a double bond that can have a
geometry: each of the two has one or two neighbours other than the partner.
`a` is the smaller of the two atom numbers, as in `Bond`. -/
def Mol.canHaveGeometry (m : Mol) (a b : Nat) : Bool :=
  m.bonds.contains ⟨a, b, .double⟩ &&
    ((m.otherNeighbours a b).length == 1 || (m.otherNeighbours a b).length == 2) &&
    ((m.otherNeighbours b a).length == 1 || (m.otherNeighbours b a).length == 2)

/-- A `Mol` is well formed when all of these hold:

1. Every bond joins two different atoms that exist: `a < b`, and `b` is less
   than the number of atoms.
2. The bonds are listed in increasing order, by `a` first and then by `b`, with
   no pair of atoms twice.
3. The atoms with an orientation are listed in increasing order, no atom
   twice.
4. Each of them has four places.
5. The double bonds with a geometry are listed in the order of the bonds, no
   bond twice.
6. Each of them is a double bond of the `Mol` that can have a geometry. -/
def Mol.WellFormed (m : Mol) : Prop :=
  (∀ bond ∈ m.bonds, bond.a < bond.b ∧ bond.b < m.atoms.length) ∧
  m.bonds.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)) ∧
  m.orientations.Pairwise (fun x y => x.atom < y.atom) ∧
  (∀ x ∈ m.orientations, m.hasFourPlaces x.atom = true) ∧
  m.geometries.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)) ∧
  (∀ x ∈ m.geometries, m.canHaveGeometry x.a x.b = true)

/-- Whether a `Mol` is well formed can be worked out by the program. -/
instance (m : Mol) : Decidable m.WellFormed :=
  show Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) from inferInstance

/-- Whether a `Mol` holds a stereo fact. -/
def Mol.hasStereo (m : Mol) : Bool :=
  !m.orientations.isEmpty || !m.geometries.isEmpty

/-- Whether atom number `atom` has an aromatic bond. This is all that a `Mol`
says about an atom being aromatic. -/
def hasAromaticBond (bonds : List Bond) (atom : Nat) : Bool :=
  bonds.any fun bond => (bond.a == atom || bond.b == atom) && bond.order == .aromatic

/-- Whether every bond of atom `atom` is a single bond. -/
def Mol.allBondsSingle (m : Mol) (atom : Nat) : Bool :=
  m.bonds.all fun bond => !(bond.a == atom || bond.b == atom) || bond.order == .single

end VeriMol
