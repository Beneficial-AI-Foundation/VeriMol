import VeriMol.Core.Mol

/-!
# The arrangement in space: two statements (SPEC.md, section 12.1)

A `Mol` stores one mark for an atom that has an orientation, and one for a
double bond that has a geometry. Each mark is said for one fixed choice: the
places of the atom in the fixed order, and the lowest-numbered neighbours of
the two atoms of the double bond. So a mark depends on how the atoms are
numbered.

What does not depend on the numbering are two statements, which this file
works out from the marks:

* `Mol.orientationOf`: seen from the first of these four places, the other
  three follow each other anticlockwise, or clockwise, around this atom;
* `Mol.geometryOf`: this neighbour of the one atom and that neighbour of the
  other lie on the same side of this double bond, or on opposite sides.

The function that puts the atoms of a `Mol` into a new order asks them for the
new marks (`Mol.arrange` in `VeriMol/Core/Chosen.lean`), and "the same
molecule, numbered differently" (`VeriMol/Core/Same.lean`) says that both
carry over. The reader and the writer do not ask them. The reader works the
marks out from the text, and the writer says them back for the order in which
it writes; both turn a mark round by counting swaps, as the first statement
does (`Mol.turnedForText`, which `VeriMol/Core/ReadMarks.lean` and
`VeriMol/Core/WriteMarks.lean` use).
-/

namespace VeriMol

/-- A place around an atom: a neighbour, or `none` for the fourth place of an
atom with three neighbours, which holds the atom's own hydrogen or stays
free. -/
abbrev Place := Option Nat

/-- The places of an atom in the fixed order (SPEC.md, section 12.1): its
fourth place first, if it has three neighbours; then its neighbours, which a
well formed `Mol` lists in increasing atom number. -/
def Mol.places (m : Mol) (atom : Nat) : List Place :=
  (if (m.neighbours atom).length = 3 then [none] else []) ++ (m.neighbours atom).map some

/-- A place as a number: 0 for the fourth place, and for a neighbour its atom
number plus 1. The fixed order is the rising order of these numbers. -/
def placeCode : Place → Nat
  | none => 0
  | some atom => atom + 1

/-- The number of pairs of a list that stand in falling order. In a list
without repeats, one swap of two entries changes it by an odd number. -/
def fallingPairs : List Nat → Nat
  | [] => 0
  | x :: rest => (rest.filter (· < x)).length + fallingPairs rest

/-- Whether one key of two numbers comes before another: by the first number,
and where the first numbers are equal, by the second. -/
def keyBefore (x y : Nat × Nat) : Bool :=
  decide (x.1 < y.1) || (x.1 == y.1 && decide (x.2 < y.2))

/-- The number of pairs of a list of such keys that stand in falling order. -/
def fallingKeys : List (Nat × Nat) → Nat
  | [] => 0
  | x :: rest => (rest.filter fun y => keyBefore y x).length + fallingKeys rest

/-- The other orientation if `turned`, and otherwise the same. -/
def Orientation.turnedIf (orientation : Orientation) (turned : Bool) : Orientation :=
  if turned then
    match orientation with
    | .anticlockwise => .clockwise
    | .clockwise => .anticlockwise
  else orientation

/-- A mark of atom `atom`, carried from the fixed order of its places to the
order in which a text writes them, or back. `key` says where the text writes
each place: it writes the places in the rising order of their keys. The mark
is the other one if an odd number of swaps leads from one order to the other.
The reader and the writer both use this. -/
def Mol.turnedForText (m : Mol) (atom : Nat) (key : Place → Nat × Nat) (mark : Orientation) :
    Orientation :=
  mark.turnedIf (fallingKeys ((m.places atom).map key) % 2 == 1)

/-- The other geometry if `turned`, and otherwise the same. -/
def Geometry.turnedIf (geometry : Geometry) (turned : Bool) : Geometry :=
  if turned then
    match geometry with
    | .sameSide => .oppositeSides
    | .oppositeSides => .sameSide
  else geometry

/-- The mark that the `Mol` stores for this atom, if it has an orientation. -/
def Mol.orientationAt (m : Mol) (atom : Nat) : Option Orientation :=
  (m.orientations.find? fun x => x.atom == atom).map (·.orientation)

/-- The mark that the `Mol` stores for the double bond between `a` and `b`, if
it has a geometry. `a` is the smaller of the two atom numbers. -/
def Mol.geometryAt (m : Mol) (a b : Nat) : Option Geometry :=
  (m.geometries.find? fun x => x.a == a && x.b == b).map (·.geometry)

/-- **The first statement.** Seen from the first of `places` towards `atom`,
the other three follow each other so. `places` are the four places of the
atom in some order. `none` if the atom has no orientation, or if `places` are
not its four places.

The `Mol` stores the answer for the fixed order. Another order of the same
places gets the same answer after an even number of swaps, and the other one
after an odd number. -/
def Mol.orientationOf (m : Mol) (atom : Nat) (places : List Place) : Option Orientation :=
  match m.orientationAt atom with
  | none => none
  | some stored =>
    if places.Perm (m.places atom) then
      some (stored.turnedIf (fallingPairs (places.map placeCode) % 2 == 1))
    else none

/-- **The second statement.** `x`, a neighbour of `a`, and `y`, a neighbour of
`b`, lie so to the double bond between `a` and `b`. `none` if that bond has
no geometry, or if `x` or `y` is no such neighbour.

The `Mol` stores the answer for the lowest-numbered such neighbour of each
of the two atoms. The other neighbour of an atom lies on the other side. -/
def Mol.geometryOf (m : Mol) (a b x y : Nat) : Option Geometry :=
  match m.geometryAt (min a b) (max a b) with
  | none => none
  | some stored =>
    if (m.otherNeighbours a b).contains x && (m.otherNeighbours b a).contains y then
      some (stored.turnedIf
        (((m.otherNeighbours a b).head? == some x) != ((m.otherNeighbours b a).head? == some y)))
    else none

end VeriMol
