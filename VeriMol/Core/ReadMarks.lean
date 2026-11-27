import VeriMol.Core.Problem
import VeriMol.Core.Stereo

/-!
# From the stereo marks of a text to the stereo facts (SPEC.md, section 12.2)

The marks `@`, `@@`, `/` and `\` are spelling: what they mean depends on the
order in which the text writes the atoms. The reader
(`VeriMol/Core/Read.lean`) notes what the marks are and where they stand. This
file works out, at the end of the text, the stereo facts that they say (rules
9 and 10), or the first problem with them.

What the reader notes:

* for every ring bond, the place of its ring number among the ring numbers of
  each of its two atoms (`RingBond`). A bond without such a note is a bond
  along the text;
* for every `/` and `\`, the bond that it stands at and what it says
  (`Direction`);
* for every atom with `@` or `@@`, its number, the mark and the position of
  the mark (`MarkedAtom`).

The writer goes the other way (`VeriMol/Core/WriteMarks.lean`).
-/

namespace VeriMol

/-- A ring bond as the text wrote it: its two atoms, the smaller one first, and
the place of its ring number among the ring numbers of each of them, counted
from 0. -/
structure RingBond where
  a : Nat
  b : Nat
  placeA : Nat
  placeB : Nat

/-- A direction mark of the text: the two atoms of the bond that it stands at,
the smaller one first; whether it says that `b` lies above `a`; and the
position of the mark. -/
structure Direction where
  a : Nat
  b : Nat
  above : Bool
  position : Nat

/-- An atom of the text that carries `@` or `@@`: its number, the mark, and the
position of the mark. -/
structure MarkedAtom where
  atom : Nat
  mark : Orientation
  position : Nat

/-! ## Rule 9: the orientation of an atom -/

/-- The note of the ring bond between `a` and `b`, if it is one. `a` is the
smaller of the two atom numbers. -/
def ringBondOf (rings : List RingBond) (a b : Nat) : Option RingBond :=
  rings.find? fun ring => ring.a == a && ring.b == b

/-- Where the text wrote a place of atom `atom`, as a key: first the earlier
atom that it stands next to (0), then its own hydrogen or the free place (1),
then its ring numbers in the order written (2, and the place of the number),
then the later atoms that stand next to it (3, and the atom's number). The
text writes the places of an atom in the rising order of these keys. -/
def writtenKey (rings : List RingBond) (atom : Nat) : Place → Nat × Nat
  | none => (1, 0)
  | some other =>
    if other < atom then
      match ringBondOf rings other atom with
      | none => (0, 0)
      | some ring => (2, ring.placeB)
    else
      match ringBondOf rings atom other with
      | none => (3, other)
      | some ring => (2, ring.placeA)

/-- Whether the text wrote atom `atom` next to an earlier atom: one of its
bonds to an earlier atom is a bond along the text. -/
def hasParent (mol : Mol) (rings : List RingBond) (atom : Nat) : Bool :=
  (mol.neighbours atom).any fun other =>
    decide (other < atom) && (ringBondOf rings other atom).isNone

/-- How many ring numbers the text wrote at atom `atom`. -/
def ringNumbersAt (rings : List RingBond) (atom : Nat) : Nat :=
  (rings.filter fun ring => ring.a == atom || ring.b == atom).length

/-- The orientation that the mark of one atom says, or the problem with the
mark (SPEC.md, section 12.2, rule 9). The mark is said for the places of the
atom in the order in which the text writes them. The `Mol` stores it for the
fixed order (`Mol.turnedForText`). -/
def orientationOfMark (mol : Mol) (rings : List RingBond) (marked : MarkedAtom) :
    Except Problem AtomOrientation :=
  if !mol.hasFourPlaces marked.atom then .error ⟨marked.position, Message.notAStereoCentre⟩
  else if mol.hasFreePlace marked.atom && !hasParent mol rings marked.atom then
    .error ⟨marked.position, Message.freePlaceNeedsAtom⟩
  else if mol.hasFreePlace marked.atom && ringNumbersAt rings marked.atom == 1 &&
      mol.allBondsSingle marked.atom then
    .error ⟨marked.position, Message.freePlaceAndOneRing⟩
  else
    .ok ⟨marked.atom,
      mol.turnedForText marked.atom (writtenKey rings marked.atom) marked.mark⟩

/-! ## Rule 10: the geometry of a double bond -/

/-- The direction mark at the bond between `a` and `b`, if it carries one. `a`
is the smaller of the two atom numbers. -/
def directionOf (directions : List Direction) (a b : Nat) : Option Direction :=
  directions.find? fun direction => direction.a == a && direction.b == b

/-- Whether the text says that `x` lies above `e`, with the position of the
mark that says so. `none` if the bond between the two carries no mark. -/
def aboveOf (directions : List Direction) (x e : Nat) : Option (Bool × Nat) :=
  (directionOf directions (min x e) (max x e)).map fun direction =>
    (if e < x then direction.above else !direction.above, direction.position)

/-- The neighbours of `e` other than `partner` whose bond to `e` carries a
mark: each with whether it lies above `e`, and with the position of its mark. -/
def markedOthers (mol : Mol) (directions : List Direction) (e partner : Nat) :
    List (Nat × Bool × Nat) :=
  (mol.otherNeighbours e partner).filterMap fun x =>
    (aboveOf directions x e).map fun found => (x, found.1, found.2)

/-- Two marked neighbours of one atom that are marked to the same side
contradict each other: the position of the later of the two marks. -/
def contradiction : List (Nat × Bool × Nat) → Option Nat
  | [(_, above, position), (_, above', position')] =>
    if above == above' then some (max position position') else none
  | _ => none

/-- Whether the lowest-numbered of `others` lies above, as the first marked
neighbour says it: where that one is not the lowest-numbered, the
lowest-numbered lies on the other side. -/
def lowestAbove (others : List Nat) : List (Nat × Bool × Nat) → Bool
  | (x, above, _) :: _ => if others.head? == some x then above else !above
  | [] => false

/-- What the marks say about one bond: nothing (`none`), or the problems with
them and, if there is none, the geometry (SPEC.md, section 12.2, rule 10). A
double bond gets a geometry when it can have one and, at each of its two
atoms, at least one bond to another neighbour carries a mark. -/
def geometryOfMarks (mol : Mol) (directions : List Direction) (bond : Bond) :
    Option (List Problem × Option BondGeometry) :=
  if bond.order == .double && mol.canHaveGeometry bond.a bond.b then
    let atA := markedOthers mol directions bond.a bond.b
    let atB := markedOthers mol directions bond.b bond.a
    if atA.isEmpty || atB.isEmpty then none
    else
      let problems : List Problem :=
        [contradiction atA, contradiction atB].filterMap fun found =>
          found.map fun position => ⟨position, Message.marksContradict⟩
      some (problems,
        if problems.isEmpty then
          some ⟨bond.a, bond.b,
            if lowestAbove (mol.otherNeighbours bond.a bond.b) atA
                == lowestAbove (mol.otherNeighbours bond.b bond.a) atB
            then .sameSide else .oppositeSides⟩
        else none)
  else none

/-! ## All marks of a text -/

/-- The problem with the smallest position, and of several at that position the
first. -/
def firstProblem : List Problem → Option Problem
  | [] => none
  | problem :: rest =>
    match firstProblem rest with
    | none => some problem
    | some other => if other.position < problem.position then some other else some problem

/-- The stereo facts that the marks of a text say about its `Mol`, or the first
problem with them. `mol` holds the atoms and the bonds of the text.

A direction mark must take part in the geometry of a double bond: it stands at
a bond of one of the two atoms of a double bond that gets a geometry. -/
def stereoFacts (mol : Mol) (rings : List RingBond) (directions : List Direction)
    (marked : List MarkedAtom) : Except Problem (List AtomOrientation × List BondGeometry) :=
  let oriented := (List.range mol.atoms.length).filterMap fun atom =>
    (marked.find? fun found => found.atom == atom).map (orientationOfMark mol rings)
  let judged := mol.bonds.filterMap fun bond =>
    (geometryOfMarks mol directions bond).map fun verdict => (bond, verdict)
  let alone := directions.filter fun direction =>
    !(judged.any fun found =>
      direction.a == found.1.a || direction.a == found.1.b
        || direction.b == found.1.a || direction.b == found.1.b)
  let problems : List Problem :=
    oriented.filterMap
        (fun found => match found with | .error problem => some problem | .ok _ => none)
      ++ judged.flatMap (fun found => found.2.1)
      ++ alone.map (fun direction => ⟨direction.position, Message.markWithoutPartner⟩)
  match firstProblem problems with
  | some problem => .error problem
  | none =>
    .ok (oriented.filterMap (fun found =>
        match found with | .ok orientation => some orientation | .error _ => none),
      judged.filterMap fun found => found.2.2)

end VeriMol
