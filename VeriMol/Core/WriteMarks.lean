import VeriMol.Core.Stereo
import VeriMol.Core.WriteParts

/-!
# Stereo marks in a written text (SPEC.md, section 12.3)

A `Mol` stores its stereo facts with atom numbers. A text says them with the
marks `@`, `@@`, `/` and `\`, and what a mark means depends on the order in
which the text writes the atoms. So the writer says each fact for the order in
which it writes. This is what the reader does, the other way round
(`VeriMol/Core/ReadMarks.lean`).

* **A double bond with a geometry** gets a mark at one bond of each of its two
  atoms (`chooseMarks`). A mark takes the place of the bond symbol
  (`markedSymbol`).
* **An atom with an orientation** is written in square brackets, with `@` or
  `@@` (`orientedAtom`). The `Mol` stores the orientation for the fixed order
  of the atom's places, and the mark says it for the order in which the text
  writes them (`Mol.turnedForText`; `placeKey` in `VeriMol/Core/Write.lean`
  gives that order). Where the reader would not read the atom so (rule 9),
  the writer refuses the `Mol` (`centreRefusal`).
-/

namespace VeriMol

/-! ## Which bonds carry a mark -/

/-- Two marked bonds whose marks depend on each other: the bonds, each by its
two atoms, and whether the two marks are the same. -/
structure Link where
  first : Nat × Nat
  second : Nat × Nat
  same : Bool

/-- A bond by its two atoms, the smaller one first. -/
def bondKey (x y : Nat) : Nat × Nat :=
  (min x y, max x y)

/-- Whether two bonds, each named by its two atoms, are the same bond. (Written
out: `==` on pairs is not on the list of what Core may use of Lean's library,
`Audit.allowedInCore`.) -/
def sameKey (x y : Nat × Nat) : Bool :=
  x.1 == y.1 && x.2 == y.2

/-- Whether the bond between these two atoms can carry a mark: its order is the
one that a missing symbol means (SPEC.md, section 5, rule 5). -/
def canCarryMark (mol : Mol) (x y : Nat) : Bool :=
  let key := bondKey x y
  mol.bonds.any fun bond =>
    bond.a == key.1 && bond.b == key.2 && bond.order == mol.assumedOrder key.1 key.2

/-- The bond that gets the mark for the double bond between `e` and `partner`:
the bond of `e` to its lowest-numbered neighbour, other than `partner`, whose
bond can carry a mark. With it: whether `/` at this bond says that the
lowest-numbered other neighbour of `e` lies above `e`. -/
def reference (mol : Mol) (e partner : Nat) : Option ((Nat × Nat) × Bool) :=
  match (mol.otherNeighbours e partner).find? fun x => canCarryMark mol e x with
  | none => none
  | some x =>
    -- The mark is written at the lower of the two atoms. It says the side of
    -- `x` as seen from `e` if `e` is that atom, and the other side if not.
    some (bondKey e x, decide (e < x) == ((mol.otherNeighbours e partner).head? == some x))

/-- The link that one double bond with a geometry puts between the marks at its
two atoms, or `none` if at one of them no bond can carry a mark. -/
def geometryLink (mol : Mol) (geometry : BondGeometry) : Option Link :=
  match reference mol geometry.a geometry.b, reference mol geometry.b geometry.a with
  | some atA, some atB =>
    some ⟨atA.1, atB.1, (atA.2 == atB.2) == (geometry.geometry == .sameSide)⟩
  | _, _ => none

/-- Two marked bonds at one atom of a double bond with a geometry point to
opposite sides: the link between them, if both other bonds of the atom `e`
are marked. -/
def sideLink (mol : Mol) (marked : List (Nat × Nat)) (e partner : Nat) : Option Link :=
  match mol.otherNeighbours e partner with
  | [x, y] =>
    if marked.any (sameKey (bondKey e x)) && marked.any (sameKey (bondKey e y)) then
      some ⟨bondKey e x, bondKey e y, decide (e < x) != decide (e < y)⟩
    else none
  | _ => none

/-- Whether the marks would give a geometry to this bond: it is a double bond
that can have one, and at each of its two atoms a bond to another neighbour is
marked. -/
def wouldGetGeometry (mol : Mol) (marked : List (Nat × Nat)) (bond : Bond) : Bool :=
  bond.order == .double && mol.canHaveGeometry bond.a bond.b &&
    (mol.otherNeighbours bond.a bond.b).any (fun x => marked.any (sameKey (bondKey bond.a x))) &&
    (mol.otherNeighbours bond.b bond.a).any (fun x => marked.any (sameKey (bondKey bond.b x)))

/-- The bonds that carry `/` or `\`: each by its two atoms, the smaller one
first, with `true` for `/`, which says that the higher-numbered atom lies
above the lower-numbered one. -/
abbrev Marks := List ((Nat × Nat) × Bool)

/-- The mark of a bond among the marks chosen so far. -/
def markAmong (marks : Marks) (key : Nat × Nat) : Option Bool :=
  (marks.find? fun found => sameKey found.1 key).map (·.2)

/-- One pass over the links: a bond whose partner in a link has a mark, and
which has none itself, gets the mark that the link asks for. -/
def spreadOnce (links : List Link) (marks : Marks) : Marks :=
  links.foldl
    (fun marks link =>
      match markAmong marks link.first, markAmong marks link.second with
      | some mark, none => marks ++ [(link.second, mark == link.same)]
      | none, some mark => marks ++ [(link.first, mark == link.same)]
      | _, _ => marks)
    marks

/-- Passes over the links `passes` times (`spreadOnce`). -/
def spreadTimes (links : List Link) : Nat → Marks → Marks
  | 0, marks => marks
  | passes + 1, marks => spreadTimes links passes (spreadOnce links marks)

/-- The marks, group by group: of the marked bonds in the order of the bonds,
the first one without a mark gets `/`, and its mark is spread over the bonds
that depend on it. -/
def markGroups (links : List Link) (passes : Nat) : List (Nat × Nat) → Marks → Marks
  | [], marks => marks
  | key :: rest, marks =>
    if (markAmong marks key).isSome then markGroups links passes rest marks
    else markGroups links passes rest (spreadTimes links passes (marks ++ [(key, true)]))

/-- Which bonds carry `/` or `\` (SPEC.md, section 12.3), or the reason why
the `Mol` is refused.

For every double bond with a geometry, one bond at each of its two atoms gets
a mark. The marks are chosen so that reading them gives every geometry back,
and so that two marked bonds at one atom of such a double bond point to
opposite sides. The last step makes sure of that: every link must hold. -/
def chooseMarks (mol : Mol) : Except (List Char) Marks :=
  let found := mol.geometries.map (geometryLink mol)
  if found.any Option.isNone then .error Message.noBondForAMark
  else
    let geometryLinks := found.filterMap id
    let marked := mol.bonds.filterMap fun bond =>
      if geometryLinks.any (fun link =>
          sameKey link.first (bond.a, bond.b) || sameKey link.second (bond.a, bond.b))
      then some (bond.a, bond.b) else none
    let links := geometryLinks ++ mol.geometries.flatMap fun geometry =>
      [sideLink mol marked geometry.a geometry.b,
        sideLink mol marked geometry.b geometry.a].filterMap id
    if mol.bonds.any (fun bond =>
        (mol.geometryAt bond.a bond.b).isNone && wouldGetGeometry mol marked bond) then
      .error Message.marksGiveAGeometry
    else
      let marks := markGroups links marked.length marked []
      if links.all (fun link =>
          match markAmong marks link.first, markAmong marks link.second with
          | some x, some y => (x == y) == link.same
          | _, _ => false) then .ok marks
      else .error Message.noChoiceOfMarks

/-! ## The marks in the text -/

/-- The symbol of a bond: its mark if it carries one, and otherwise what
`symbol` gives. -/
def markedSymbol (marks : Marks) (symbol : Bond → List Token) (bond : Bond) : List Token :=
  match markAmong marks (bond.a, bond.b) with
  | some up => [.bond (if up then .up else .down)]
  | none => symbol bond

/-- Why an atom with an orientation cannot be written where it stands, if it
cannot (SPEC.md, section 12.2, rule 9): it has a free place, and it would be
written without an atom before it, or with exactly one ring number and only
single bonds. `atomBefore` says whether the text writes it next to an earlier
atom, and `numbersAtAtom` is the number of ring numbers at the atom. -/
def centreRefusal (mol : Mol) (atom : Nat) (atomBefore : Bool) (numbersAtAtom : Nat) :
    Option (List Char) :=
  if mol.hasFreePlace atom && !atomBefore then some Message.freePlaceWithoutAtom
  else if mol.hasFreePlace atom && numbersAtAtom == 1 && mol.allBondsSingle atom then
    some Message.freePlaceWithOneRing
  else none

/-- The token of an atom with an orientation: in square brackets, with the mark
that says the orientation for the order in which the text writes the places
of the atom. `key` says where the text writes each place. -/
def orientedAtom (mol : Mol) (number : Nat) (atom : Atom) (stored : Orientation)
    (key : Place → Nat × Nat) : Token :=
  .atom { atom.inBrackets (writtenLowercase mol.bonds number atom) with
    mark := some (mol.turnedForText number key stored) }

end VeriMol
