import VeriMol.Core.Search
import VeriMol.Core.Write

/-!
# The chosen form of a `Mol` (SPEC.md, section 3.2)

One molecule has many `Mol`s, one for every numbering of its atoms. This file
picks one of them: the chosen form. Where the search finds it, it is the same
for every numbering of the molecule. So two well formed `Mol`s that have a
chosen form are the same molecule, numbered differently, exactly when their
chosen forms are equal (`VeriMol/Proofs/Chosen.lean`).

Every numbering gets a key: one entry for every place. The entry of a place
says how the atom there is bonded to the atoms at the places before it, the
nearest place first, and then what the atom is. For a `Mol` with stereo
facts, the entry of the last place says after that the stereo facts of the
`Mol` as it is numbered then. The chosen form is the numbering with the least
key. Because the bonds to the nearest places come first, the least key walks
through the molecule: the next atom is one that is bonded to the atom just
placed, if there is one.

The numberings with the least key are found by the search of
`VeriMol/Core/Search.lean`. It gives up when it would have to hold more than
`searchLimit` beginnings. Two rules keep it small. Atoms that can be
exchanged for one another, and that take part in no stereo fact, are placed
in the order of their numbers. And for a `Mol` without stereo facts, of the
beginnings that are alike the search holds one (`Mol.outlineOf`; "Beginnings
that are alike", further down, says when two are alike). The search still
gives up for molecules that have very many beginnings which are not alike,
such as ten molecules of ethane side by side.

The program runs `Mol.chosenForm` and `writeChosen`, with the table of twins
`Mol.smallerTwins` and the outlines `Mol.outline`. `Mol.key` and `Mol.twins` say
the key and the twins in the way SPEC.md says them. The theorems and the
tests use these two; the program does not run them.
-/

namespace VeriMol

open Search

/-! ## A `Mol` in a new order -/

/-- The order of the bond between two atoms, which may be given in either
order. `none` if they are not bonded. -/
def Mol.orderBetween (m : Mol) (i j : Nat) : Option BondOrder :=
  (m.bonds.find? fun bond =>
    (bond.a == i && bond.b == j) || (bond.a == j && bond.b == i)).map (·.order)

/-- All pairs of numbers below `n`, the smaller one first, in the order in
which a `Mol` lists its bonds. -/
def pairsBelow (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun x => ((List.range n).filter fun y => x < y).map fun y => (x, y)

/-- The bond between the atoms at the two new places of `pair`, if there is
one. `order` says which atom of `m` stands at each new place. -/
def Mol.arrangedBond (m : Mol) (order : List Nat) (pair : Nat × Nat) : Option Bond :=
  match order[pair.1]?, order[pair.2]? with
  | some i, some j => (m.orderBetween i j).map fun o => ⟨pair.1, pair.2, o⟩
  | _, _ => none

/-- The atoms and the bonds of the `Mol` with its atoms in a new order: atom
`j` of the result is atom `order[j]` of `m`. -/
def Mol.arrangedGraph (m : Mol) (order : List Nat) : Mol :=
  { atoms := order.filterMap fun i => m.atoms[i]?
    bonds := (pairsBelow order.length).filterMap (m.arrangedBond order) }

/-- The `Mol` with its atoms in a new order: atom `j` of the result is atom
`order[j]` of `m`.

The stereo facts are said anew for the new numbers, through the two statements
of `VeriMol/Core/Stereo.lean`. The new orientation of an atom is what `m` says
for its places in the order of their new numbers. The new geometry of a double
bond is what `m` says for the neighbours of its two atoms that have the lowest
new numbers. -/
def Mol.arrange (m : Mol) (order : List Nat) : Mol :=
  let graph := m.arrangedGraph order
  let old (place : Nat) : Nat := (order[place]?).getD 0
  if m.hasStereo then
    { graph with
      orientations := (List.range order.length).filterMap fun place =>
        (m.orientationOf (old place) ((graph.places place).map (Option.map old))).map
          fun orientation => ⟨place, orientation⟩
      geometries := graph.bonds.filterMap fun bond =>
        match (graph.otherNeighbours bond.a bond.b).head?,
            (graph.otherNeighbours bond.b bond.a).head? with
        | some x, some y =>
          (m.geometryOf (old bond.a) (old bond.b) (old x) (old y)).map
            fun geometry => ⟨bond.a, bond.b, geometry⟩
        | _, _ => none }
  else graph

/-! ## The key -/

/-- The stereo facts of a `Mol` as numbers, for its key: for every atom 0, 1 or
2 (no orientation, anticlockwise, clockwise), and then for every bond 0, 1 or
2 (no geometry, the same side, opposite sides). -/
def Mol.stereoCode (m : Mol) : List Nat :=
  ((List.range m.atoms.length).map fun atom =>
      match m.orientationAt atom with
      | none => 0
      | some .anticlockwise => 1
      | some .clockwise => 2)
    ++ m.bonds.map fun bond =>
      match m.geometryAt bond.a bond.b with
      | none => 0
      | some .sameSide => 1
      | some .oppositeSides => 2

/-- A bond order as a number. -/
def BondOrder.code : BondOrder → Nat
  | .quadruple => 0 | .triple => 1 | .double => 2 | .aromatic => 3 | .single => 4

/-- The bonds of the `Mol` at the atom `a`. -/
def Mol.bondsAt (m : Mol) (a : Nat) : List Bond :=
  m.bonds.filter fun bond => bond.a == a || bond.b == a

/-- How the atoms `i` and `a` are bonded, as a number: the lookup of
`Mol.orderBetween`, made among the bonds `near`, which are the bonds at `a`.
5 if the two are not bonded. -/
def bondCodeAmong (near : List Bond) (i a : Nat) : Nat :=
  match (near.find? fun bond =>
      (bond.a == i && bond.b == a) || (bond.a == a && bond.b == i)).map (·.order) with
  | some order => order.code
  | none => 5

/-- An atom as four numbers: its element, its hydrogens, its isotope, its
charge. An atom with more hydrogens, up to 9, gets the smaller number, so that
the walk usually starts at an end of the molecule. -/
def Atom.code (atom : Atom) : List Nat :=
  [Element.all.idxOf atom.element,
   if atom.hydrogens ≤ 9 then 9 - atom.hydrogens else atom.hydrogens,
   match atom.isotope with | none => 0 | some k => k + 1,
   if atom.charge < 0 then 2 * atom.charge.natAbs - 1 else 2 * atom.charge.natAbs]

/-- The row of the atom `a`, when the atoms `done` stand before it: for every
place before it, the nearest one first, how `a` is bonded to the atom that
stands there. -/
def Mol.row (m : Mol) (done : List Nat) (a : Nat) : List Nat :=
  let near := m.bondsAt a
  done.reverse.map fun i => bondCodeAmong near i a

/-- The entry of the atom `a`, when the atoms `done` stand before it: how it is
bonded to them, and what it is. For a `Mol` with stereo facts, the entry of
the last place says after that the stereo facts of the `Mol` in this order. -/
def Mol.entry (m : Mol) (done : List Nat) (a : Nat) : List Nat :=
  m.row done a ++ (match m.atoms[a]? with | some atom => atom.code | none => [])
    ++ (if m.hasStereo && done.length + 1 == m.atoms.length
        then (m.arrange (done ++ [a])).stereoCode else [])

/-- The key of a `Mol` as it is numbered (SPEC.md, section 3.2): the entry of
every atom, in the order of the atom numbers. The chosen form of a molecule is
its numbering with the least key. -/
def Mol.key (m : Mol) : List (List Nat) :=
  keys m.entry (List.range m.atoms.length)

/-- How two entries are compared: number by number from the front. Where one
entry is the beginning of the other, the shorter one comes first. -/
def leEntry (x y : List Nat) : Bool := decide (x ≤ y)

/-! ## Atoms that can be exchanged

Atoms that can be exchanged for one another give many numberings with the
least key, and all of them give the same `Mol`: the six nitrogen atoms of
`N[Co+3](N)(N)(N)(N)N` alone can be put in 720 orders. So the search places
such atoms, the twins, in the order of their numbers. Exchanging two atoms
can turn a stereo fact round, so two atoms count as twins only if neither
takes part in one (SPEC.md, section 3.2). -/

/-- Whether the atom takes part in a stereo fact: it has an orientation, or it
is an atom of a double bond with a geometry, or it is a neighbour of such an
atom. -/
def Mol.inStereoFact (m : Mol) (atom : Nat) : Bool :=
  m.orientations.any (fun x => x.atom == atom || (m.neighbours x.atom).contains atom) ||
    m.geometries.any (fun x =>
      x.a == atom || x.b == atom || (m.neighbours x.a).contains atom
        || (m.neighbours x.b).contains atom)

/-- The atom at the other end of a bond at the atom `a`. -/
def Bond.other (bond : Bond) (a : Nat) : Nat :=
  if bond.a == a then bond.b else bond.a

/-- Whether two atoms can be exchanged, worked out from what the two atoms are
and from the bonds at each of them: they are two atoms with the same element,
isotope, charge and hydrogens, and every atom that one of them is bonded to,
the partner aside, is bonded to the other in the same way. -/
def twinsFrom (a : Nat) (atomA : Option Atom) (nearA : List Bond) (b : Nat) (atomB : Option Atom)
    (nearB : List Bond) : Bool :=
  a != b && atomA.isSome && atomA == atomB &&
    (nearA.all fun bond =>
      bond.other a == b
        || bondCodeAmong nearA (bond.other a) a == bondCodeAmong nearB (bond.other a) b) &&
    (nearB.all fun bond =>
      bond.other b == a
        || bondCodeAmong nearA (bond.other b) a == bondCodeAmong nearB (bond.other b) b)

/-- Whether two atoms of a `Mol` can be exchanged: they are two atoms with the
same element, isotope, charge and hydrogens, each is bonded to every third
atom exactly as the other is, and neither takes part in a stereo fact
(`Mol.twins_iff` in `VeriMol/Proofs/Chosen.lean` says so for a well formed
`Mol`). -/
def Mol.twins (m : Mol) (a b : Nat) : Bool :=
  !m.inStereoFact a && !m.inStereoFact b &&
    twinsFrom a m.atoms[a]? (m.bondsAt a) b m.atoms[b]? (m.bondsAt b)

/-- For every atom, its twins with a smaller number. The search makes this
table once for a `Mol`. What the atoms are and which bonds they have is looked
up once for each atom, not once for each pair. -/
def Mol.smallerTwins (m : Mol) : List (List Nat) :=
  let table := (List.range m.atoms.length).map fun a =>
    (a, m.atoms[a]?, m.bondsAt a, m.inStereoFact a)
  table.map fun (a, atomA, nearA, inFactA) =>
    ((table.take a).filter fun (b, atomB, nearB, inFactB) =>
      !inFactA && !inFactB && twinsFrom a atomA nearA b atomB nearB).map (·.1)

/-- 1 if one of the atoms `smaller` is not placed yet, otherwise 0. -/
def stillWaiting (smaller done : List Nat) : Nat :=
  if smaller.any (fun b => !done.contains b) then 1 else 0

/-- The entry of an atom for the search: its entry, and behind it whether a
twin of it with a smaller number is still waiting. An atom whose smaller twins
are all placed comes first. -/
def Mol.searchEntry (m : Mol) (smallerTwins : List (List Nat)) (done : List Nat) (a : Nat) :
    List Nat × Nat :=
  (m.entry done a, stillWaiting (smallerTwins[a]?.getD []) done)

/-! ## Beginnings that are alike

Whole groups of atoms can be exchanged for one another as well, such as the
three rings of `c1ccccc1P(c1ccccc1)c1ccccc1`. Their atoms are no twins,
because their neighbours differ, and the search then holds many beginnings
that go through the same atoms in another order. Where two beginnings have
placed the same atoms, and every atom that is still to come is bonded to the
places of the one as to the places of the other, everything that can follow
is the same for both. So one of the two is enough (SPEC.md, section 3.2).

That is not so for a `Mol` with stereo facts: there the entry of the last
place says the stereo facts of the whole numbering, which can differ for two
such beginnings. So for a `Mol` with stereo facts the search takes no
outlines: there only the rule for twins keeps it small. -/

/-- The numbers of a row that say "bonded" (every number but 5), each with its
place in the row: a list of two numbers, the place and the number. Most
numbers of a row are 5, so this is much shorter than the row. (A list and not
a pair: `==` on pairs is not on the list of what Core may use of Lean's
library, `Audit.allowedInCore`.) -/
def placedCodes : Nat → List Nat → List (List Nat)
  | _, [] => []
  | place, code :: rest =>
    if code = 5 then placedCodes (place + 1) rest
    else [place, code] :: placedCodes (place + 1) rest

/-- What an outline is: for every atom of the `Mol`, `none` if the atom is
placed, and otherwise at which places it is bonded, and by which kind of
bond. -/
abbrev Outline := List (Option (List (List Nat)))

/-- The outline of a beginning of the search. Two beginnings of the same
length have the same outline exactly when they are alike: they have placed
the same atoms, and every atom that is not placed has the same row for both
(`Mol.outlineOf_eq_iff` in `VeriMol/Proofs/Chosen.lean`). -/
def Mol.outlineOf (m : Mol) (done : List Nat) : Outline :=
  (List.range m.atoms.length).map fun u =>
    if done.contains u then none else some (placedCodes 0 (m.row done u))

/-- What the search is given to take outlines with: `Mol.outlineOf` for a
`Mol` without stereo facts, and nothing for a `Mol` with stereo facts. -/
def Mol.outline (m : Mol) : Option (List Nat → Outline) :=
  if m.hasStereo then none else some m.outlineOf

/-! ## The chosen form -/

/-- The search gives up when it would have to hold more than this many
beginnings. -/
def searchLimit : Nat := 1000

/-- The chosen numbering of a `Mol`: its old atom numbers, in their new order.
`none` if the search gives up, and only then (`Mol.chosenOrder_isSome` in
`VeriMol/Proofs/Chosen.lean`). -/
def Mol.chosenOrder (m : Mol) : Option (List Nat) :=
  match searchWithin searchLimit (m.searchEntry m.smallerTwins) (lePair leEntry) m.outline
      (List.range m.atoms.length) m.atoms.length with
  | some (order :: _) => some order
  | _ => none

/-- The chosen form of a `Mol`: the `Mol` with its atoms in the chosen order.
For a well formed `Mol` that is the same molecule, numbered differently
(`Mol.renumbered_chosenForm` in `VeriMol/Proofs/Chosen.lean`). `none` if the
search gives up. -/
def Mol.chosenForm (m : Mol) : Option Mol :=
  m.chosenOrder.map m.arrange

/-- The command `canonical` refuses a `Mol` with more atoms than this, before
the search begins (SPEC.md, section 3.2): the table of twins can grow with the
square of the number of atoms, and it does where the atoms are twins of one
another. `Mol.chosenForm` itself has no such limit. -/
def atomLimit : Nat := 1000

/-- What the command `canonical` writes for a `Mol`: its chosen form, in the
spelling that `rewrite` writes. A `Mol` that is not well formed is refused, as
the two spellings refuse it. Then a `Mol` with more than `atomLimit` atoms is
refused. Only then does the search begin. -/
def writeChosen (mol : Mol) : Except (List Char) (List Char) :=
  if ¬ mol.WellFormed then .error Message.notWellFormed
  else if atomLimit < mol.atoms.length then .error (Message.tooManyAtoms atomLimit)
  else
    match mol.chosenForm with
    | none => .error Message.searchGivesUp
    | some chosen => write chosen

end VeriMol
