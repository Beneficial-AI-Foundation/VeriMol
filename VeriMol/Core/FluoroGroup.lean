import VeriMol.Core.Mol

/-!
# Perfluorinated groups: the search (SPEC.md, section 16.3)

A perfluorinated group is made of carbon atoms that hang together through
the bonds between them. Its atoms are of two kinds. A fluorinated carbon
atom is a carbon atom with four bonds, at least one of them to a fluorine
atom, that carries no hydrogen and has no double, triple or quadruple bond.
What else it is bonded to is not looked at. A branch carbon atom is such an
atom, except that it need not carry fluorine: it is bonded to three carbon
atoms of a group. The atom in the middle of (CF3)3C– is one. This file finds
the groups of a `Mol`, and the size of the largest.

It is the checker of a rule: "no perfluorinated group of `n` or more carbon
atoms". The rule is stated on its own, as a definition for theorems that says
what a group is and not how one is found, in
`VeriMol/Proofs/Predicates/FluoroGroup.lean`. `VeriMol/Proofs/FluoroGroup.lean`
proves that this file finds exactly the groups of that definition, for every
`Mol`: it finds no atom that does not belong to a group, and it leaves no
atom out.

The work has two parts. First the carbon atoms of the groups are worked out
(`Mol.groupCarbons`): the fluorinated carbon atoms, and then, round by round,
the branch carbon atoms. Then a search spreads from atom to atom along the
bonds, through these atoms only (`Mol.spread`).
-/

namespace VeriMol

/-! ## The carbon atoms of the groups -/

/-- Whether atom number `c` meets the five conditions that every carbon atom
of a perfluorinated group must meet: it is a carbon atom; its count of
hydrogens is 0; none of its bonds is a double, triple or quadruple bond; it
has exactly four bonds; and none of the four goes to a hydrogen atom. -/
def Mol.isSkeletonCarbon (m : Mol) (c : Nat) : Bool :=
  let around := (m.neighbours c).map fun x => m.atoms[x]?.map (·.element)
  (match m.atoms[c]? with
    | some atom => atom.element == .C && atom.hydrogens == 0
    | none => false) &&
  (m.bonds.all fun bond =>
    !(bond.a == c || bond.b == c) || bond.order == .single || bond.order == .aromatic) &&
  around.length == 4 &&
  !around.contains (some .H)

/-- Whether atom number `c` is a fluorinated carbon atom: it meets the five
conditions, and at least one of its four bonds goes to a fluorine atom. -/
def Mol.isFluoroCarbon (m : Mol) (c : Nat) : Bool :=
  m.isSkeletonCarbon c &&
  ((m.neighbours c).map fun x => m.atoms[x]?.map (·.element)).contains (some .F)

/-- Whether a list of numbers holds two different numbers. -/
def hasTwoDifferent : List Nat → Bool
  | [] => false
  | y :: others => others.any (· != y)

/-- Whether a list of numbers holds three different numbers: its first number
and two different ones among the rest, or three among the rest. -/
def hasThreeDifferent : List Nat → Bool
  | [] => false
  | x :: rest => hasTwoDifferent (rest.filter (· != x)) || hasThreeDifferent rest

/-- One round. `members` holds the carbon atoms of the groups that are known
so far. The round gives the atoms that it adds: every atom of the `Mol` that
is not among them yet, meets the five conditions, and is bonded to three
different atoms of `members`. -/
def Mol.newGroupCarbons (m : Mol) (members : List Nat) : List Nat :=
  (List.range m.atoms.length).filter fun c =>
    !members.contains c && m.isSkeletonCarbon c &&
      hasThreeDifferent ((m.neighbours c).filter members.contains)

/-- Round after round, until a round adds no atom. `rounds` bounds the number
of rounds, so that Lean sees that this ends. Every round but the last adds at
least one atom, so one round for every atom of the `Mol` is always enough
(`Mol.groupCarbons`). -/
def Mol.growGroupCarbons (m : Mol) : Nat → List Nat → List Nat
  | 0, members => members
  | rounds + 1, members =>
    let new := m.newGroupCarbons members
    if new.isEmpty then members else m.growGroupCarbons rounds (new ++ members)

/-- The carbon atoms of the perfluorinated groups of a `Mol`, each once: the
fluorinated carbon atoms, and the branch carbon atoms, which are worked out
from them inwards. A branch carbon atom can be one of the three atoms that
hold the next. -/
def Mol.groupCarbons (m : Mol) : List Nat :=
  m.growGroupCarbons m.atoms.length ((List.range m.atoms.length).filter m.isFluoroCarbon)

/-! ## The search -/

/-- The search. It spreads from atom to atom along the bonds, through the
atoms of `members` only.

`todo` holds the atoms that are still to be looked at, and `found` the atoms
that are found so far. One step takes the first atom of `todo`. If it is
found already, or is no atom of `members`, the atom is passed over. Otherwise
it is found, and the atoms that it is bonded to are put in front of `todo`.
The search ends when `todo` is empty.

`steps` bounds the number of steps, so that Lean sees that the search ends. A
carbon atom of a group has four bonds, so each atom that is found puts four
atoms into `todo`: four steps for every atom of the `Mol` and one more are
always enough (`Mol.fluoroGroupAmong`). -/
def Mol.spread (m : Mol) (members : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, found => found
  | _ + 1, [], found => found
  | steps + 1, c :: todo, found =>
    if found.contains c || !members.contains c then m.spread members steps todo found
    else m.spread members steps (m.neighbours c ++ todo) (c :: found)

/-- The atoms of `members` that the search reaches from atom number `a`,
each once, with four steps for every atom of the `Mol` and one more. -/
def Mol.fluoroGroupAmong (m : Mol) (members : List Nat) (a : Nat) : List Nat :=
  m.spread members (4 * m.atoms.length + 1) [a] []

/-- The perfluorinated group of atom number `a`: the carbon atoms of the
groups that the search reaches from `a`, each once. It is empty if `a` is no
such atom. The theorems are stated with it; `Mol.fluoroGroups` runs the same
search, once for each group. -/
def Mol.fluoroGroupOf (m : Mol) (a : Nat) : List Nat :=
  m.fluoroGroupAmong m.groupCarbons a

/-- The groups of the given atoms, each group once. `members` holds the
carbon atoms of the groups. `seen` holds the atoms of the groups that are
listed already: an atom among them starts no search of its own. -/
def Mol.fluoroGroupsFrom (m : Mol) (members : List Nat) : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | a :: rest, seen =>
    if seen.contains a || !members.contains a then m.fluoroGroupsFrom members rest seen
    else
      let group := m.fluoroGroupAmong members a
      group :: m.fluoroGroupsFrom members rest (group ++ seen)

/-- The perfluorinated groups of a `Mol`, each as the list of its atoms, in
the order of the lowest atom number of each group. -/
def Mol.fluoroGroups (m : Mol) : List (List Nat) :=
  m.fluoroGroupsFrom m.groupCarbons (List.range m.atoms.length) []

/-- The size of the largest perfluorinated group of a `Mol`: the number of
its carbon atoms. 0 if the `Mol` has no fluorinated carbon atom. -/
def Mol.largestFluoroGroup (m : Mol) : Nat :=
  (m.fluoroGroups.map List.length).foldl max 0

/-- The checker of the rule: whether `m` has no perfluorinated group of `n`
or more carbon atoms. -/
def Mol.hasNoFluoroGroup (m : Mol) (n : Nat) : Bool :=
  decide (m.largestFluoroGroup < n)

end VeriMol
