import VeriMol.Core.Mol

/-!
# The hydrogens of an atom without square brackets (SPEC.md, section 5, rule 7)

1. Add up the bonds of the atom: single 1, double 2, triple 3, quadruple 4,
   aromatic 1.
2. Take the smallest normal valence of the element that is at least this sum.
   If there is none, the atom has 0 hydrogens.
3. Otherwise the hydrogens are that valence minus the sum. A lowercase atom
   gets one fewer, but never fewer than 0.
-/

namespace VeriMol

/-- What a bond counts when the bonds of an atom are added up. -/
def BondOrder.weight : BondOrder → Nat
  | .single    => 1
  | .double    => 2
  | .triple    => 3
  | .quadruple => 4
  | .aromatic  => 1

/-- The normal valences of the elements that may stand without square
brackets, smallest first. Every other element has none. -/
def Element.valences : Element → List Nat
  | .B  => [3]
  | .C  => [4]
  | .N  => [3, 5]
  | .O  => [2]
  | .P  => [3, 5]
  | .S  => [2, 4, 6]
  | .F  => [1]
  | .Cl => [1]
  | .Br => [1]
  | .I  => [1]
  | _   => []

/-- The hydrogens of an atom without square brackets whose bonds add up to
`sum`. Subtraction of natural numbers stops at 0, which is what the rule
wants. -/
def bareHydrogens (element : Element) (aromatic : Bool) (sum : Nat) : Nat :=
  match element.valences.find? (fun valence => sum ≤ valence) with
  | none => 0
  | some valence => if aromatic then valence - sum - 1 else valence - sum

/-- What the bonds of atom number `atom` add up to. -/
def bondSum (bonds : List Bond) (atom : Nat) : Nat :=
  ((bonds.filter fun bond => bond.a = atom ∨ bond.b = atom).map (·.order.weight)).sum

end VeriMol
