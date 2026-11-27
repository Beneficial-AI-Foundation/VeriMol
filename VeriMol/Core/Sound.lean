import VeriMol.Core.Hydrogens
import VeriMol.Core.Problem

/-!
# Is a `Mol` sound? (SPEC.md, section 16.2)

The reader records what a text says and checks no valence. The filter asks its
rule only of a `Mol` that is sound: well formed, with every atom an uncharged
atom of an element that SMILES writes without square brackets, without a mass
number, with no aromatic bond or at least two, and with bonds and hydrogens
that add up to a usual valence, or to one below it for an atom with aromatic
bonds.

This file is the checker: it finds the first reason why a `Mol` is not sound.
What "sound" means is stated on its own, as a definition for theorems, in
`VeriMol/Proofs/Predicates/Sound.lean`, and `VeriMol/Proofs/Sound.lean`
proves that this checker says yes exactly when a `Mol` is sound by that
definition.
-/

namespace VeriMol

/-- Why the atom `atom`, which stands at number `i` of `m`, keeps `m` from
being sound: the first of five reasons that applies, or `none` if none does.
In this order:

* its element is none of those that SMILES writes without square brackets;
* it has a mass number;
* it has a charge;
* exactly one of its bonds is aromatic;
* its bonds and hydrogens add up to no usual valence of its element, and, if
  it has aromatic bonds, not to one below a usual valence either. The bonds
  are added up as `bondSum` adds them, and the usual valences are those of
  `Element.valences`. -/
def Mol.atomProblem (m : Mol) (i : Nat) (atom : Atom) : Option (List Char) :=
  let total := bondSum m.bonds i + atom.hydrogens
  let aromatic :=
    (m.bonds.filter fun bond => (bond.a == i || bond.b == i) && bond.order == .aromatic).length
  if !Element.bare.contains atom.element then some (Message.unsoundElement i)
  else if atom.isotope.isSome then some (Message.unsoundIsotope i)
  else if atom.charge != 0 then some (Message.unsoundCharge i)
  else if aromatic == 1 then some (Message.unsoundAromatic i)
  else if !(atom.element.valences.contains total ||
      (aromatic != 0 && atom.element.valences.contains (total + 1))) then
    some (Message.unsoundValence i)
  else none

/-- The first reason why `m` is not sound, or `none` if it is sound. A `Mol`
that is not well formed gets that reason. Otherwise the atoms are gone
through in the order of their numbers, and the first atom that fails a test
gives the reason. -/
def Mol.soundProblem (m : Mol) : Option (List Char) :=
  if ¬ m.WellFormed then some Message.notWellFormed
  else ((List.range m.atoms.length).zip m.atoms).findSome? fun (i, atom) => m.atomProblem i atom

/-- The checker of soundness: whether `m` is sound. It is the yes or no of
`Mol.soundProblem`, which the filter asks because it also needs the reason. -/
def Mol.isSound (m : Mol) : Bool :=
  m.soundProblem.isNone

end VeriMol
