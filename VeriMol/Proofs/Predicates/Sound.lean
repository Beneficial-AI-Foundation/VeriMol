import VeriMol.Core.Hydrogens

/-!
# Sound: of which `Mol`s a rule is asked (SPEC.md, section 16.2)

The reader records what a SMILES says and checks no valence: `CC(F)(F)(F)F`,
a carbon atom with five bonds, is read as a `Mol`. A rule about the structure
of a compound says nothing of worth about such a `Mol`. So the filter asks
one question before any rule, and it is the same for every rule: is the `Mol`
sound?

This file is that question as a definition, `Mol.Sound`. It is written to be
read, and no program runs it. The checker that the program runs stands in
`VeriMol/Core/Sound.lean`. `VeriMol/Proofs/Sound.lean` proves that the
checker says yes exactly when a `Mol` is sound, and that `Sound` gives the
same answer for every numbering of the atoms of a molecule (theorem 46 of
CLAIMS.md).

`Sound` is narrow on purpose, and it is a choice: no theorem says that these
are the right tests. It looks at one atom at a time, so it is no test that a
compound can exist. And the usual way of writing a compound can fail it:
nitromethane written with charges, `C[N+](=O)[O-]`, is not sound, and
`CN(=O)=O` is. SPEC.md, section 16.2, has examples and says what the tests
leave open.
-/

namespace VeriMol

/-- How many of the bonds of atom number `i` are aromatic. -/
def Mol.aromaticBonds (m : Mol) (i : Nat) : Nat :=
  (m.bonds.filter fun bond => (bond.a = i ∨ bond.b = i) ∧ bond.order = .aromatic).length

/-- What `Sound` asks of one atom: of the atom `atom`, which stands at number
`i` of `m`. The five lines of the definition say, in this order:

* its element is one of the ten that SMILES writes without square brackets;
* it has no mass number;
* its charge is 0;
* it has no aromatic bond, or at least two: an atom with exactly one belongs
  to no ring of aromatic bonds;
* its bonds and hydrogens add up to a usual valence of its element, or, if
  it has aromatic bonds, to one below a usual valence.

In the fifth line, `bondSum` counts a single bond as 1, a double bond as 2, a
triple bond as 3, a quadruple bond as 4 and an aromatic bond as 1, and
`Element.valences` has the usual valences: 3 for B; 4 for C; 3 and 5 for N
and for P; 2 for O; 2, 4 and 6 for S; 1 for F, Cl, Br and I (both stand in
`VeriMol/Core/Hydrogens.lean`). Counted as 1 each, the aromatic bonds of an
atom leave out its share of the double bonds of the ring: each carbon atom
of benzene comes out at 3, one below 4. No other element has a usual
valence, so the first line follows from the fifth. It is written out so that
the list of elements can be read here. -/
def Mol.SoundAtom (m : Mol) (i : Nat) (atom : Atom) : Prop :=
  atom.element ∈ [Element.B, .C, .N, .O, .P, .S, .F, .Cl, .Br, .I] ∧
  atom.isotope = none ∧
  atom.charge = 0 ∧
  m.aromaticBonds i ≠ 1 ∧
  (bondSum m.bonds i + atom.hydrogens ∈ atom.element.valences ∨
    0 < m.aromaticBonds i ∧ bondSum m.bonds i + atom.hydrogens + 1 ∈ atom.element.valences)

/-- `m` is sound: it is well formed, and each of its atoms passes the five
tests of `Mol.SoundAtom`. Only of a sound `Mol` is a rule asked. -/
def Mol.Sound (m : Mol) : Prop :=
  m.WellFormed ∧ ∀ i atom, m.atoms[i]? = some atom → m.SoundAtom i atom

end VeriMol
