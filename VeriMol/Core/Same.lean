import VeriMol.Core.Stereo

/-!
# The same molecule, numbered differently (SPEC.md, section 3.1)

A `Mol` numbers its atoms, so one molecule has many `Mol`s: one for every order
in which its atoms can be listed. This file says when two `Mol`s are the same
molecule with its atoms numbered differently.

It is a definition, not a program: it says that a renumbering exists, not how
to find one. The program does not run it. The theorems are stated with it:
those of `VeriMol/Proofs/Same.lean` about the definition itself, those of
`VeriMol/Proofs/Chosen.lean` and `VeriMol/Proofs/Molecule.lean` about the
chosen form, the command `canonical` and the canonical text of a molecule, and
those which say that "sound" and the rule of the filter give the same answer
for every numbering (`Mol.Renumbered.sound_iff`,
`Mol.Renumbered.noFluoroGroup_iff`).

The stereo facts of a `Mol` are marks that depend on the numbering
(`VeriMol/Core/Stereo.lean`). So the definition does not compare the marks. It
says that the two statements which are worked out from them carry over: what
the one `Mol` says about the orientation of an atom and about the geometry of
a double bond, the other says for the new numbers.

It covers the numbering and nothing else. The same ring with aromatic bonds
and with single and double bonds in turn is two molecules in this sense, and so
is the same hydrogen as a count and as an atom of its own. The definition is
meant for well formed `Mol`s.
-/

namespace VeriMol

/-- Atoms `i` and `j` are joined by a bond of this order. The two atoms may be
given in either order. -/
def Mol.Joined (m : Mol) (i j : Nat) (order : BondOrder) : Prop :=
  ⟨i, j, order⟩ ∈ m.bonds ∨ ⟨j, i, order⟩ ∈ m.bonds

/-- `m₂` is `m₁` with its atoms numbered differently: `f` gives every atom
number of `m₁` its number in `m₂`, and `g` leads back. -/
structure Mol.RenumberedBy (f g : Nat → Nat) (m₁ m₂ : Mol) : Prop where
  /-- `f` sends the atom numbers of `m₁` to atom numbers of `m₂`, and `g`
  undoes it. -/
  forth : ∀ i, i < m₁.atoms.length → f i < m₂.atoms.length ∧ g (f i) = i
  /-- `g` sends the atom numbers of `m₂` to atom numbers of `m₁`, and `f`
  undoes it. -/
  back : ∀ j, j < m₂.atoms.length → g j < m₁.atoms.length ∧ f (g j) = j
  /-- Every atom is the same atom at its new number. -/
  atoms : ∀ i, i < m₁.atoms.length → m₂.atoms[f i]? = m₁.atoms[i]?
  /-- Two atoms are joined in `m₁` exactly when their new numbers are joined
  in `m₂`, by a bond of the same order. -/
  bonds : ∀ i j order, i < m₁.atoms.length → j < m₁.atoms.length →
    (m₁.Joined i j order ↔ m₂.Joined (f i) (f j) order)
  /-- What `m₁` says about the orientation of an atom, for its places in some
  order, `m₂` says about the atom at its new number, for the places at their
  new numbers. -/
  orientations : ∀ atom places, atom < m₁.atoms.length →
    (∀ i, some i ∈ places → i < m₁.atoms.length) →
    m₂.orientationOf (f atom) (places.map (Option.map f)) = m₁.orientationOf atom places
  /-- What `m₁` says about two neighbours of a double bond, `m₂` says about
  the atoms at their new numbers. -/
  geometries : ∀ a b x y, a < m₁.atoms.length → b < m₁.atoms.length →
    x < m₁.atoms.length → y < m₁.atoms.length →
    m₂.geometryOf (f a) (f b) (f x) (f y) = m₁.geometryOf a b x y

/-- The same molecule, numbered differently: `m₂` is `m₁` with its atoms in
another order. -/
def Mol.Renumbered (m₁ m₂ : Mol) : Prop :=
  ∃ f g, Mol.RenumberedBy f g m₁ m₂

end VeriMol
