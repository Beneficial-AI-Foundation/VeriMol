import VeriMol.Proofs.Chosen
import VeriMol.Proofs.Run
import VeriMol.Proofs.Write

/-!
# Molecules and canonical texts correspond one to one

A `Mol` numbers its atoms, so one molecule has many `Mol`s. This file has a
type for the molecule itself, `Molecule`: a well formed `Mol`, up to the
numbering of its atoms (SPEC.md, section 3.1). And it has a type for the
canonical texts, `CanonicalText`: the texts that the command `canonical`
writes (SPEC.md, section 3.2).

Theorem 45 of CLAIMS.md says that the two correspond one to one, through the
program itself: the writer of `canonical` leads from a molecule to its text,
and the reader leads back.

* `Molecule.canonicalText` gives the canonical text of a molecule, or `none`
  where `canonical` writes no text for it.
* `CanonicalText.molecule` gives the molecule that a canonical text is read
  as.
* `Molecule.canonicalText_eq_some_iff`, the first statement of theorem 45: a
  canonical text is the canonical text of a molecule exactly when it is read
  as that molecule.

So every canonical text belongs to exactly one molecule, and two canonical
texts that are read as the same molecule are equal
(`CanonicalText.molecule_injective`). A molecule has at most one canonical
text, and none where the writer of `canonical` answers with an error.

Four statements more say what the two types and the two maps are, through
the functions of the program (`Molecule.of_eq_of_iff`,
`isCanonicalText_iff_run`, `Molecule.canonicalText_of`,
`CanonicalText.molecule_of`).

CLAIMS.md says under theorem 45 what all this leaves open: which molecules
have a canonical text, and that "the same molecule" is about the numbering
and nothing else, so that a `Molecule` need not be what a chemist calls one
molecule.

Everything in this file follows from theorems 5, 8, 11, 15, 20, 23, 24, 26
and 27, from the definition of `writeChosen`, and from one helper lemma
(`Mol.Renumbered.length_eq`: the same molecule, numbered differently, has as
many atoms). The program runs none of it.
-/

namespace VeriMol

/-! ## What the writer of `canonical` gives for a `Mol` -/

/-- When `writeChosen`, the writer of `canonical`, gives a text: the `Mol` is
well formed, it has at most `atomLimit` atoms, it has a chosen form, and the
text is what the writer gives for the chosen form. -/
theorem writeChosen_ok_iff (mol : Mol) (text : List Char) :
    writeChosen mol = .ok text ↔
      mol.WellFormed ∧ mol.atoms.length ≤ atomLimit ∧
        ∃ chosen, mol.chosenForm = some chosen ∧ write chosen = .ok text := by
  unfold writeChosen
  by_cases w : mol.WellFormed
  · by_cases hl : atomLimit < mol.atoms.length
    · have hl' : ¬ mol.atoms.length ≤ atomLimit := Nat.not_le.2 hl
      simp [w, hl, hl']
    · have hl' : mol.atoms.length ≤ atomLimit := Nat.not_lt.1 hl
      cases hc : mol.chosenForm with
      | none => simp [w, hl]
      | some c => simp [w, hl, hl']
  · simp [w]

/-- Two well formed `Mol`s that are the same molecule, numbered differently,
get the same answer from the writer of `canonical`: the same text, or the same
error. This is theorem 32 for `Mol`s that need not come from a text. -/
theorem writeChosen_eq_of_renumbered (m₁ m₂ : Mol) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (h : m₁.Renumbered m₂) : writeChosen m₁ = writeChosen m₂ := by
  have hc := Mol.chosenForm_eq_of_renumbered m₁ m₂ w₁ w₂ h
  simp only [writeChosen, w₁, w₂, not_true_eq_false, ↓reduceIte, hc, h.length_eq]

/-- If the writer of `canonical` gives a text for one `Mol`, it gives that same
text for a second `Mol` exactly when the second is well formed and is the
first numbered differently. This is theorem 31 for `Mol`s that need not come
from a text. -/
theorem writeChosen_eq_iff (m₁ m₂ : Mol) (text : List Char) (h : writeChosen m₁ = .ok text) :
    writeChosen m₂ = .ok text ↔ m₂.WellFormed ∧ m₁.Renumbered m₂ := by
  obtain ⟨w₁, _, c₁, hc₁, hw₁⟩ := (writeChosen_ok_iff m₁ text).1 h
  constructor
  · intro h₂
    obtain ⟨w₂, _, c₂, hc₂, hw₂⟩ := (writeChosen_ok_iff m₂ text).1 h₂
    have e : c₁ = c₂ := write_injective c₁ c₂ text hw₁ hw₂
    subst e
    exact ⟨w₂, (Mol.renumbered_iff_chosenForm_eq m₁ m₂ c₁ w₁ w₂ hc₁).2 hc₂⟩
  · rintro ⟨w₂, hr⟩
    rw [← writeChosen_eq_of_renumbered m₁ m₂ w₁ w₂ hr]
    exact h

/-- A text that the writer of `canonical` gives for a `Mol` is read as a `Mol`
that is the first one numbered differently, and that gets this very text
itself. -/
theorem read_of_writeChosen (mol : Mol) (text : List Char) (h : writeChosen mol = .ok text) :
    ∃ chosen, read text = .ok chosen ∧ writeChosen chosen = .ok text ∧
      mol.Renumbered chosen := by
  obtain ⟨w, _, c, hc, hw⟩ := (writeChosen_ok_iff mol text).1 h
  have hr := Mol.renumbered_chosenForm mol c w hc
  have wc := Mol.chosenForm_wellFormed mol c w hc
  exact ⟨c, read_write c text hw, (writeChosen_eq_iff mol c text h).2 ⟨wc, hr⟩, hr⟩

/-! ## Molecules -/

/-- "The same molecule, numbered differently" (SPEC.md, section 3.1), on the
well formed `Mol`s. It is an equivalence relation there (theorem 20). -/
def Mol.sameMolecule : Setoid {mol : Mol // mol.WellFormed} where
  r a b := a.1.Renumbered b.1
  iseqv := ⟨fun a => Mol.Renumbered.refl a.1, fun h => Mol.Renumbered.symm h,
    fun h₁ h₂ => Mol.Renumbered.trans h₁ h₂⟩

/-- A molecule: a well formed `Mol`, up to the numbering of its atoms. Two
well formed `Mol`s give the same `Molecule` exactly when one is the other
numbered differently (`Molecule.of_eq_of_iff`). -/
def Molecule : Type := Quotient Mol.sameMolecule

/-- The molecule of a well formed `Mol`. Every `Molecule` is the molecule of
some well formed `Mol`. -/
def Molecule.of (mol : Mol) (w : mol.WellFormed) : Molecule :=
  Quotient.mk Mol.sameMolecule ⟨mol, w⟩

/-- Theorem 45 of CLAIMS.md, third statement. What a `Molecule` is: two well
formed `Mol`s give the same `Molecule` exactly when one is the other numbered
differently. -/
theorem Molecule.of_eq_of_iff (m₁ m₂ : Mol) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) :
    Molecule.of m₁ w₁ = Molecule.of m₂ w₂ ↔ m₁.Renumbered m₂ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ## Canonical texts -/

/-- A canonical text: a text that the writer of `canonical` gives for some
`Mol`. -/
def IsCanonicalText (text : List Char) : Prop :=
  ∃ mol, writeChosen mol = .ok text

/-- The canonical texts, as a type. -/
def CanonicalText : Type := {text : List Char // IsCanonicalText text}

/-- Theorem 45 of CLAIMS.md, fourth statement. What a canonical text is: the
canonical texts are the texts that the command `canonical` prints unchanged. -/
theorem isCanonicalText_iff_run (text : List Char) :
    IsCanonicalText text ↔
      run ["canonical".toList, text]
        = { stdout := text ++ ['\n'], stderr := [], exitCode := 0 } := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨c, hr, hw, _⟩ := read_of_writeChosen m text hm
    rw [run_canonical text c hr, hw]
  · intro h
    cases hr : read text with
    | error problem =>
      rw [run_word_of_read_error _ text problem (.inr (.inr rfl)) hr] at h
      simp at h
    | ok mol =>
      rw [run_canonical text mol hr] at h
      cases hw : writeChosen mol with
      | error message => rw [hw] at h; simp at h
      | ok written =>
        rw [hw] at h
        have e : written = text := by simpa using h
        exact ⟨mol, e ▸ hw⟩

/-! ## The two maps -/

/-- What the writer of `canonical` answers for a molecule: what it answers for
any of its numberings, which is the same for all of them
(`writeChosen_eq_of_renumbered`). -/
def Molecule.canonical : Molecule → Except (List Char) (List Char) :=
  Quotient.lift (fun mol => writeChosen mol.1)
    (fun a b h => writeChosen_eq_of_renumbered a.1 b.1 a.2 b.2 h)

/-- The canonical text of a molecule. `none` where the writer of `canonical`
gives no text for it. -/
def Molecule.canonicalText (molecule : Molecule) : Option CanonicalText :=
  match h : molecule.canonical with
  | .ok text => some ⟨text, by
      induction molecule using Quotient.inductionOn with
      | _ a => exact ⟨a.1, h⟩⟩
  | .error _ => none

/-- The molecule that a canonical text is read as. The reader reads every
canonical text (`read_of_writeChosen`), and what it returns is well formed
(theorem 8). -/
def CanonicalText.molecule (text : CanonicalText) : Molecule :=
  match h : read text.1 with
  | .ok mol => Molecule.of mol (read_wellFormed text.1 mol h)
  | .error _ => False.elim (by
      obtain ⟨m, hm⟩ := text.2
      obtain ⟨c, hr, _, _⟩ := read_of_writeChosen m text.1 hm
      rw [h] at hr
      cases hr)

/-- Theorem 45 of CLAIMS.md, fifth statement. The first map is the writer of
`canonical`: a text is the canonical text of the molecule of a `Mol` exactly
when the writer of `canonical` gives that text for the `Mol`. -/
theorem Molecule.canonicalText_of (mol : Mol) (w : mol.WellFormed) (text : CanonicalText) :
    (Molecule.of mol w).canonicalText = some text ↔ writeChosen mol = .ok text.1 := by
  have hc : (Molecule.of mol w).canonical = writeChosen mol := rfl
  unfold Molecule.canonicalText
  split
  · rename_i t h
    rw [hc] at h
    rw [h]
    constructor
    · intro e
      rw [← Option.some.inj e]
    · intro e
      exact congrArg some (Subtype.ext (Except.ok.inj e))
  · rename_i e h
    rw [hc] at h
    rw [h]
    simp

/-- Theorem 45 of CLAIMS.md, sixth statement. The second map is the reader: if
a canonical text is read as a `Mol`, its molecule is the molecule of that
`Mol`. -/
theorem CanonicalText.molecule_of (text : CanonicalText) (mol : Mol)
    (h : read text.1 = .ok mol) :
    text.molecule = Molecule.of mol (read_wellFormed text.1 mol h) := by
  unfold CanonicalText.molecule
  split
  · rename_i mol' h'
    have e : mol' = mol := Except.ok.inj (h'.symm.trans h)
    subst e
    rfl
  · rename_i e h'
    rw [h] at h'
    cases h'

/-! ## The correspondence -/

/-- Theorem 45 of CLAIMS.md, first statement. **Molecules and canonical texts
correspond one to one.** A canonical text is the canonical text of a molecule
exactly when it is read as that molecule. (A text that is not canonical, such
as `OCC`, is read as a molecule as well, and is not its canonical text.)

So the writer of `canonical` and the reader undo each other, between the
molecules that have a canonical text and the canonical texts. A molecule for
which the writer of `canonical` gives no text has no canonical text, and then
no canonical text is read as it. -/
theorem Molecule.canonicalText_eq_some_iff (molecule : Molecule) (text : CanonicalText) :
    molecule.canonicalText = some text ↔ text.molecule = molecule := by
  induction molecule using Quotient.inductionOn with
  | _ a =>
    show (Molecule.of a.1 a.2).canonicalText = some text ↔ text.molecule = Molecule.of a.1 a.2
    rw [Molecule.canonicalText_of]
    obtain ⟨m, hm⟩ := text.2
    obtain ⟨c, hr, hw, _⟩ := read_of_writeChosen m text.1 hm
    have wc := read_wellFormed text.1 c hr
    rw [text.molecule_of c hr, Molecule.of_eq_of_iff]
    constructor
    · intro h
      exact ((writeChosen_eq_iff a.1 c text.1 h).1 hw).2.symm
    · intro h
      rw [← writeChosen_eq_of_renumbered c a.1 wc a.2 h]
      exact hw

/-- Theorem 45 of CLAIMS.md, second statement. Two canonical texts that are
read as the same molecule are equal: different canonical texts are different
molecules. -/
theorem CanonicalText.molecule_injective : Function.Injective CanonicalText.molecule := by
  intro t₁ t₂ h
  have h₁ := (Molecule.canonicalText_eq_some_iff t₁.molecule t₁).2 rfl
  have h₂ := (Molecule.canonicalText_eq_some_iff t₁.molecule t₂).2 h.symm
  exact Option.some.inj (h₁.symm.trans h₂)

end VeriMol
