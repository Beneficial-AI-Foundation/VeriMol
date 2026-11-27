import VeriMol.Core.Run
import VeriMol.Proofs.RoundTrip

/-!
# What `rewrite` and `plain` print is read as the same `Mol`

This file proves theorems 13 to 16 of CLAIMS.md, and the two spellings of
acetic acid of theorem 39. Theorems 13 to 16 follow from the round trip of the
two spellings (theorems 11 and 12, `VeriMol/Proofs/RoundTrip.lean`), because
the program prints a text only if it read the original text and wrote the
`Mol` it found. The two examples Lean works out itself.

These theorems say that a text that comes out is right. They do not say that a
text comes out.
-/

namespace VeriMol

/-- If `rewritten` prints a text, then the original text was read as some
`Mol`, and the printed text is read as the same `Mol`. This holds for every
writer whose texts are read back as the `Mol` that was written. -/
theorem rewritten_same_mol {writer : Mol → Except (List Char) (List Char)}
    (hwriter : ∀ mol text, writer mol = .ok text → read text = .ok mol)
    {original written : List Char}
    (h : rewritten writer original
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    ∃ mol, read original = .ok mol ∧ read written = .ok mol := by
  unfold rewritten at h
  split at h
  · simp [Output.error] at h
  · rename_i mol hmol
    split at h
    · rename_i text htext
      have hsame : text = written := by
        simpa [Output.ok] using h
      exact ⟨mol, hmol, hsame ▸ hwriter mol text htext⟩
    · simp [Output.error] at h

/-- Theorem 13 of CLAIMS.md. Rewriting never changes what a text says.

Take the command `rewrite` or `plain` and any text `original`. If the program
succeeds and prints a text `written` (followed by a line break), then the
original was read as some `Mol`, and reading `written` returns that same
`Mol`. -/
theorem run_rewrite_same_mol (word original written : List Char)
    (hword : word = "rewrite".toList ∨ word = "plain".toList)
    (h : run [word, original] = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    ∃ mol, read original = .ok mol ∧ read written = .ok mol := by
  rcases hword with rfl | rfl
  · have hrun : run ["rewrite".toList, original] = rewritten write original := by
      simp [run]
    rw [hrun] at h
    exact rewritten_same_mol read_write h
  · have hrun : run ["plain".toList, original] = rewritten writePlain original := by
      simp [run]
    rw [hrun] at h
    exact rewritten_same_mol read_writePlain h

/-- Theorem 14 of CLAIMS.md. Rewriting a rewritten text gives the same text
again. If the program printed `written` for `original`, it prints exactly the
same for `written`. -/
theorem run_rewrite_again (word original written : List Char)
    (hword : word = "rewrite".toList ∨ word = "plain".toList)
    (h : run [word, original] = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    run [word, written] = run [word, original] := by
  obtain ⟨mol, horiginal, hwritten⟩ := run_rewrite_same_mol word original written hword h
  rcases hword with rfl | rfl <;> simp [run, rewritten, horiginal, hwritten]

/-- Theorem 15 of CLAIMS.md. The writer never gives two different `Mol`s the
same text for `rewrite`. -/
theorem write_injective (m₁ m₂ : Mol) (text : List Char)
    (h₁ : write m₁ = .ok text) (h₂ : write m₂ = .ok text) : m₁ = m₂ := by
  have h := (read_write m₁ text h₁).symm.trans (read_write m₂ text h₂)
  simpa using h

/-- Theorem 16 of CLAIMS.md. With `rewrite`, and with `plain`: two texts that
are both written back get the same text exactly when they are read as the same
`Mol`. So each of the two commands gives one text for every `Mol` that it can
write, and tells two `Mol`s apart: also two that are the same molecule numbered
differently. -/
theorem run_rewrite_eq_iff (word t₁ t₂ w₁ w₂ : List Char)
    (hword : word = "rewrite".toList ∨ word = "plain".toList)
    (h₁ : run [word, t₁] = { stdout := w₁ ++ ['\n'], stderr := [], exitCode := 0 })
    (h₂ : run [word, t₂] = { stdout := w₂ ++ ['\n'], stderr := [], exitCode := 0 }) :
    w₁ = w₂ ↔ read t₁ = read t₂ := by
  obtain ⟨m₁, hr₁, hw₁⟩ := run_rewrite_same_mol word t₁ w₁ hword h₁
  obtain ⟨m₂, hr₂, hw₂⟩ := run_rewrite_same_mol word t₂ w₂ hword h₂
  constructor
  · intro h
    subst h
    rw [hr₁, hr₂, ← hw₁, hw₂]
  · intro h
    have e : run [word, t₁] = run [word, t₂] := by
      rcases hword with rfl | rfl <;> simp [run, rewritten, h]
    rw [h₁, h₂] at e
    simpa using e

/-! ## Single examples

Lean works these out itself. The texts are those of the table in SPEC.md,
section 9.2, and the `Mol` is the one of acetic acid, as SPEC.md, section 7,
prints it. It is written out in each statement, so that the statement can be
read on its own. -/

/-- Theorem 39 of CLAIMS.md, for the plain spelling of acetic acid. -/
theorem writePlain_aceticAcid :
    writePlain
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 1, b := 3, order := .single } ] }
      = .ok "[CH3]-[C]-1=[O].[OH]1".toList := by
  rfl

/-- Theorem 39 of CLAIMS.md, for the spelling of acetic acid with round
brackets. -/
theorem write_aceticAcid :
    write
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 1, b := 3, order := .single } ] }
      = .ok "CC(=O)O".toList := by
  rfl

end VeriMol
