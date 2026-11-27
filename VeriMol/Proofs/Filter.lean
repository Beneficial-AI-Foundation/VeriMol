import VeriMol.Core.Filter
import VeriMol.Proofs.FluoroGroup
import VeriMol.Proofs.Printed
import VeriMol.Proofs.Sound

/-!
# What passes the filter: theorem 49 of CLAIMS.md

The filter (`VeriMol/Core/Filter.lean`) reads a SMILES text, asks whether the
`Mol` is sound, asks the checker of a rule, and then hands the `Mol` on or
refuses. This file proves what that gives.

1. For any rule: if the checker of the rule is right for every sound `Mol`,
   then the filter hands on a `Mol` exactly when the text is read as that
   `Mol`, the `Mol` is sound, and the rule holds for it (`filter_eq_ok_iff`).
   This is proven once. It rests on the checker of soundness being right
   (theorem 46), and it asks no more of the checker of a rule than this:
   to say yes, for a sound `Mol`, exactly when the rule holds.
2. For the rule that is built, "no perfluorinated group of `n` or more
   carbon atoms": the filter hands on a `Mol` exactly when the text is read as
   it, it is sound, and it has no such group (`filterPerfluoro_eq_ok_iff`).
   The checker of this rule is right for every `Mol` (theorem 48), which is
   more than the first statement asks.
3. The same said of the program (`run_filter_eq_iff`, `run_filter_exitCode_iff`):
   the command prints a `Mol` and ends with exit code 0 exactly in that case.
   The other two statements of theorem 49 stand in `VeriMol/Proofs/Run.lean`:
   that the command gives the answer of the filter (`run_filter`), and which
   texts are a number behind `filter perfluoro` (`groupSize?_eq_some_iff`).

The statements are about the `Mol` that is handed on: the object itself,
not a text for it. What is not said here: that the rule and `Sound` are the
right ones, and that the reader reads a SMILES as a chemist does (CLAIMS.md,
"Trusted"). And no statement says that a compound which passes is harmless.
-/

namespace VeriMol

/-- Theorem 49 of CLAIMS.md, for every rule. Let `allows` be the checker of a
rule `Rule`, and let it be right for every sound `Mol`: it says yes exactly
when the rule holds. Then the filter hands on the `Mol` `m` for a text exactly
when the reader gives `m` for the text, `m` is sound, and the rule holds for
`m`.

The reason that a refusal gives, `refusal`, plays no part in this. -/
theorem filter_eq_ok_iff {allows : Mol → Bool} {Rule : Mol → Prop} (refusal : Mol → List Char)
    (right : ∀ m, m.Sound → (allows m = true ↔ Rule m)) (text : List Char) (m : Mol) :
    filter allows refusal text = .ok m ↔ read text = .ok m ∧ m.Sound ∧ Rule m := by
  unfold filter
  cases hr : read text with
  | error problem => simp
  | ok mol =>
    simp only [Except.ok.injEq]
    cases hs : mol.soundProblem with
    | some reason =>
      -- the checker of soundness found a reason, so the `Mol` is not sound
      simp only [reduceCtorEq, false_iff, not_and]
      rintro rfl sound
      rw [(Mol.soundProblem_eq_none_iff mol).2 sound] at hs
      cases hs
    | none =>
      have sound : mol.Sound := (Mol.soundProblem_eq_none_iff mol).1 hs
      simp only
      split
      · rename_i yes
        simp only [Except.ok.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, sound, (right mol sound).1 yes⟩
        · rintro ⟨rfl, _, _⟩
          rfl
      · rename_i no
        simp only [reduceCtorEq, false_iff, not_and]
        rintro rfl _ holds
        exact no ((right mol sound).2 holds)

/-- Theorem 49 of CLAIMS.md, the statement that counts. The filter with the
rule `perfluoro` hands on the `Mol` `m` for a text exactly when all of this
holds:

* the reader gives `m` for the text;
* `m` is sound (`VeriMol/Proofs/Predicates/Sound.lean`);
* `m` has no perfluorinated group of `n` or more carbon atoms
  (`VeriMol/Proofs/Predicates/FluoroGroup.lean`).

So whatever passes the filter is proven to satisfy the rule, and no `Mol` that
is read, is sound and satisfies the rule is held back. -/
theorem filterPerfluoro_eq_ok_iff (n : Nat) (text : List Char) (m : Mol) :
    filterPerfluoro n text = .ok m ↔ read text = .ok m ∧ m.Sound ∧ m.NoFluoroGroup n :=
  filter_eq_ok_iff _ (fun mol _ => Mol.hasNoFluoroGroup_iff mol n) text m

/-- Theorem 49 of CLAIMS.md, said of the program. Behind the words `filter`
and `perfluoro` and a number `n` from 1 on, the program prints the printed
layout of the `Mol` `m` and nothing else, and ends with exit code 0, exactly
when the reader gives `m` for the text, `m` is sound, and `m` has no
perfluorinated group of `n` or more carbon atoms. The printed layout tells
two `Mol`s apart (theorem 2), so what is printed is this `Mol` and no
other. -/
theorem run_filter_eq_iff (size text : List Char) (n : Nat) (hsize : groupSize? size = some n)
    (m : Mol) :
    run ["filter".toList, "perfluoro".toList, size, text]
        = { stdout := m.printed, stderr := [], exitCode := 0 }
      ↔ read text = .ok m ∧ m.Sound ∧ m.NoFluoroGroup n := by
  rw [run_filter size text n hsize, ← filterPerfluoro_eq_ok_iff]
  cases filterPerfluoro n text with
  | error reason => simp
  | ok mol =>
    simp only [Output.mk.injEq, and_true, Except.ok.injEq]
    exact ⟨Mol.printed_injective mol m, fun same => by rw [same]⟩

/-- Theorem 49 of CLAIMS.md, for the exit code. Behind the words `filter` and
`perfluoro` and a number `n` from 1 on, the program ends with exit code 0
exactly when the text is read as a `Mol` that is sound and has no
perfluorinated group of `n` or more carbon atoms. In every other case it
ends with exit code 1 (theorem 1). -/
theorem run_filter_exitCode_iff (size text : List Char) (n : Nat)
    (hsize : groupSize? size = some n) :
    (run ["filter".toList, "perfluoro".toList, size, text]).exitCode = 0
      ↔ ∃ m, read text = .ok m ∧ m.Sound ∧ m.NoFluoroGroup n := by
  rw [run_filter size text n hsize]
  constructor
  · intro h
    cases hg : filterPerfluoro n text with
    | error reason => rw [hg] at h; cases h
    | ok mol => exact ⟨mol, (filterPerfluoro_eq_ok_iff n text mol).1 hg⟩
  · rintro ⟨m, h⟩
    rw [(filterPerfluoro_eq_ok_iff n text m).2 h]

end VeriMol
