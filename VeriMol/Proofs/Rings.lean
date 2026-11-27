import VeriMol.Core

/-!
# The table of open ring numbers: its three laws

The laws of the table of `VeriMol/Core/Rings.lean`, one for each of its three
uses: what `ringAt` finds after a pair is put in front, what it finds after a
number is taken out (`withoutRing`), and that a table in which no number is
found is empty.
-/

namespace VeriMol

theorem ringAt_cons {α : Type} (k n : Nat) (v : α) (t : List (Nat × α)) :
    ringAt k ((n, v) :: t) = if n = k then some v else ringAt k t := rfl

theorem ringAt_withoutRing {α : Type} (k n : Nat) (t : List (Nat × α)) :
    ringAt k (withoutRing n t) = if n = k then none else ringAt k t := by
  induction t with
  | nil => simp [withoutRing, ringAt]
  | cons e t ih =>
    obtain ⟨n', v⟩ := e
    by_cases h : n' = n
    · subst h
      have : withoutRing n' ((n', v) :: t) = withoutRing n' t := by simp [withoutRing]
      rw [this, ih]
      by_cases hk : n' = k <;> simp [ringAt, hk]
    · have : withoutRing n ((n', v) :: t) = (n', v) :: withoutRing n t := by
        simp [withoutRing, h]
      rw [this]
      by_cases hk : n' = k
      · subst hk; simp [ringAt, Ne.symm h]
      · simp [ringAt, hk, ih]

theorem eq_nil_of_ringAt_none {α : Type} (t : List (Nat × α)) (h : ∀ k, ringAt k t = none) :
    t = [] := by
  cases t with
  | nil => rfl
  | cons e t =>
    obtain ⟨n, v⟩ := e
    have := h n
    simp [ringAt] at this

end VeriMol
