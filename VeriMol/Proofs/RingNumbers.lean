import VeriMol.Proofs.Brackets
import VeriMol.Proofs.Refusal
import VeriMol.Proofs.Spelled

/-!
# When a spelling gives a text: a count of the open ring numbers

The writer keeps a table of the ring numbers that are in use
(`VeriMol/Core/WriteParts.lean`). It can fail in two ways: it finds no free
number among the 99, or it does not find the number of a ring bond that it is
to close. This file shows what the table holds while a spelling goes through
the atoms, and what follows from that, for both spellings:

* The second way does not happen for a well formed `Mol`: the writer finds
  the number of every ring bond that it closes (`closeRings_counted`, for a
  table as `Counted` describes it; `tokensFrom_tooManyRingNumbers` keeps
  the table so). So the message about ring numbers is true whenever a
  spelling gives it, for every `Mol`, with or without stereo facts
  (`Spelling.write_tooManyRingNumbers_sound`).
* For a well formed `Mol` without stereo facts whose atoms can all be
  written, the first way happens exactly when more than 99 ring numbers are
  open at the same time, and the writer has no other reason to refuse.

"Open behind atom `i`" is said without the writer's table: a ring number is
open behind atom `i` for every bond that begins at atom `i` or before it,
ends behind atom `i`, and is written with a ring number, which is so unless
its later atom is written next to its earlier atom (`ringBond`). In the
plain spelling these are the bonds that do not join two atoms that follow
each other (`plain_ringBond_iff`), so there the count needs no function of
the writer at all (SPEC.md, section 9.1). In the spelling with round
brackets it depends on the parents (section 9.2).

Theorem 19 of CLAIMS.md says this in seven statements, in the second half of
the file. For both spellings: when a spelling gives a text for a `Mol` without
stereo facts, when it answers with the message about ring numbers, and that
this message is true for every `Mol`. For the plain spelling the first two
with the count that needs no parents, and for the commands `rewrite` and
`plain` when they print the error about ring numbers. Theorem 17 says the
first in the words of the writer's own functions, and theorem 18 says only
that no other message can come.

All but one of the statements are about a `Mol` without stereo facts: for a
`Mol` with stereo facts the writer has more reasons to refuse (SPEC.md,
section 12.3), and no theorem says in plain words when they come.

The proof follows the writer atom by atom. In front of atom `i` its table
holds exactly the ring bonds that are open there, each under one number
(`Counted`). A bond that opens gets a free number as long as fewer than 99
are in use, and with 99 in use none is free (`openRings_counted`): a
table without a number twice, whose numbers are all among the 99, holds 99
entries at most; and a table of fewer than 99 entries leaves a number free.
-/

namespace VeriMol

/-! ## A table without a number twice -/

/-- A number that is looked up and not found is no number of the table. -/
theorem not_key_of_ringAt_none {α : Type} {k : Nat} :
    ∀ {t : List (Nat × α)}, ringAt k t = none → k ∉ t.map (·.1)
  | [], _ => by simp
  | (n, w) :: t, h => by
    rw [ringAt_cons] at h
    by_cases hn : n = k
    · simp [hn] at h
    · simp [hn] at h
      have := not_key_of_ringAt_none h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun hk => hn hk.symm, this⟩

/-- In a table without a number twice, an entry is found under its number. -/
theorem ringAt_of_entry {α : Type} {k : Nat} {v : α} :
    ∀ {t : List (Nat × α)}, (t.map (·.1)).Nodup → (k, v) ∈ t → ringAt k t = some v
  | [], _, h => by simp at h
  | (n, w) :: t, hd, h => by
    rw [List.map_cons, List.nodup_cons] at hd
    rw [ringAt_cons]
    rcases List.mem_cons.1 h with h | h
    · cases h
      simp
    · have hne : n ≠ k := by
        intro hn
        subst hn
        exact hd.1 (List.mem_map.2 ⟨(n, v), h, rfl⟩)
      simp [hne]
      exact ringAt_of_entry hd.2 h

/-- In a table without a bond twice, a bond stands under one number only. -/
theorem key_of_bond {k k' : Nat} {e : Bond} :
    ∀ {t : List (Nat × Bond)}, (t.map (·.2)).Nodup → (k, e) ∈ t → (k', e) ∈ t → k = k'
  | [], _, h, _ => by simp at h
  | (n, w) :: t, hd, h, h' => by
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.1 h with h1 | h1 <;> rcases List.mem_cons.1 h' with h2 | h2
    · cases h1; cases h2; rfl
    · cases h1
      exact (hd.1 (List.mem_map.2 ⟨(k', e), h2, rfl⟩)).elim
    · cases h2
      exact (hd.1 (List.mem_map.2 ⟨(k, e), h1, rfl⟩)).elim
    · exact key_of_bond hd.2 h1 h2

/-- What is left when a number is taken out: every entry under another number. -/
theorem mem_withoutRing {α : Type} {k : Nat} {entry : Nat × α} {t : List (Nat × α)} :
    entry ∈ withoutRing k t ↔ entry ∈ t ∧ entry.1 ≠ k := by
  simp [withoutRing]

/-! ## The 99 ring numbers -/

/-- A number that the writer takes as free is one of the 99. -/
theorem freeNumber_mem {W : List (Nat × Bond)} {k : Nat} (h : freeNumber W = some k) :
    k ∈ ringNumbers := by
  unfold freeNumber at h
  exact List.mem_of_find?_eq_some h

/-- While the table has fewer than 99 entries, the writer finds a free number. -/
theorem freeNumber_of_lt {W : List (Nat × Bond)} (h : W.length < 99) :
    ∃ k, freeNumber W = some k := by
  cases hf : freeNumber W with
  | some k => exact ⟨k, rfl⟩
  | none =>
    exfalso
    unfold freeNumber at hf
    rw [List.find?_eq_none] at hf
    have hsub : ringNumbers ⊆ W.map (·.1) := by
      intro k hk
      have hnot := hf k hk
      cases hr : ringAt k W with
      | none => simp [hr] at hnot
      | some v => exact List.mem_map.2 ⟨(k, v), mem_of_ringAt hr, rfl⟩
    have hnodup : ringNumbers.Nodup := by
      unfold ringNumbers
      exact List.nodup_range'
    have := List.Nodup.length_le_of_subset hnodup hsub
    simp [ringNumbers] at this
    omega

/-! ## What the counting knows about the writer's table -/

/-- The writer's table, as the counting sees it: no number stands in it twice,
every number is one of the 99, no bond stands in it twice, and its bonds are
exactly the bonds of `l` with the property `Q`. It says more than `TableHolds`
of `VeriMol/Proofs/Follow.lean`, which the round trip uses: the bonds of the
table are exactly those with the property, so its entries can be counted. -/
structure Counted (l : List Bond) (Q : Bond → Prop) (W : List (Nat × Bond)) : Prop where
  numbers : (W.map (·.1)).Nodup
  inRange : ∀ entry ∈ W, entry.1 ∈ ringNumbers
  once : (W.map (·.2)).Nodup
  bonds : ∀ e, e ∈ W.map (·.2) ↔ e ∈ l ∧ Q e

/-- The property may be replaced by one that says the same of every bond of `l`. -/
theorem Counted.congr {l : List Bond} {Q Q' : Bond → Prop} {W : List (Nat × Bond)}
    (h : Counted l Q W) (hQ : ∀ e ∈ l, (Q e ↔ Q' e)) : Counted l Q' W :=
  ⟨h.numbers, h.inRange, h.once, fun e => by
    rw [h.bonds e]
    exact ⟨fun ⟨hl, hq⟩ => ⟨hl, (hQ e hl).1 hq⟩, fun ⟨hl, hq⟩ => ⟨hl, (hQ e hl).2 hq⟩⟩⟩

/-- Such a table holds 99 entries at most. -/
theorem Counted.length_le {l : List Bond} {Q : Bond → Prop} {W : List (Nat × Bond)}
    (h : Counted l Q W) : W.length ≤ 99 := by
  have hsub : W.map (·.1) ⊆ ringNumbers := by
    intro k hk
    obtain ⟨entry, he, hke⟩ := List.mem_map.1 hk
    exact hke ▸ h.inRange entry he
  have := List.Nodup.length_le_of_subset h.numbers hsub
  simpa [ringNumbers] using this

/-- It holds as many entries as `l` has bonds with the property. -/
theorem Counted.length_eq {l : List Bond} (hl : l.Nodup) {Q : Bond → Prop} [DecidablePred Q]
    {W : List (Nat × Bond)} (h : Counted l Q W) :
    W.length = (l.filter fun e => decide (Q e)).length := by
  have hperm : (W.map (·.2)).Perm (l.filter fun e => decide (Q e)) :=
    (List.perm_ext_iff_of_nodup h.once (hl.sublist List.filter_sublist)).2 (by
      intro e
      rw [h.bonds e]
      simp [List.mem_filter])
  simpa using hperm.length_eq

/-- Closing one bond of the table: the writer finds its number, and the bond
is gone. -/
theorem Counted.close {l : List Bond} (hl : l.Pairwise Bond.before) {Q : Bond → Prop}
    {W : List (Nat × Bond)} (h : Counted l Q W) {c : Bond} (hc : c ∈ l) (hq : Q c) :
    ∃ k, numberOf W c = some k ∧ Counted l (fun e => Q e ∧ e ≠ c) (withoutRing k W) := by
  -- the bond stands in the table, under some number
  obtain ⟨⟨k0, c0⟩, hmem, hc0⟩ := List.mem_map.1 ((h.bonds c).2 ⟨hc, hq⟩)
  simp only at hc0
  subst hc0
  have hat : ringAt k0 W = some c0 := ringAt_of_entry h.numbers hmem
  -- so the writer finds a number
  have hsome : (numberOf W c0).isSome = true := by
    unfold numberOf
    rw [List.find?_isSome]
    exact ⟨k0, h.inRange _ hmem, by simp [hat]⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨k, hk, ?_⟩
  -- and the number it finds stands for this very bond
  obtain ⟨e, he, ha, hb⟩ := numberOf_some hk
  have hemem : (k, e) ∈ W := mem_of_ringAt he
  have hel := (h.bonds e).1 (List.mem_map.2 ⟨(k, e), hemem, rfl⟩)
  have hec : e = c0 := key_unique hl hel.1 hc ha hb
  subst hec
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h.numbers
  · intro entry hentry
    exact h.inRange entry (mem_withoutRing.1 hentry).1
  · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h.once
  · intro x
    constructor
    · intro hx
      obtain ⟨⟨k', x'⟩, hx', hxx⟩ := List.mem_map.1 hx
      simp only at hxx
      subst hxx
      obtain ⟨hxW, hkk⟩ := mem_withoutRing.1 hx'
      have hxl := (h.bonds x').1 (List.mem_map.2 ⟨(k', x'), hxW, rfl⟩)
      refine ⟨hxl.1, hxl.2, ?_⟩
      intro hxe
      subst hxe
      exact hkk (key_of_bond h.once hxW hemem)
    · rintro ⟨hxl, hxq, hne⟩
      obtain ⟨⟨k', x'⟩, hx', hxx⟩ := List.mem_map.1 ((h.bonds x).2 ⟨hxl, hxq⟩)
      simp only at hxx
      subst hxx
      refine List.mem_map.2 ⟨(k', x'), mem_withoutRing.2 ⟨hx', ?_⟩, rfl⟩
      intro hkk
      simp only at hkk
      subst hkk
      have := ringAt_of_entry h.numbers hx'
      rw [he] at this
      cases this
      exact hne rfl

/-- Opening one bond that is not in the table, under a number that the writer
found free. -/
theorem Counted.open {l : List Bond} {Q : Bond → Prop} {W : List (Nat × Bond)} (h : Counted l Q W)
    {c : Bond} (hc : c ∈ l) (hnq : ¬ Q c) {k : Nat} (hk : freeNumber W = some k) :
    Counted l (fun e => Q e ∨ e = c) ((k, c) :: W) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨not_key_of_ringAt_none (freeNumber_some hk), h.numbers⟩
  · intro entry hentry
    rcases List.mem_cons.1 hentry with hentry | hentry
    · subst hentry
      exact freeNumber_mem hk
    · exact h.inRange entry hentry
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨fun hmem => hnq ((h.bonds c).1 hmem).2, h.once⟩
  · intro x
    simp only [List.map_cons, List.mem_cons]
    constructor
    · rintro (hx | hx)
      · subst hx
        exact ⟨hc, Or.inr rfl⟩
      · exact ⟨((h.bonds x).1 hx).1, Or.inl ((h.bonds x).1 hx).2⟩
    · rintro ⟨hxl, hq | hq⟩
      · exact Or.inr ((h.bonds x).2 ⟨hxl, hq⟩)
      · exact Or.inl hq

/-! ## The ring numbers of one atom -/

/-- The ring numbers that close at an atom: the writer finds every one of them. -/
theorem closeRings_counted {l : List Bond} (hl : l.Pairwise Bond.before) :
    ∀ (closing : List Bond) {Q : Bond → Prop} {W : List (Nat × Bond)}, Counted l Q W →
      closing.Nodup → (∀ c ∈ closing, c ∈ l ∧ Q c) →
      ∃ tokens left, closeRings W closing = some (tokens, left) ∧
        Counted l (fun e => Q e ∧ e ∉ closing) left
  | [], Q, W, h, _, _ => ⟨[], W, rfl, h.congr (fun e _ => by simp)⟩
  | c :: rest, Q, W, h, hnd, hall => by
    rw [List.nodup_cons] at hnd
    obtain ⟨k, hk, hW⟩ := h.close hl (hall c List.mem_cons_self).1 (hall c List.mem_cons_self).2
    obtain ⟨tokens, left, hclose, hleft⟩ := closeRings_counted hl rest hW hnd.2 (by
      intro x hx
      exact ⟨(hall x (List.mem_cons_of_mem _ hx)).1, (hall x (List.mem_cons_of_mem _ hx)).2,
        fun hxc => hnd.1 (hxc ▸ hx)⟩)
    refine ⟨.ring k :: tokens, left, ?_, ?_⟩
    · simp [closeRings, hk, hclose]
    · refine hleft.congr (fun e _ => ?_)
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨hq, hne⟩, hnr⟩
        exact ⟨hq, hne, hnr⟩
      · rintro ⟨hq, hne, hnr⟩
        exact ⟨⟨hq, hne⟩, hnr⟩

/-- The ring numbers that open at an atom: the writer finds a free number for
every one of them exactly when the table and they together are 99 at most. -/
theorem openRings_counted {l : List Bond} (symbol : Bond → List Token) :
    ∀ (opening : List Bond) {Q : Bond → Prop} {W : List (Nat × Bond)}, Counted l Q W →
      opening.Nodup → (∀ c ∈ opening, c ∈ l ∧ ¬ Q c) →
      (W.length + opening.length ≤ 99 →
        ∃ tokens left, openRings symbol W opening = some (tokens, left) ∧
          Counted l (fun e => Q e ∨ e ∈ opening) left) ∧
      (99 < W.length + opening.length → openRings symbol W opening = none)
  | [], Q, W, h, _, _ => by
    refine ⟨fun _ => ⟨[], W, rfl, h.congr (fun e _ => by simp)⟩, fun hlt => ?_⟩
    have := h.length_le
    simp at hlt
    omega
  | c :: rest, Q, W, h, hnd, hall => by
    rw [List.nodup_cons] at hnd
    have hc := hall c List.mem_cons_self
    have hrest : ∀ k, freeNumber W = some k → ∀ x ∈ rest, x ∈ l ∧ ¬ (Q x ∨ x = c) := by
      intro k _ x hx
      refine ⟨(hall x (List.mem_cons_of_mem _ hx)).1, ?_⟩
      rintro (hq | hxc)
      · exact (hall x (List.mem_cons_of_mem _ hx)).2 hq
      · exact hnd.1 (hxc ▸ hx)
    constructor
    · intro hle
      simp only [List.length_cons] at hle
      obtain ⟨k, hk⟩ := freeNumber_of_lt (W := W) (by omega)
      obtain ⟨tokens, left, hopen, hleft⟩ :=
        (openRings_counted symbol rest (h.open hc.1 hc.2 hk) hnd.2 (hrest k hk)).1 (by
          simp only [List.length_cons]; omega)
      refine ⟨symbol c ++ .ring k :: tokens, left, ?_, ?_⟩
      · simp [openRings, hk, hopen]
      · refine hleft.congr (fun e _ => ?_)
        simp only [List.mem_cons]
        constructor
        · rintro ((hq | he) | he)
          · exact Or.inl hq
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr he)
        · rintro (hq | he | he)
          · exact Or.inl (Or.inl hq)
          · exact Or.inl (Or.inr he)
          · exact Or.inr he
    · intro hlt
      simp only [List.length_cons] at hlt
      cases hk : freeNumber W with
      | none => simp [openRings, hk]
      | some k =>
        have := (openRings_counted symbol rest (h.open hc.1 hc.2 hk) hnd.2 (hrest k hk)).2 (by
          simp only [List.length_cons]; omega)
        simp [openRings, hk, this]

/-! ## The atoms, one after the other -/

/-- A ring number is open for this bond in front of atom `i`: the bond begins
before the atom, ends at it or behind it, and is written with a ring number.
`ring` says which bonds are. -/
abbrev OpenAt (ring : Bond → Bool) (i : Nat) (e : Bond) : Prop :=
  e.a < i ∧ i ≤ e.b ∧ ring e = true

/-- The same, once the numbers that close at atom `i` are closed: the bond
ends behind the atom. -/
abbrev StaysAt (ring : Bond → Bool) (i : Nat) (e : Bond) : Prop :=
  e.a < i ∧ i < e.b ∧ ring e = true

/-- If an entry has `p` exactly when it has `q` or `r`, and no entry has both
`q` and `r`, then the entries with `p` are as many as those with `q` and
those with `r` together. -/
theorem length_filter_split {α : Type} (p q r : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = (q x || r x)) → (∀ x ∈ l, ¬ (q x = true ∧ r x = true)) →
      (l.filter p).length = (l.filter q).length + (l.filter r).length
  | [], _, _ => by simp
  | x :: l, h, hno => by
    have ih := length_filter_split p q r l (fun y hy => h y (List.mem_cons_of_mem _ hy))
      (fun y hy => hno y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    have hnx := hno x List.mem_cons_self
    cases hq : q x <;> cases hr : r x <;> simp [hx, hq, hr, ih] at hnx ⊢ <;> omega

/-- The ring numbers of one atom. With the table as it must be in front of
atom `i`, the writer finds the numbers that close at the atom. It finds a free
number for each bond that opens there exactly when no more than 99 ring
numbers are open behind the atom, and the table is then as it must be in
front of the next atom. -/
theorem rings_counted {l : List Bond} (hl : l.Pairwise Bond.before) (hab : ∀ e ∈ l, e.a < e.b)
    (ring : Bond → Bool) (symbol : Bond → List Token) (i : Nat) {W : List (Nat × Bond)}
    (h : Counted l (OpenAt ring i) W) :
    ∃ closing afterClosing,
      closeRings W (l.filter fun bond => bond.b == i && ring bond)
        = some (closing, afterClosing) ∧
      ((l.filter fun e => decide (OpenAt ring (i + 1) e)).length ≤ 99 →
        ∃ opening left,
          openRings symbol afterClosing (l.filter fun bond => bond.a == i && ring bond)
            = some (opening, left) ∧ Counted l (OpenAt ring (i + 1)) left) ∧
      (99 < (l.filter fun e => decide (OpenAt ring (i + 1) e)).length →
        openRings symbol afterClosing (l.filter fun bond => bond.a == i && ring bond)
          = none) := by
  have hnodup : l.Nodup := nodup_of_ordered hl
  -- the ring numbers that close at this atom
  obtain ⟨closing, afterClosing, hclose, hafter⟩ :=
    closeRings_counted hl (l.filter fun bond => bond.b == i && ring bond) h
      (hnodup.sublist List.filter_sublist) (by
        intro c hc
        obtain ⟨hcl, hcp⟩ := List.mem_filter.1 hc
        have := hab c hcl
        simp only [Bool.and_eq_true, beq_iff_eq] at hcp
        exact ⟨hcl, by omega, by omega, hcp.2⟩)
  have hstays : Counted l (StaysAt ring i) afterClosing := by
    refine hafter.congr (fun e he => ?_)
    have := hab e he
    simp only [List.mem_filter, he, true_and, Bool.and_eq_true, beq_iff_eq]
    unfold OpenAt StaysAt
    cases ring e <;> simp <;> omega
  -- the ring numbers that open at this atom
  have hopening := openRings_counted (l := l) symbol
    (l.filter fun bond => bond.a == i && ring bond) hstays
    (hnodup.sublist List.filter_sublist) (by
      intro c hc
      obtain ⟨hcl, hcp⟩ := List.mem_filter.1 hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hcp
      exact ⟨hcl, fun hs => by have := hs.1; omega⟩)
  -- how many are open behind the atom: those that stay, and those that open
  have hcount : (l.filter fun e => decide (OpenAt ring (i + 1) e)).length
      = afterClosing.length + (l.filter fun bond => bond.a == i && ring bond).length := by
    rw [hstays.length_eq hnodup]
    refine length_filter_split _ _ _ l (fun e he => ?_) (fun e he => ?_)
    · have := hab e he
      rw [Bool.eq_iff_iff]
      simp only [OpenAt, StaysAt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      cases ring e <;> simp <;> omega
    · simp only [StaysAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rintro ⟨⟨h1, _⟩, h2, _⟩
      omega
  refine ⟨closing, afterClosing, hclose, fun hle => ?_, fun hlt => hopening.2 (by omega)⟩
  obtain ⟨opening, left, hopen, hleft⟩ := hopening.1 (by omega)
  refine ⟨opening, left, hopen, hleft.congr (fun e he => ?_)⟩
  have := hab e he
  simp only [List.mem_filter, he, true_and, Bool.and_eq_true, beq_iff_eq]
  unfold OpenAt StaysAt
  cases ring e <;> simp <;> omega

/-- The atoms from number `i` on, for a `Mol` without orientations whose bonds
are in order. With the table as it must be in front of atom `i`, a spelling
gives its tokens exactly when no more than 99 ring numbers are open behind any
of these atoms. -/
theorem tokensFrom_isOk (spelling : Spelling) {mol : Mol} (hl : mol.bonds.Pairwise Bond.before)
    (hab : ∀ e ∈ mol.bonds, e.a < e.b) (ho : mol.orientations = []) (marks : Marks)
    (parents : List (Option Nat)) :
    ∀ (atoms : List (Atom × Option Nat)) (i : Nat) {W : List (Nat × Bond)},
      Counted mol.bonds (OpenAt (ringBond parents) i) W →
      ((tokensFrom spelling mol marks parents i atoms W).isOk = true ↔
        ∀ j, j < atoms.length →
          (mol.bonds.filter fun e => decide (OpenAt (ringBond parents) (i + j + 1) e)).length ≤ 99)
  | [], i, W, _ => by simp [tokensFrom, Except.isOk, Except.toBool]
  | (atom, parent) :: rest, i, W, h => by
    obtain ⟨closing, afterClosing, hclose, hyes, hno⟩ :=
      rings_counted hl hab (ringBond parents) (markedSymbol marks (spelling.symbol mol)) i h
    by_cases hc : (mol.bonds.filter fun e =>
        decide (OpenAt (ringBond parents) (i + 1) e)).length ≤ 99
    · obtain ⟨opening, left, hopen, hleft⟩ := hyes hc
      have ih := tokensFrom_isOk spelling hl hab ho marks parents rest (i + 1) hleft
      have hstep : (tokensFrom spelling mol marks parents i ((atom, parent) :: rest) W).isOk
          = (tokensFrom spelling mol marks parents (i + 1) rest left).isOk := by
        rw [tokensFrom_cons ho, hclose]
        simp only [hopen]
        cases tokensFrom spelling mol marks parents (i + 1) rest left <;> rfl
      rw [hstep, ih]
      constructor
      · intro hall j hj
        cases j with
        | zero => exact hc
        | succ j =>
          have := hall j (by simpa using hj)
          have e : i + 1 + j + 1 = i + (j + 1) + 1 := by omega
          rw [e] at this
          exact this
      · intro hall j hj
        have := hall (j + 1) (by simpa using hj)
        have e : i + (j + 1) + 1 = i + 1 + j + 1 := by omega
        rw [e] at this
        exact this
    · have hnone := hno (by omega)
      have hfail : (tokensFrom spelling mol marks parents i ((atom, parent) :: rest) W).isOk
          = false := by
        rw [tokensFrom_cons ho, hclose]
        simp only [hnone]
        rfl
      rw [hfail]
      constructor
      · intro hs
        cases hs
      · intro hall
        exact absurd (hall 0 (by simp)) hc

/-- The ring numbers that are open behind atom `i`, as the statements count
them: one for every bond that begins at the atom or before it, ends behind
it, and is written with a ring number. -/
theorem openAt_count (l : List Bond) (ring : Bond → Bool) (i : Nat) :
    (l.filter fun e => decide (OpenAt ring (0 + i + 1) e))
      = l.filter fun bond => decide (bond.a ≤ i ∧ i < bond.b) && ring bond := by
  refine List.filter_congr (fun e _ => ?_)
  rw [Bool.eq_iff_iff]
  simp only [OpenAt, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, by omega, h3⟩

/-- The tokens of a spelling. For a well formed `Mol` without orientations the
writer gives them exactly when, behind every atom, no more than 99 ring
numbers are open: one for every bond that begins at the atom or before it,
ends behind it, and is written with a ring number. Which marks its bonds
carry plays no part. -/
theorem Spelling.tokens_isOk_iff (spelling : Spelling) (mol : Mol) (hw : mol.WellFormed)
    (ho : mol.orientations = []) (marks : Marks) :
    (∃ tokens, spelling.tokens mol marks = .ok tokens) ↔
      ∀ i, i < mol.atoms.length →
        (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b)
            && ringBond (spelling.parents mol) bond).length ≤ 99 := by
  have h0 : Counted mol.bonds (OpenAt (ringBond (spelling.parents mol)) 0) [] :=
    ⟨by simp, by simp, by simp, fun e => by simp [OpenAt]⟩
  have hsame := fun i => openAt_count mol.bonds (ringBond (spelling.parents mol)) i
  have hlen : (mol.atoms.zip (spelling.parents mol)).length = mol.atoms.length := by
    simp [List.length_zip, Spelling.parents, parentsFrom_length]
  have hok : (∃ tokens, spelling.tokens mol marks = .ok tokens)
      ↔ (tokensFrom spelling mol marks (spelling.parents mol) 0
          (mol.atoms.zip (spelling.parents mol)) []).isOk = true := by
    unfold Spelling.tokens
    cases tokensFrom spelling mol marks (spelling.parents mol) 0
      (mol.atoms.zip (spelling.parents mol)) [] <;> simp [Except.isOk, Except.toBool]
  rw [hok, tokensFrom_isOk spelling hw.2.1 (fun e he => (hw.1 e he).1) ho marks _ _ 0 h0, hlen]
  constructor <;> intro h i hi <;> have := h i hi
  · rwa [hsame i] at this
  · rwa [hsame i]

/-! ## Theorem 19, for both spellings -/

/-- Theorem 19 of CLAIMS.md, for both spellings. For a `Mol` without stereo
facts a spelling gives a text exactly when the `Mol` is well formed, each of
its atoms can be written (SPEC.md, section 9.4), and behind no atom more than
99 ring numbers are open.

The count stands in the statement itself: for atom `i`, the bonds of the `Mol`
with `a ≤ i` and `i < b` that are written with a ring number, which are those
whose later atom is not written next to its earlier atom (`ringBond`). -/
theorem Spelling.write_isOk_iff_ringNumbers (spelling : Spelling) (mol : Mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ text, spelling.write mol = .ok text) ↔
      mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
      ∀ i, i < mol.atoms.length →
        (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b)
            && ringBond (spelling.parents mol) bond).length ≤ 99 := by
  rw [spelling.write_isOk_iff]
  constructor
  · rintro ⟨hw, hr, marks, tokens, _, htokens⟩
    exact ⟨hw, hr, (spelling.tokens_isOk_iff mol hw horientations marks).1 ⟨tokens, htokens⟩⟩
  · rintro ⟨hw, hr, hc⟩
    obtain ⟨tokens, htokens⟩ := (spelling.tokens_isOk_iff mol hw horientations []).2 hc
    exact ⟨hw, hr, [], tokens, chooseMarks_of_no_geometries hgeometries, htokens⟩

/-- For a well formed `Mol` without stereo facts whose atoms can all be
written, a spelling answers with the message about ring numbers exactly when,
behind some atom, more than 99 ring numbers are open. -/
theorem Spelling.tooManyRingNumbers_iff_of_fine (spelling : Spelling) (mol : Mol)
    (hw : mol.WellFormed) (hr : ∀ a ∈ mol.atoms, a.refusal = none)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    spelling.write mol = .error Message.tooManyRingNumbers ↔
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b) && ringBond (spelling.parents mol) bond).length := by
  have hiff := spelling.write_isOk_iff_ringNumbers mol horientations hgeometries
  have hrest : spelling.write mol = .error Message.tooManyRingNumbers ∨
      ∃ text, spelling.write mol = .ok text :=
    (spelling.write_of_fine hw hr horientations hgeometries).symm
  constructor
  · intro herr
    apply Classical.byContradiction
    intro hnot
    have hall : ∀ i, i < mol.atoms.length →
        (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b) && ringBond (spelling.parents mol) bond).length
            ≤ 99 := by
      intro i hi
      apply Classical.byContradiction
      intro hgt
      exact hnot ⟨i, hi, by omega⟩
    obtain ⟨text, htext⟩ := hiff.2 ⟨hw, hr, hall⟩
    rw [htext] at herr
    cases herr
  · rintro ⟨i, hi, hgt⟩
    rcases hrest with herr | hok
    · exact herr
    · have := (hiff.1 hok).2.2 i hi
      omega

/-- Theorem 19 of CLAIMS.md, for both spellings. For a `Mol` without stereo
facts a spelling answers with the message about ring numbers exactly when the
`Mol` is well formed, each of its atoms can be written, and behind some atom
more than 99 ring numbers are open. So that message is true whenever a
spelling gives it for such a `Mol`. -/
theorem Spelling.write_tooManyRingNumbers_iff (spelling : Spelling) (mol : Mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    spelling.write mol = .error Message.tooManyRingNumbers ↔
      mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b) && ringBond (spelling.parents mol) bond).length := by
  by_cases hw : mol.WellFormed
  · by_cases hr : ∀ a ∈ mol.atoms, a.refusal = none
    · rw [spelling.tooManyRingNumbers_iff_of_fine mol hw hr horientations hgeometries]
      exact ⟨fun h => ⟨hw, hr, h⟩, fun h => h.2.2⟩
    · constructor
      · intro h
        exfalso
        cases hf : mol.atoms.findSome? Atom.refusal with
        | none => exact hr (List.findSome?_eq_none_iff.1 hf)
        | some m =>
          unfold Spelling.write at h
          simp only [hw, not_true_eq_false, ↓reduceIte, hf, Except.error.injEq] at h
          obtain ⟨a, _, ha⟩ := List.exists_of_findSome?_eq_some hf
          unfold Atom.refusal at ha
          split at ha
          · cases ha; exact absurd h (by decide)
          · split at ha
            · cases ha; exact absurd h (by decide)
            · cases ha
      · rintro ⟨_, hr', _⟩
        exact absurd hr' hr
  · constructor
    · intro h
      unfold Spelling.write at h
      simp only [hw, not_false_eq_true, ↓reduceIte, Except.error.injEq] at h
      exact absurd h (by decide)
    · rintro ⟨hw', _⟩
      exact absurd hw' hw

/-- The same for a command. For a text that is read as a `Mol` without stereo
facts, a command that writes the `Mol` in a spelling answers with the error
about ring numbers exactly when, behind some atom of the `Mol`, more than 99
ring numbers are open. -/
theorem rewritten_tooManyRingNumbers_iff (spelling : Spelling) (text : List Char) (mol : Mol)
    (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    rewritten spelling.write text = Output.error Message.tooManyRingNumbers ↔
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b) && ringBond (spelling.parents mol) bond).length := by
  rw [← spelling.tooManyRingNumbers_iff_of_fine mol (read_wellFormed text mol h)
    (read_no_refusal text mol h) horientations hgeometries]
  unfold rewritten
  rw [h]
  simp only
  cases hp : spelling.write mol with
  | ok w =>
    simp only [reduceCtorEq, iff_false]
    intro heq
    have := congrArg Output.exitCode heq
    simp [Output.ok, Output.error] at this
  | error m =>
    simp only [Except.error.injEq]
    constructor
    · intro heq
      have := congrArg Output.stderr heq
      simpa [Output.error] using this
    · intro hm; subst hm; rfl

/-- Theorem 19 of CLAIMS.md, for the command `rewrite`. For a text that is
read as a `Mol` without stereo facts, `rewrite` answers with the error about
ring numbers exactly when, behind some atom of the `Mol`, more than 99 ring
numbers are open in the spelling with round brackets. So that error is true
whenever `rewrite` prints it for such a text. (For every other such text it
prints the spelling: theorems 5 and 18.) -/
theorem run_rewrite_tooManyRingNumbers_iff (text : List Char) (mol : Mol)
    (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    run ["rewrite".toList, text] = Output.error Message.tooManyRingNumbers ↔
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b)
            && ringBond (Spelling.brackets.parents mol) bond).length := by
  have hrun : run ["rewrite".toList, text] = rewritten Spelling.brackets.write text := by
    simp [run]
    rfl
  rw [hrun]
  exact rewritten_tooManyRingNumbers_iff .brackets text mol h horientations hgeometries

/-! ## Theorem 19, for every `Mol`: the message about ring numbers is true -/

/-- The reasons for which an atom with an orientation cannot be written where
it stands are other messages than the one about ring numbers. -/
theorem centreRefusal_ne (mol : Mol) (atom : Nat) (atomBefore : Bool) (numbers : Nat) :
    centreRefusal mol atom atomBefore numbers ≠ some Message.tooManyRingNumbers := by
  unfold centreRefusal
  split
  · decide
  · split
    · decide
    · simp

/-- The reasons for which no marks are chosen are other messages than the one
about ring numbers. -/
theorem chooseMarks_ne (mol : Mol) : chooseMarks mol ≠ .error Message.tooManyRingNumbers := by
  unfold chooseMarks
  simp only
  split
  · intro h
    injection h with h
    exact absurd h (by decide)
  · split
    · intro h
      injection h with h
      exact absurd h (by decide)
    · split
      · simp
      · intro h
        injection h with h
        exact absurd h (by decide)

/-- The atoms from number `i` on, for a `Mol` whose bonds are in order, with
or without orientations. With the table as it must be in front of atom `i`, a
spelling answers with the message about ring numbers only if more than 99 ring
numbers are open behind one of these atoms: the writer finds the number of
every ring bond that it closes, so the message can only come from a bond that
is to open. -/
theorem tokensFrom_tooManyRingNumbers (spelling : Spelling) {mol : Mol}
    (hl : mol.bonds.Pairwise Bond.before) (hab : ∀ e ∈ mol.bonds, e.a < e.b) (marks : Marks)
    (parents : List (Option Nat)) :
    ∀ (atoms : List (Atom × Option Nat)) (i : Nat) {W : List (Nat × Bond)},
      Counted mol.bonds (OpenAt (ringBond parents) i) W →
      tokensFrom spelling mol marks parents i atoms W = .error Message.tooManyRingNumbers →
      ∃ j, j < atoms.length ∧
        99 < (mol.bonds.filter fun e => decide (OpenAt (ringBond parents) (i + j + 1) e)).length
  | [], i, W, _, h => by simp [tokensFrom] at h
  | (atom, parent) :: rest, i, W, hW, h => by
    obtain ⟨closing, afterClosing, hclose, hyes, hno⟩ :=
      rings_counted hl hab (ringBond parents) (markedSymbol marks (spelling.symbol mol)) i hW
    simp only [tokensFrom] at h
    split at h
    · -- the atom cannot be written where it stands: that is another message
      rename_i message htoken
      exfalso
      split at htoken
      · cases htoken
      · split at htoken
        · rename_i refusal hrefusal
          cases htoken
          injection h with hm
          exact centreRefusal_ne _ _ _ _ (hm ▸ hrefusal)
        · cases htoken
    · rename_i token htoken
      split at h
      · -- the writer finds the number of every bond that closes
        rename_i hnone
        rw [hclose] at hnone
        cases hnone
      · rename_i closing' afterClosing' hsome
        rw [hclose] at hsome
        cases hsome
        split at h
        · -- no free number: more than 99 ring numbers are open behind this atom
          rename_i hnoneOpen
          refine ⟨0, by simp, ?_⟩
          show 99 < (mol.bonds.filter fun e => decide (OpenAt (ringBond parents) (i + 1) e)).length
          apply Classical.byContradiction
          intro hle
          obtain ⟨opening, left, hopen, _⟩ := hyes (by omega)
          rw [hopen] at hnoneOpen
          cases hnoneOpen
        · rename_i opening left hopen
          split at h
          · rename_i message hrest
            injection h with hm
            subst hm
            have hc : (mol.bonds.filter fun e =>
                decide (OpenAt (ringBond parents) (i + 1) e)).length ≤ 99 := by
              apply Classical.byContradiction
              intro hgt
              rw [hno (by omega)] at hopen
              cases hopen
            obtain ⟨opening', left', hopen', hleft⟩ := hyes hc
            rw [hopen] at hopen'
            cases hopen'
            obtain ⟨j, hj, hgt⟩ :=
              tokensFrom_tooManyRingNumbers spelling hl hab marks parents rest (i + 1) hleft hrest
            refine ⟨j + 1, by simpa using hj, ?_⟩
            have e : i + (j + 1) + 1 = i + 1 + j + 1 := by omega
            rw [e]
            exact hgt
          · cases h

/-- Theorem 19 of CLAIMS.md, for every `Mol`, with or without stereo facts.
The message about ring numbers is true whenever a spelling gives it: the
`Mol` is then well formed, each of its atoms can be written, and behind some
atom more than 99 ring numbers are open. (For a `Mol` without stereo facts
the converse holds as well: `Spelling.write_tooManyRingNumbers_iff`.) -/
theorem Spelling.write_tooManyRingNumbers_sound (spelling : Spelling) (mol : Mol)
    (h : spelling.write mol = .error Message.tooManyRingNumbers) :
    mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b) && ringBond (spelling.parents mol) bond).length := by
  unfold Spelling.write at h
  by_cases hw : mol.WellFormed
  · simp only [hw, not_true_eq_false, ↓reduceIte] at h
    cases hf : mol.atoms.findSome? Atom.refusal with
    | some m =>
      exfalso
      simp only [hf, Except.error.injEq] at h
      obtain ⟨a, _, ha⟩ := List.exists_of_findSome?_eq_some hf
      unfold Atom.refusal at ha
      split at ha
      · cases ha; exact absurd h (by decide)
      · split at ha
        · cases ha; exact absurd h (by decide)
        · cases ha
    | none =>
      have hr := List.findSome?_eq_none_iff.1 hf
      simp only [hf] at h
      cases hm : chooseMarks mol with
      | error message =>
        exfalso
        simp only [hm, Except.error.injEq] at h
        exact chooseMarks_ne mol (by rw [hm, h])
      | ok marks =>
        simp only [hm] at h
        cases ht : spelling.tokens mol marks with
        | ok ts =>
          exfalso
          obtain ⟨text, htext⟩ :=
            Option.isSome_iff_exists.1 (spell_isSome (spelling.tokens_spelled mol hr marks ts ht))
          simp [ht, htext] at h
        | error message =>
          simp only [ht, Except.error.injEq] at h
          subst h
          have h0 : Counted mol.bonds (OpenAt (ringBond (spelling.parents mol)) 0) [] :=
            ⟨by simp, by simp, by simp, fun e => by simp [OpenAt]⟩
          obtain ⟨j, hj, hgt⟩ := tokensFrom_tooManyRingNumbers spelling hw.2.1
            (fun e he => (hw.1 e he).1) marks (spelling.parents mol) _ 0 h0 ht
          have hlen : (mol.atoms.zip (spelling.parents mol)).length = mol.atoms.length := by
            simp [List.length_zip, Spelling.parents, parentsFrom_length]
          refine ⟨hw, hr, j, hlen ▸ hj, ?_⟩
          rw [← openAt_count]
          exact hgt
  · simp only [hw, not_false_eq_true, ↓reduceIte, Except.error.injEq] at h
    exact absurd h (by decide)

/-! ## Theorem 19, for the plain spelling: the count without the parents -/

/-- In the plain spelling the parent of an atom is the atom just before it, if
the two are bonded. So a bond of a well formed `Mol` is written with a ring
number exactly when it does not join two atoms that follow each other. -/
theorem plain_ringBond_iff {mol : Mol} (hw : mol.WellFormed) {e : Bond} (he : e ∈ mol.bonds) :
    ringBond (Spelling.plain.parents mol) e = true ↔ e.b ≠ e.a + 1 := by
  have hrange := hw.1 e he
  unfold ringBond
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne hb
    apply hne
    have hbonded : bonded (mol.bonds.filter Spelling.plain.runsAlong) e.a (e.a + 1) = true := by
      unfold bonded
      exact List.any_eq_true.2 ⟨e, List.mem_filter.2 ⟨he, by simp [Spelling.runsAlong, hb]⟩,
        by simp [hb]⟩
    have hparent := parentsFrom_previous (mol.bonds.filter Spelling.plain.runsAlong) mol.atoms 0 []
      (by intro k hk; omega) e.b e.a (by omega) hrange.2 hbonded
    unfold parentOf Spelling.parents
    rw [hparent]
    rfl
  · intro hne hp
    apply hne
    unfold parentOf at hp
    cases hx : (Spelling.plain.parents mol)[e.b]? with
    | none =>
      rw [hx] at hp
      cases hp
    | some v =>
      rw [hx] at hp
      simp only [Option.getD_some] at hp
      subst hp
      have hbonded := (parentsFrom_parent (mol.bonds.filter Spelling.plain.runsAlong) mol.atoms 0 []
        (by simp) e.b e.a hx).2
      unfold bonded at hbonded
      obtain ⟨x, hx', hpx⟩ := List.any_eq_true.1 hbonded
      have halong := (List.mem_filter.1 hx').2
      simp only [Spelling.runsAlong, beq_iff_eq] at halong
      simp only [Nat.zero_add, Bool.and_eq_true, beq_iff_eq] at hpx
      omega

/-- The bonds that the count of the plain spelling looks at, said without the
parents. -/
theorem plain_count {mol : Mol} (hw : mol.WellFormed) (i : Nat) :
    (mol.bonds.filter fun bond =>
        decide (bond.a ≤ i ∧ i < bond.b) && ringBond (Spelling.plain.parents mol) bond)
      = mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b ∧ bond.b ≠ bond.a + 1) := by
  apply List.filter_congr
  intro e he
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, plain_ringBond_iff hw he]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- Theorem 19 of CLAIMS.md, for the plain spelling. For a `Mol` without
stereo facts the plain spelling gives a text exactly when the `Mol` is well
formed, each of its atoms can be written (SPEC.md, section 9.4), and behind
no atom more than 99 ring numbers are open.

The count stands in the statement itself, and it names no function of the
writer: for atom `i`, the bonds of the `Mol` with `a ≤ i`, `i < b` and
`b ≠ a + 1`. -/
theorem writePlain_isOk_iff_ringNumbers (mol : Mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ text, writePlain mol = .ok text) ↔
      mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
      ∀ i, i < mol.atoms.length →
        (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b ∧ bond.b ≠ bond.a + 1)).length ≤ 99 := by
  have h := Spelling.plain.write_isOk_iff_ringNumbers mol horientations hgeometries
  constructor
  · intro ht
    obtain ⟨hw, hr, hc⟩ := h.1 ht
    exact ⟨hw, hr, fun i hi => by rw [← plain_count hw i]; exact hc i hi⟩
  · rintro ⟨hw, hr, hc⟩
    exact h.2 ⟨hw, hr, fun i hi => by rw [plain_count hw i]; exact hc i hi⟩

/-- Theorem 19 of CLAIMS.md, for the plain spelling. For a `Mol` without
stereo facts the plain spelling answers with the message about ring numbers
exactly when the `Mol` is well formed, each of its atoms can be written, and
behind some atom more than 99 ring numbers are open. So that message is true
whenever the plain spelling gives it for such a `Mol`. -/
theorem writePlain_tooManyRingNumbers_iff (mol : Mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    writePlain mol = .error Message.tooManyRingNumbers ↔
      mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b ∧ bond.b ≠ bond.a + 1)).length := by
  have h := Spelling.plain.write_tooManyRingNumbers_iff mol horientations hgeometries
  constructor
  · intro ht
    obtain ⟨hw, hr, i, hi, hc⟩ := h.1 ht
    exact ⟨hw, hr, i, hi, by rw [← plain_count hw i]; exact hc⟩
  · rintro ⟨hw, hr, i, hi, hc⟩
    exact h.2 ⟨hw, hr, i, hi, by rw [plain_count hw i]; exact hc⟩

/-- Theorem 19 of CLAIMS.md, for the command `plain`. For a text that is read
as a `Mol` without stereo facts, `plain` answers with the error about ring
numbers exactly when, behind some atom of the `Mol`, more than 99 ring
numbers are open. (For every other such text it prints the plain spelling:
theorems 5 and 18.) -/
theorem run_plain_tooManyRingNumbers_iff (text : List Char) (mol : Mol) (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    run ["plain".toList, text] = Output.error Message.tooManyRingNumbers ↔
      ∃ i, i < mol.atoms.length ∧
        99 < (mol.bonds.filter fun bond =>
          decide (bond.a ≤ i ∧ i < bond.b ∧ bond.b ≠ bond.a + 1)).length := by
  have hrun : run ["plain".toList, text] = rewritten Spelling.plain.write text := by
    simp [run]
    rfl
  have hw := read_wellFormed text mol h
  rw [hrun, rewritten_tooManyRingNumbers_iff .plain text mol h horientations hgeometries]
  constructor
  · rintro ⟨i, hi, hc⟩
    exact ⟨i, hi, by rw [← plain_count hw i]; exact hc⟩
  · rintro ⟨i, hi, hc⟩
    exact ⟨i, hi, by rw [plain_count hw i]; exact hc⟩

end VeriMol
