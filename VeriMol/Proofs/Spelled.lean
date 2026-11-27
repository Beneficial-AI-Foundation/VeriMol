import VeriMol.Core.Write

/-!
# The tokens that a spelling makes can be spelled

This file proves theorem 17 of CLAIMS.md: which `Mol`s get a text from a
spelling, in the words of the writer's own functions for the marks and for
the tokens.

A spelling makes tokens, and `spell` turns the tokens into text
(`Spelling.write` in `VeriMol/Core/Write.lean`). `spell` can refuse a token:
an atom with more than 9 hydrogens of its own, for example, or a ring
number above 99. `Spelling.write` has a branch for that case, and its comment
says "cannot happen". Here that is proven: every token that a spelling makes
for a `Mol` whose atoms can all be written is a token that `spell` spells
(`Spelling.tokens_spelled`).

So a spelling gives a text exactly when the `Mol` is well formed, each of its
atoms can be written, the marks for its double bonds are chosen, and the
spelling makes its tokens (`Spelling.write_isOk_iff`). What the theorem adds
to the definition of `Spelling.write` is its last branch: it is never taken.

Not proven here: when the marks are chosen and when a spelling makes its
tokens, said without the writer's own functions. For a `Mol` without stereo
facts `VeriMol/Proofs/RingNumbers.lean` says when the tokens are made by
counting bonds (theorem 19); for the spelling with round brackets that count
still names the writer's function for the parents.
-/

namespace VeriMol

/-- Every token of the list can be spelled. -/
def AllSpelled (tokens : List Token) : Prop := ∀ t ∈ tokens, t.spell.isSome = true

theorem AllSpelled.nil : AllSpelled [] := by
  intro t ht; simp at ht

theorem AllSpelled.cons {t : Token} {rest : List Token} (ht : t.spell.isSome = true)
    (hrest : AllSpelled rest) : AllSpelled (t :: rest) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ht
  · exact hrest x hx

theorem AllSpelled.append {xs ys : List Token} (hx : AllSpelled xs) (hy : AllSpelled ys) :
    AllSpelled (xs ++ ys) := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact hx t h
  · exact hy t h

theorem allSpelled_append_iff {xs ys : List Token} :
    AllSpelled (xs ++ ys) ↔ AllSpelled xs ∧ AllSpelled ys := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (List.mem_append_left _ ht),
      fun t ht => h t (List.mem_append_right _ ht)⟩
  · intro h
    exact AllSpelled.append h.1 h.2

theorem allSpelled_cons_iff {t : Token} {rest : List Token} :
    AllSpelled (t :: rest) ↔ t.spell.isSome = true ∧ AllSpelled rest := by
  constructor
  · intro h
    exact ⟨h t (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
  · intro h
    exact AllSpelled.cons h.1 h.2

theorem spell_isSome {tokens : List Token} (h : AllSpelled tokens) :
    (spell tokens).isSome = true := by
  induction tokens with
  | nil => rfl
  | cons t rest ih =>
    have ht := h t (List.mem_cons_self ..)
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hts : t.spell with
    | none => simp [hts] at ht
    | some first =>
      cases hrs : spell rest with
      | none => simp [hrs] at hr
      | some behind => simp [spell, hts, hrs]

theorem ringNumbers_lt {k : Nat} (h : k ∈ ringNumbers) : k < 100 := by
  simp [ringNumbers, List.mem_range'_1] at h
  omega

theorem ring_spelled {k : Nat} (h : k ∈ ringNumbers) : (Token.ring k).spell.isSome = true := by
  have hk := ringNumbers_lt h
  simp only [Token.spell]
  split
  · rfl
  · rfl

theorem closeRings_spelled : ∀ (bonds : List Bond) (rings : List (Nat × Bond)) (tokens : List Token)
    (left : List (Nat × Bond)),
    closeRings rings bonds = some (tokens, left) → AllSpelled tokens := by
  intro bonds
  induction bonds with
  | nil =>
    intro rings tokens left h
    simp [closeRings] at h
    rw [h.1]
    exact AllSpelled.nil
  | cons bond rest ih =>
    intro rings tokens left h
    simp only [closeRings] at h
    cases hn : numberOf rings bond with
    | none => simp [hn] at h
    | some number =>
      simp only [hn] at h
      cases hc : closeRings (withoutRing number rings) rest with
      | none => simp [hc] at h
      | some pair =>
        obtain ⟨tokens', left'⟩ := pair
        simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact AllSpelled.cons (ring_spelled (List.mem_of_find?_eq_some hn)) (ih _ _ _ hc)

theorem openRings_spelled (symbol : Bond → List Token) (hsym : ∀ bond, AllSpelled (symbol bond)) :
    ∀ (bonds : List Bond) (rings : List (Nat × Bond)) (tokens : List Token)
    (left : List (Nat × Bond)),
    openRings symbol rings bonds = some (tokens, left) → AllSpelled tokens := by
  intro bonds
  induction bonds with
  | nil =>
    intro rings tokens left h
    simp [openRings] at h
    rw [h.1]
    exact AllSpelled.nil
  | cons bond rest ih =>
    intro rings tokens left h
    simp only [openRings] at h
    cases hn : freeNumber rings with
    | none => simp [hn] at h
    | some number =>
      simp only [hn] at h
      cases hc : openRings symbol ((number, bond) :: rings) rest with
      | none => simp [hc] at h
      | some pair =>
        obtain ⟨tokens', left'⟩ := pair
        simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact AllSpelled.append (hsym bond)
          (AllSpelled.cons (ring_spelled (List.mem_of_find?_eq_some hn)) (ih _ _ _ hc))

theorem plainSymbol_spelled (bond : Bond) : AllSpelled (plainSymbol bond) := by
  intro t ht
  simp [plainSymbol] at ht
  subst ht
  rfl

theorem markedSymbol_spelled (marks : Marks) {symbol : Bond → List Token}
    (hsym : ∀ bond, AllSpelled (symbol bond)) (bond : Bond) :
    AllSpelled (markedSymbol marks symbol bond) := by
  unfold markedSymbol
  split
  · rename_i up _
    cases up <;> exact AllSpelled.cons rfl AllSpelled.nil
  · exact hsym bond

/-! ## The atoms -/

theorem inBrackets_spelled (bonds : List Bond) (number : Nat) (atom : Atom)
    (hr : atom.refusal = none) :
    (Token.atom (atom.inBrackets (writtenLowercase bonds number atom))).spell.isSome = true := by
  have h1 : ¬ (9 < atom.hydrogens ∨ 99 < atom.charge.natAbs) := by
    intro hc
    simp [Atom.refusal, hc] at hr
  have h2 : ¬ (atom.element = .H ∧ 0 < atom.hydrogens) := by
    intro hc
    simp [Atom.refusal, h1, hc] at hr
  have h3 : ¬ (9 < atom.hydrogens ∨ 99 < atom.charge.natAbs ∨
      (atom.element = .H ∧ 0 < atom.hydrogens)) := by
    intro hc
    rcases hc with hc | hc | hc
    · exact h1 (Or.inl hc)
    · exact h1 (Or.inr hc)
    · exact h2 hc
  simp only [Token.spell, WrittenAtom.spell, Atom.inBrackets, h3, ↓reduceIte]
  cases hl : writtenLowercase bonds number atom with
  | false => simp
  | true =>
    simp only [writtenLowercase, Bool.and_eq_true] at hl
    simp [hl.2]

theorem shortAtom_spelled (bonds : List Bond) (number : Nat) (atom : Atom)
    (hr : atom.refusal = none) : (shortAtom bonds number atom).spell.isSome = true := by
  simp only [shortAtom]
  cases hb : writtenBare bonds number atom with
  | false => simpa using inBrackets_spelled bonds number atom hr
  | true =>
    have h1 : (bareSymbol? atom.element (writtenLowercase bonds number atom)).isSome = true := by
      simp only [writtenBare, Bool.and_eq_true] at hb
      exact hb.1.1.1.1.1
    simp [Token.spell, WrittenAtom.spell, WrittenAtom.bare, h1]

/-- An atom with an orientation is written in square brackets, and its mark
does not stand in the way of spelling it. -/
theorem orientedAtom_spelled (mol : Mol) (number : Nat) (atom : Atom) (stored : Orientation)
    (key : Place → Nat × Nat) (hr : atom.refusal = none) :
    (orientedAtom mol number atom stored key).spell.isSome = true := by
  have h := inBrackets_spelled mol.bonds number atom hr
  simp only [Token.spell, WrittenAtom.spell, Atom.inBrackets] at h
  simp only [orientedAtom, Token.spell, WrittenAtom.spell, Atom.inBrackets]
  split
  · rename_i hrefused
    simp [hrefused] at h
  · rename_i hfine
    simp only [hfine, ↓reduceIte, Option.isSome_map] at h ⊢
    exact h

/-! ## The two spellings -/

theorem shortSymbol_spelled (mol : Mol) (bond : Bond) : AllSpelled (shortSymbol mol bond) := by
  simp only [shortSymbol]
  split
  · exact AllSpelled.nil
  · exact plainSymbol_spelled bond

theorem Spelling.symbol_spelled (spelling : Spelling) (mol : Mol) (bond : Bond) :
    AllSpelled (spelling.symbol mol bond) := by
  cases spelling
  · exact plainSymbol_spelled bond
  · exact shortSymbol_spelled mol bond

theorem Spelling.atom_spelled (spelling : Spelling) (bonds : List Bond) (number : Nat)
    (atom : Atom) (hr : atom.refusal = none) :
    (spelling.atom bonds number atom).spell.isSome = true := by
  cases spelling
  · exact inBrackets_spelled bonds number atom hr
  · exact shortAtom_spelled bonds number atom hr

theorem beforeAtom_spelled (spelling : Spelling) (mol : Mol) (marks : Marks) (number : Nat)
    (parent : Option Nat) (later : List (Option Nat)) :
    AllSpelled (beforeAtom spelling mol marks number parent later) := by
  cases parent with
  | none =>
    simp only [beforeAtom]
    split
    · exact AllSpelled.nil
    · exact AllSpelled.cons rfl AllSpelled.nil
  | some parent =>
    simp only [beforeAtom]
    refine AllSpelled.append (AllSpelled.append ?_ ?_) ?_
    · split
      · exact AllSpelled.nil
      · exact AllSpelled.cons rfl AllSpelled.nil
    · split
      · exact AllSpelled.cons rfl AllSpelled.nil
      · exact AllSpelled.nil
    · split
      · exact markedSymbol_spelled marks (spelling.symbol_spelled mol) _
      · exact AllSpelled.nil

theorem tokensFrom_spelled (spelling : Spelling) (mol : Mol) (marks : Marks)
    (parents : List (Option Nat)) :
    ∀ (atoms : List (Atom × Option Nat)) (number : Nat) (rings : List (Nat × Bond))
      (tokens : List Token), (∀ pair ∈ atoms, pair.1.refusal = none) →
      tokensFrom spelling mol marks parents number atoms rings = .ok tokens →
      AllSpelled tokens := by
  intro atoms
  induction atoms with
  | nil =>
    intro number rings tokens _ h
    simp only [tokensFrom, Except.ok.injEq] at h
    subst h
    exact AllSpelled.nil
  | cons pair rest ih =>
    obtain ⟨atom, parent⟩ := pair
    intro number rings tokens hr h
    have hatom := hr (atom, parent) List.mem_cons_self
    simp only [tokensFrom] at h
    split at h
    · cases h
    · rename_i token htoken
      split at h
      · cases h
      · rename_i closing afterClosing hc
        split at h
        · cases h
        · rename_i opening afterOpening ho
          split at h
          · cases h
          · rename_i behind hb
            cases h
            have htok : token.spell.isSome = true := by
              split at htoken
              · cases htoken
                exact spelling.atom_spelled mol.bonds number atom hatom
              · split at htoken
                · cases htoken
                · cases htoken
                  exact orientedAtom_spelled mol number atom _ _ hatom
            simp only [allSpelled_append_iff, allSpelled_cons_iff]
            exact ⟨⟨⟨beforeAtom_spelled spelling mol marks number parent _, htok,
              closeRings_spelled _ _ _ _ hc⟩,
              openRings_spelled _ (markedSymbol_spelled marks (spelling.symbol_spelled mol))
                _ _ _ _ ho⟩,
              ih _ _ _ (fun pair hp => hr pair (List.mem_cons_of_mem _ hp)) hb⟩

/-- For a `Mol` whose atoms can all be written, the tokens of a spelling can
always be spelled. -/
theorem Spelling.tokens_spelled (spelling : Spelling) (mol : Mol)
    (hr : ∀ a ∈ mol.atoms, a.refusal = none) (marks : Marks) (tokens : List Token)
    (h : spelling.tokens mol marks = .ok tokens) : AllSpelled tokens :=
  tokensFrom_spelled spelling mol marks (spelling.parents mol)
    (mol.atoms.zip (spelling.parents mol)) 0 [] tokens
    (fun pair hp => hr pair.1 (List.of_mem_zip (a := pair.1) (b := pair.2) hp).1) h

/-! ## What follows for `Spelling.write` -/

/-- Theorem 17 of CLAIMS.md. Each of the two spellings gives a text exactly
when the `Mol` is well formed, each of its atoms can be written, the marks for
its double bonds are chosen, and the spelling makes its tokens. The last
branch of `Spelling.write`, for tokens that cannot be spelled, plays no part.
When the marks are chosen and the tokens are made, the theorem says in the
words of `chooseMarks` and `Spelling.tokens` only (see the head of this
file). -/
theorem Spelling.write_isOk_iff (spelling : Spelling) (mol : Mol) :
    (∃ text, spelling.write mol = .ok text) ↔
      mol.WellFormed ∧ (∀ a ∈ mol.atoms, a.refusal = none) ∧
        ∃ marks tokens, chooseMarks mol = .ok marks ∧ spelling.tokens mol marks = .ok tokens := by
  unfold Spelling.write
  by_cases hw : mol.WellFormed
  · simp only [hw, not_true_eq_false, ↓reduceIte, true_and]
    cases hf : mol.atoms.findSome? Atom.refusal with
    | some message =>
      have hnot : ¬ ∀ a ∈ mol.atoms, a.refusal = none := by
        intro hall
        rw [List.findSome?_eq_none_iff.2 hall] at hf
        cases hf
      simp [hnot]
    | none =>
      have hall := List.findSome?_eq_none_iff.1 hf
      cases hm : chooseMarks mol with
      | error message => simp
      | ok marks =>
        cases ht : spelling.tokens mol marks with
        | error message => simp [ht]
        | ok ts =>
          obtain ⟨text, htext⟩ :=
            Option.isSome_iff_exists.1 (spell_isSome (spelling.tokens_spelled mol hall marks ts ht))
          simp [ht, htext]
          exact hall
  · simp [hw]

end VeriMol
