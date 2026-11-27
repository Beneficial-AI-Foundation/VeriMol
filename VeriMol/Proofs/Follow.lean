import VeriMol.Proofs.Read
import VeriMol.Proofs.Rings

/-!
# The reader follows the writer: the groundwork

Theorems 11 and 12 of CLAIMS.md say that a spelling is read back as the same
`Mol`. One proof gives both (`VeriMol/Proofs/RoundTrip.lean`): it lets the
reader follow the writer, atom by atom. This file holds the parts of it that
are about the atoms, the bonds and the ring numbers alone; other proofs use
some of them as well. `VeriMol/Proofs/Notes.lean` says what the reader does
with each kind of token, with what it notes about stereo marks.

1. **Bonds in order.** Putting a bond of the `Mol` at its place among the
   bonds read so far gives the bonds read so far with that bond added
   (`insertBond_filter`). This is why the reader keeps its bonds in order.
2. **Reading tokens, wherever they stand.** The writer makes tokens. The reader
   gets each token with its position in the text, and the position only
   matters for error messages. `Reads` says that reading some tokens succeeds
   at whatever positions they stand.
3. **Where the reader stands.** Behind an atom (`AtAtom`); and in front of
   one, the atom just before it and what the reader has read last (`prevOf`,
   `lastOf`).
4. **The two tables.** The reader and the writer each keep a table of the
   open ring numbers. The reader's table mirrors the writer's (`Mirrors`), and
   every entry of the writer's table is a bond of the `Mol`, with no bond
   under two numbers (`TableHolds`).
-/

namespace VeriMol

/-! ## Bonds in order -/

/-- No bond stands before itself. -/
theorem Bond.not_before_self (x : Bond) : ¬ x.before x := by
  unfold Bond.before; omega

/-- In a list that is in order, no two bonds join the same two atoms. -/
theorem key_unique {l : List Bond} (hl : l.Pairwise Bond.before) {x y : Bond}
    (hx : x ∈ l) (hy : y ∈ l) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨hz, hzs⟩ := hl
    simp only [List.mem_cons] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]
    · have := hz y hy; subst hx; unfold Bond.before at this; omega
    · have := hz x hx; subst hy; unfold Bond.before at this; omega
    · exact ih hzs hx hy

/-- So no bond stands in such a list twice. -/
theorem nodup_of_ordered {l : List Bond} (hl : l.Pairwise Bond.before) : l.Nodup := by
  refine List.Pairwise.imp ?_ hl
  intro a b h heq
  subst heq
  exact Bond.not_before_self a h

/-- A bond that stands before the first bond of a list is put in front. -/
theorem insertBond_before_head (x y : Bond) (ys : List Bond) (h : x.before y) :
    insertBond x (y :: ys) = x :: y :: ys := by
  simp [insertBond, h]

/-- Putting a bond of the list at its place among those already chosen gives
the choice with that bond added. -/
theorem insertBond_filter {l : List Bond} (hl : l.Pairwise Bond.before)
    (p : Bond → Bool) {c : Bond} (hc : c ∈ l) (hp : p c = false) :
    insertBond c (l.filter p) = l.filter (fun e => p e || e == c) := by
  induction l with
  | nil => simp at hc
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨hy, hys⟩ := hl
    by_cases hyc : y = c
    · subst hyc
      have hne : ∀ e ∈ ys, (e == y) = false := by
        intro e he
        have hb := hy e he
        have : e ≠ y := fun h => Bond.not_before_self y (h ▸ hb)
        simpa using this
      have h1 : (y :: ys).filter p = ys.filter p := by simp [hp]
      have h2 : (y :: ys).filter (fun e => p e || e == y) = y :: ys.filter p := by
        rw [List.filter_cons]
        simp only [beq_self_eq_true, Bool.or_true, ite_true]
        congr 1
        apply List.filter_congr
        intro e he
        simp [hne e he]
      rw [h1, h2]
      cases hf : ys.filter p with
      | nil => rfl
      | cons z zs =>
        have hz : z ∈ ys := by
          have : z ∈ ys.filter p := by rw [hf]; exact List.mem_cons_self
          exact (List.mem_filter.mp this).1
        exact insertBond_before_head y z zs (hy z hz)
    · have hc' : c ∈ ys := by
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h.symm hyc
        · exact h
      have hnb : ¬ c.before y := by
        have hb := hy c hc'
        unfold Bond.before at *; omega
      have hyc' : (y == c) = false := by simpa using hyc
      by_cases hpy : p y = true
      · simp [hpy, insertBond, hnb, ih hys hc']
      · have hpy' : p y = false := by simpa using hpy
        simp [hpy', hyc', ih hys hc']

/-! ## Reading tokens, wherever they stand -/

/-- Reading one list of tokens and then another: the second is read from the
state that the first one leaves. -/
theorem steps_append (s : Reading) (ps qs : List Placed) :
    steps s (ps ++ qs) =
      match steps s ps with
      | .error problem => .error problem
      | .ok next => steps next qs := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append, steps]
    cases h : step s p with
    | error problem => rfl
    | ok next => exact ih next

/-- Reading the tokens `tokens` from the state `s` succeeds, at whatever
positions the tokens stand, and the state afterwards has the property `P`. -/
def Reads (s : Reading) (tokens : List Token) (P : Reading → Prop) : Prop :=
  ∀ placed : List Placed, placed.map Placed.token = tokens →
    ∃ s', steps s placed = .ok s' ∧ P s'

/-- No token: the state stays as it is. -/
theorem Reads.nil {s : Reading} {P : Reading → Prop} (h : P s) : Reads s [] P := by
  intro placed hplaced
  have : placed = [] := by simpa using hplaced
  subst this
  exact ⟨s, rfl, h⟩

/-- One token, and then the rest. -/
theorem Reads.cons {s : Reading} {token : Token} {tokens : List Token} {P Q : Reading → Prop}
    (h1 : ∀ position, ∃ s', step s ⟨token, position⟩ = .ok s' ∧ Q s')
    (h2 : ∀ s', Q s' → Reads s' tokens P) : Reads s (token :: tokens) P := by
  intro placed hplaced
  cases placed with
  | nil => simp at hplaced
  | cons p ps =>
    simp only [List.map_cons, List.cons.injEq] at hplaced
    obtain ⟨hp, hps⟩ := hplaced
    obtain ⟨s1, hstep, hq⟩ := h1 p.position
    have hpe : (⟨token, p.position⟩ : Placed) = p := by
      cases p; simp at hp; simp [hp]
    rw [hpe] at hstep
    obtain ⟨s', hsteps, hP⟩ := h2 s1 hq ps hps
    exact ⟨s', by simp only [steps, hstep]; exact hsteps, hP⟩

/-- One list of tokens, and then another. -/
theorem Reads.append {s : Reading} {tokens more : List Token} {P Q : Reading → Prop}
    (h1 : Reads s tokens Q) (h2 : ∀ s', Q s' → Reads s' more P) :
    Reads s (tokens ++ more) P := by
  intro placed hplaced
  obtain ⟨l1, l2, rfl, hl1, hl2⟩ := List.map_eq_append_iff.mp hplaced
  obtain ⟨s1, hs1, hq⟩ := h1 l1 hl1
  obtain ⟨s', hs', hP⟩ := h2 s1 hq l2 hl2
  exact ⟨s', by rw [steps_append, hs1]; exact hs', hP⟩

/-- What holds afterwards may be replaced by something that follows from it. -/
theorem Reads.mono {s : Reading} {tokens : List Token} {P Q : Reading → Prop}
    (h : Reads s tokens P) (hPQ : ∀ s', P s' → Q s') : Reads s tokens Q := by
  intro placed hplaced
  obtain ⟨s', hs', hP⟩ := h placed hplaced
  exact ⟨s', hs', hPQ s' hP⟩

/-- One token alone. -/
theorem Reads.single {s : Reading} {token : Token} {P : Reading → Prop}
    (h : ∀ position, ∃ s', step s ⟨token, position⟩ = .ok s' ∧ P s') :
    Reads s [token] P :=
  Reads.cons h (fun _ hP => Reads.nil hP)

/-! ## Behind an atom -/

/-- The reader stands behind atom number `i`, or behind one of its ring
numbers: the next atom would be bonded to atom `i`, and no bond symbol and no
direction mark is waiting. -/
structure AtAtom (i : Nat) (s : Reading) : Prop where
  previous : s.previous = some i
  pending : s.pending = none
  last : s.last = .atom
  mark : s.mark = none

/-! ## The reader's table mirrors the writer's -/

/-- The reader's table of open ring numbers mirrors the writer's: the same
numbers are open, and for each the reader holds the earlier atom of the bond.
`noted bond symbol` says what the reader may have noted as the symbol of an
open bond: the symbol, or nothing where none stands in front of the ring
number (`notedSymbol` in `VeriMol/Proofs/Brackets.lean`, for both spellings). -/
def Mirrors (noted : Bond → Option BondOrder → Prop) (W : List (Nat × Bond))
    (R : List (Nat × OpenRing)) : Prop :=
  (∀ k, ringAt k W = none → ringAt k R = none) ∧
  (∀ k e, ringAt k W = some e →
    ∃ opened, ringAt k R = some opened ∧ opened.atom = e.a ∧ noted e opened.order)

/-- Both take the same number out. -/
theorem Mirrors.without {noted : Bond → Option BondOrder → Prop} {W : List (Nat × Bond)}
    {R : List (Nat × OpenRing)} (h : Mirrors noted W R) (k : Nat) :
    Mirrors noted (withoutRing k W) (withoutRing k R) := by
  constructor
  · intro k' hk'
    rw [ringAt_withoutRing] at hk' ⊢
    by_cases hkk : k = k'
    · simp [hkk]
    · simp [hkk] at hk' ⊢
      exact h.1 k' hk'
  · intro k' e hk'
    rw [ringAt_withoutRing] at hk' ⊢
    by_cases hkk : k = k'
    · simp [hkk] at hk'
    · simp [hkk] at hk' ⊢
      exact h.2 k' e hk'

/-- Both put the same number in. -/
theorem Mirrors.add {noted : Bond → Option BondOrder → Prop} {W : List (Nat × Bond)}
    {R : List (Nat × OpenRing)} (h : Mirrors noted W R) (k : Nat) (e : Bond)
    (symbol : Option BondOrder) (position place : Nat) (mark : Option (Bool × Nat))
    (hok : noted e symbol) :
    Mirrors noted ((k, e) :: W) ((k, ⟨e.a, symbol, position, place, mark⟩) :: R) := by
  constructor
  · intro k' hk'
    rw [ringAt_cons] at hk' ⊢
    by_cases hkk : k = k'
    · simp [hkk] at hk'
    · simp [hkk] at hk' ⊢
      exact h.1 k' hk'
  · intro k' x hk'
    rw [ringAt_cons] at hk' ⊢
    by_cases hkk : k = k'
    · simp [hkk] at hk' ⊢
      subst hk'
      exact ⟨rfl, hok⟩
    · simp [hkk] at hk' ⊢
      exact h.2 k' x hk'

/-- What is known about the writer's table: every entry is a bond of the `Mol`
with the property `Q`, and no bond stands under two numbers. -/
def TableHolds (l : List Bond) (Q : Bond → Prop) (W : List (Nat × Bond)) : Prop :=
  (∀ k e, ringAt k W = some e → e ∈ l ∧ Q e) ∧
  (∀ k k' e, ringAt k W = some e → ringAt k' W = some e → k = k')

/-- A property of the entries may be replaced by one that follows from it. -/
theorem TableHolds.mono {l : List Bond} {Q Q' : Bond → Prop} {W : List (Nat × Bond)}
    (h : TableHolds l Q W) (hQ : ∀ e ∈ l, Q e → Q' e) : TableHolds l Q' W :=
  ⟨fun k e hk => ⟨(h.1 k e hk).1, hQ e (h.1 k e hk).1 (h.1 k e hk).2⟩, h.2⟩

/-- Taking a number out: the bond it stood for is no longer in the table. -/
theorem TableHolds.without {l : List Bond} {Q : Bond → Prop} {W : List (Nat × Bond)}
    (h : TableHolds l Q W) {k : Nat} {e : Bond} (hk : ringAt k W = some e) :
    TableHolds l (fun x => Q x ∧ x ≠ e) (withoutRing k W) := by
  constructor
  · intro k' x hx
    rw [ringAt_withoutRing] at hx
    by_cases hkk : k = k'
    · simp [hkk] at hx
    · simp [hkk] at hx
      refine ⟨(h.1 k' x hx).1, (h.1 k' x hx).2, ?_⟩
      intro hxe
      subst hxe
      exact hkk (h.2 k k' x hk hx)
  · intro k1 k2 x h1 h2
    rw [ringAt_withoutRing] at h1 h2
    by_cases a1 : k = k1
    · simp [a1] at h1
    · by_cases a2 : k = k2
      · simp [a2] at h2
      · simp [a1] at h1
        simp [a2] at h2
        exact h.2 k1 k2 x h1 h2

/-- Putting a number in, for a bond that was not in the table. -/
theorem TableHolds.add {l : List Bond} {Q : Bond → Prop} {W : List (Nat × Bond)}
    (h : TableHolds l Q W) (k : Nat) {c : Bond} (hc : c ∈ l) (hnq : ¬ Q c) :
    TableHolds l (fun x => Q x ∨ x = c) ((k, c) :: W) := by
  constructor
  · intro k' x hx
    rw [ringAt_cons] at hx
    by_cases hkk : k = k'
    · simp [hkk] at hx
      subst hx
      exact ⟨hc, Or.inr rfl⟩
    · simp [hkk] at hx
      exact ⟨(h.1 k' x hx).1, Or.inl (h.1 k' x hx).2⟩
  · intro k1 k2 x h1 h2
    rw [ringAt_cons] at h1 h2
    by_cases a1 : k = k1
    · by_cases a2 : k = k2
      · rw [← a1, ← a2]
      · simp [a1] at h1
        simp [a2] at h2
        subst h1
        exact absurd (h.1 k2 _ h2).2 hnq
    · by_cases a2 : k = k2
      · simp [a1] at h1
        simp [a2] at h2
        subst h2
        exact absurd (h.1 k1 _ h1).2 hnq
      · simp [a1] at h1
        simp [a2] at h2
        exact h.2 k1 k2 x h1 h2

/-- The number that the writer finds for a bond stands for a bond between the
same two atoms. -/
theorem numberOf_some {W : List (Nat × Bond)} {c : Bond} {k : Nat} (h : numberOf W c = some k) :
    ∃ e, ringAt k W = some e ∧ e.a = c.a ∧ e.b = c.b := by
  unfold numberOf at h
  have hp := List.find?_some h
  cases hk : ringAt k W with
  | none => simp [hk] at hp
  | some e =>
    simp [hk] at hp
    exact ⟨e, rfl, hp.1, hp.2⟩

/-- The number that the writer takes as free is not in its table. -/
theorem freeNumber_some {W : List (Nat × Bond)} {k : Nat} (h : freeNumber W = some k) :
    ringAt k W = none := by
  unfold freeNumber at h
  have hp := List.find?_some h
  simpa using hp

/-! ## In front of an atom -/

/-- The atom just before atom `i`, if there is one. -/
def prevOf : Nat → Option Nat
  | 0 => none
  | p + 1 => some p

/-- If there is an atom just before atom `i`, then `i` is one more. -/
theorem prevOf_eq_some {i x : Nat} (h : prevOf i = some x) : i = x + 1 := by
  cases i with
  | zero => simp [prevOf] at h
  | succ k => simp [prevOf] at h; omega

/-- What the reader has read last when it stands in front of atom `i`. -/
def lastOf : Nat → Last
  | 0 => .nothing
  | _ + 1 => .atom

end VeriMol
