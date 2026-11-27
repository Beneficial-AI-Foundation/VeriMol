import VeriMol.Proofs.Facts

/-!
# What the reader notes, token by token

While it reads, the reader builds the atoms and the bonds, and it notes the
stereo marks and where they stand (`VeriMol/Core/Read.lean`). This file says
what the whole state of the reader is after each kind of token that the two
spellings write (`VeriMol/Core/Write.lean`), and then follows the ring numbers
of one atom (`closeRings_notes`, `openRings_notes`), for both spellings at
once. Between two tokens, `NotesAt` says what the reader has noted about
stereo marks. The places of the ring numbers in it are those that
`VeriMol/Proofs/Facts.lean` defines (`placeA`, `placeB`, `ringEntry`).

`VeriMol/Proofs/RoundTrip.lean` puts these together, atom by atom.
-/

namespace VeriMol

/-! ## One token at a time -/

/-- The atoms with `@` or `@@` so far, with one more atom if it carries a
mark. -/
def markedWith (marked : List MarkedAtom) (number : Nat) (written : WrittenAtom)
    (position : Nat) : List MarkedAtom :=
  match written.mark with
  | some mark => marked ++ [⟨number, mark, position⟩]
  | none => marked

/-- The direction marks so far, with the one that was noted at the number
that opened a ring bond, if there was one. -/
def noteDirections (a b : Nat) (mark : Option (Bool × Nat)) (directions : List Direction) :
    List Direction :=
  match mark with
  | some found => ⟨a, b, found.1, found.2⟩ :: directions
  | none => directions

/-- An atom with nothing in front of it that bonds it. -/
theorem step_atom_alone_eq {s : Reading} (written : WrittenAtom) (position : Nat)
    (hprev : s.previous = none) :
    step s ⟨.atom written, position⟩ = .ok { s with
      atoms := s.atoms ++ [written]
      previous := some s.atoms.length
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := 0
      marked := markedWith s.marked s.atoms.length written position } := by
  simp only [step, Last.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hprev, markedWith]
  cases written.mark <;> rfl

/-- An atom behind a bond symbol. -/
theorem step_atom_bonded_eq {s : Reading} {p symbolAt : Nat} {order : BondOrder}
    (written : WrittenAtom) (position : Nat) (hprev : s.previous = some p)
    (hpend : s.pending = some (order, symbolAt)) (hmark : s.mark = none) :
    step s ⟨.atom written, position⟩ = .ok { s with
      atoms := s.atoms ++ [written]
      bonds := insertBond ⟨p, s.atoms.length, order⟩ s.bonds
      previous := some s.atoms.length
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := 0
      marked := markedWith s.marked s.atoms.length written position } := by
  simp only [step, Last.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hprev, hpend, hmark,
    markedWith]
  cases written.mark <;> rfl

/-- An atom with no bond symbol and no direction mark in front of it, bonded
to an earlier atom: the bond gets the order that a reader assumes. -/
theorem step_atom_assumed_eq {s : Reading} {p : Nat} (written : WrittenAtom) (position : Nat)
    (hprev : s.previous = some p) (hpend : s.pending = none) (hmark : s.mark = none) :
    step s ⟨.atom written, position⟩ = .ok { s with
      atoms := s.atoms ++ [written]
      bonds := insertBond
        ⟨p, s.atoms.length, assumedOrder (s.atoms ++ [written]) p s.atoms.length⟩ s.bonds
      previous := some s.atoms.length
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := 0
      marked := markedWith s.marked s.atoms.length written position } := by
  simp only [step, Last.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hprev, hpend, hmark,
    markedWith]
  cases written.mark <;> rfl

/-- An atom behind a direction mark: the bond gets the order that a reader
assumes, and the mark is noted for it. -/
theorem step_atom_marked_eq {s : Reading} {p : Nat} {found : Bool × Nat} (written : WrittenAtom)
    (position : Nat) (hprev : s.previous = some p) (hpend : s.pending = none)
    (hmark : s.mark = some found) (hlt : p < s.atoms.length) :
    step s ⟨.atom written, position⟩ = .ok { s with
      atoms := s.atoms ++ [written]
      bonds := insertBond
        ⟨p, s.atoms.length, assumedOrder (s.atoms ++ [written]) p s.atoms.length⟩ s.bonds
      previous := some s.atoms.length
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := 0
      directions := ⟨p, s.atoms.length, found.1, found.2⟩ :: s.directions
      marked := markedWith s.marked s.atoms.length written position } := by
  simp only [step, Last.allows, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hprev, hpend, hmark,
    markedWith, directionAt, hlt]
  cases written.mark <;> rfl

/-- A bond symbol behind an atom or a ring number. -/
theorem step_order_eq {s : Reading} (order : BondOrder) (position : Nat) (hlast : s.last = .atom) :
    step s ⟨.bond (.order order), position⟩
      = .ok { s with pending := some (order, position), last := .bondAfterAtom } := by
  simp [step, Last.allows, hlast]

/-- A bond symbol behind `(`. -/
theorem step_order_open_eq {s : Reading} (order : BondOrder) (position : Nat)
    (hlast : s.last = .branchOpen) :
    step s ⟨.bond (.order order), position⟩
      = .ok { s with pending := some (order, position), last := .bondAfterOpen } := by
  simp [step, Last.allows, hlast]

/-- A bond symbol behind `)`. -/
theorem step_order_close_eq {s : Reading} (order : BondOrder) (position : Nat)
    (hlast : s.last = .branchClose) :
    step s ⟨.bond (.order order), position⟩
      = .ok { s with pending := some (order, position), last := .bondAfterClose } := by
  simp [step, Last.allows, hlast]

/-- The token of a direction mark: `/` if `up`, and `\` if not. -/
def markToken (up : Bool) : Token := .bond (if up then .up else .down)

/-- A direction mark behind an atom or a ring number. -/
theorem step_mark_eq {s : Reading} (up : Bool) (position : Nat) (hlast : s.last = .atom) :
    step s ⟨markToken up, position⟩
      = .ok { s with mark := some (up, position), last := .bondAfterAtom } := by
  cases up <;> simp [markToken, step, Last.allows, hlast]

/-- A direction mark behind `(`. -/
theorem step_mark_open_eq {s : Reading} (up : Bool) (position : Nat)
    (hlast : s.last = .branchOpen) :
    step s ⟨markToken up, position⟩
      = .ok { s with mark := some (up, position), last := .bondAfterOpen } := by
  cases up <;> simp [markToken, step, Last.allows, hlast]

/-- A direction mark behind `)`. -/
theorem step_mark_close_eq {s : Reading} (up : Bool) (position : Nat)
    (hlast : s.last = .branchClose) :
    step s ⟨markToken up, position⟩
      = .ok { s with mark := some (up, position), last := .bondAfterClose } := by
  cases up <;> simp [markToken, step, Last.allows, hlast]

/-- A dot behind an atom or behind `)`. -/
theorem step_dot_eq {s : Reading} (position : Nat)
    (hlast : s.last = .atom ∨ s.last = .branchClose) :
    step s ⟨.dot, position⟩ = .ok { s with previous := none, last := .dot position } := by
  rcases hlast with hlast | hlast <;> simp [step, Last.allows, hlast]

/-- `(` behind an atom or behind `)`. -/
theorem step_branchOpen_eq {s : Reading} (position : Nat)
    (hlast : s.last = .atom ∨ s.last = .branchClose) :
    step s ⟨.branchOpen, position⟩
      = .ok { s with branches := (s.previous, position) :: s.branches, last := .branchOpen } := by
  rcases hlast with hlast | hlast <;> simp [step, Last.allows, hlast]

/-- `)` behind an atom or behind `)`. -/
theorem step_branchClose_eq {s : Reading} {saved : Option Nat} {openedAt : Nat}
    {rest : List (Option Nat × Nat)} (position : Nat)
    (hlast : s.last = .atom ∨ s.last = .branchClose)
    (hbranches : s.branches = (saved, openedAt) :: rest) :
    step s ⟨.branchClose, position⟩
      = .ok { s with previous := saved, branches := rest, last := .branchClose } := by
  rcases hlast with hlast | hlast <;> simp [step, Last.allows, hlast, hbranches]

/-- A ring number that is not open: it opens. The reader notes the atom, the
bond symbol in front of the number if there is one, the place of the number
among the ring numbers of its atom, and the direction mark in front of it if
there is one. -/
theorem step_ringOpen_eq {s : Reading} {i k : Nat} (position : Nat) (hprev : s.previous = some i)
    (hlast : s.last = .atom ∨ s.last = .bondAfterAtom) (hfree : ringAt k s.rings = none) :
    step s ⟨.ring k, position⟩ = .ok { s with
      rings := (k, ⟨i, s.pending.map (·.1), position, s.numbersAtAtom, s.mark⟩) :: s.rings
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := s.numbersAtAtom + 1 } := by
  rcases hlast with hlast | hlast <;> simp [step, Last.allows, hlast, hprev, hfree]

/-- A ring number that is open, behind its atom with no symbol and no mark in
front of it: it closes. The bond is put at its place, and the reader notes
the places of its two ring numbers, and the direction mark of the number that
opened it. -/
theorem step_ringClose_eq {s : Reading} {i k : Nat} {opened : OpenRing} {order : BondOrder}
    (position : Nat) (h : AtAtom i s) (hring : ringAt k s.rings = some opened)
    (hlt : opened.atom < i)
    (horder : ringOrder opened.order none (assumedOrder s.atoms opened.atom i) = some order)
    (hnew : ∀ bond ∈ s.bonds, ¬(bond.a = opened.atom ∧ bond.b = i)) :
    step s ⟨.ring k, position⟩ = .ok { s with
      bonds := insertBond ⟨opened.atom, i, order⟩ s.bonds
      rings := withoutRing k s.rings
      pending := none
      last := .atom
      mark := none
      numbersAtAtom := s.numbersAtAtom + 1
      ringBonds := ⟨opened.atom, i, opened.place, s.numbersAtAtom⟩ :: s.ringBonds
      directions := noteDirections opened.atom i opened.mark s.directions } := by
  have hmin : min opened.atom i = opened.atom := Nat.min_eq_left (Nat.le_of_lt hlt)
  have hmax : max opened.atom i = i := Nat.max_eq_right (Nat.le_of_lt hlt)
  have hstep : step s ⟨.ring k, position⟩ = closeRing s k opened i position := by
    simp [step, Last.allows, h.last, h.previous, hring]
  have hany : (s.bonds.any fun bond => decide (bond.a = opened.atom ∧ bond.b = i)) = false := by
    rw [List.any_eq_false]
    intro bond hbond
    simpa using hnew bond hbond
  rw [hstep]
  unfold closeRing
  simp only [Nat.ne_of_lt hlt, ↓reduceIte, h.pending, Option.map_none,
    horder, h.mark, Option.isSome_none, Bool.and_false, Bool.false_and, Bool.or_self,
    Bool.false_eq_true, hmin, hmax, hany, hlt, noteDirections]
  cases hm : opened.mark with
  | none => rfl
  | some found => simp [directionAt, hlt]

/-! ## Lists in order -/

/-- In a list in rising order of a key, the entries with a smaller key than
one entry are those that stand before it. -/
theorem rising_filter_lt {δ : Type} (key : δ → Nat) (done : List δ) (c : δ) (rest : List δ)
    (h : (done ++ c :: rest).Pairwise (fun x y => key x < key y)) :
    (done ++ c :: rest).filter (fun x => decide (key x < key c)) = done := by
  rw [List.pairwise_append] at h
  obtain ⟨_, hcr, hdc⟩ := h
  rw [List.pairwise_cons] at hcr
  rw [List.filter_append]
  have h1 : done.filter (fun x => decide (key x < key c)) = done := by
    rw [List.filter_eq_self]
    intro x hx
    simpa using hdc x hx c List.mem_cons_self
  have h2 : (c :: rest).filter (fun x => decide (key x < key c)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have := hcr.1 x hx
      simp
      omega
  rw [h1, h2, List.append_nil]

/-- The ring numbers that close at an atom stand in the order of the atoms
where they opened. -/
theorem closes_sorted {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool) (i : Nat) :
    (l.filter (closesAt ring i)).Pairwise (fun x y => x.a < y.a) := by
  refine List.Pairwise.imp_of_mem ?_ (hl.filter _)
  intro x y hx hy hxy
  have hxb := (List.mem_filter.mp hx).2
  have hyb := (List.mem_filter.mp hy).2
  simp only [closesAt, Bool.and_eq_true, beq_iff_eq] at hxb hyb
  have h1 := hxb.1
  have h2 := hyb.1
  unfold Bond.before at hxy
  omega

/-- The ring numbers that open at an atom stand in the order of the atoms
where they will close. -/
theorem opens_sorted {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool) (i : Nat) :
    (l.filter (opensAt ring i)).Pairwise (fun x y => x.b < y.b) := by
  refine List.Pairwise.imp_of_mem ?_ (hl.filter _)
  intro x y hx hy hxy
  have hxb := (List.mem_filter.mp hx).2
  have hyb := (List.mem_filter.mp hy).2
  simp only [opensAt, Bool.and_eq_true, beq_iff_eq] at hxb hyb
  have h1 := hxb.1
  have h2 := hyb.1
  unfold Bond.before at hxy
  omega

/-- The place of a ring number that closes: as many numbers close at its atom
before it. -/
theorem placeB_eq {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool) {i : Nat}
    {done : List Bond} {c : Bond} {rest : List Bond}
    (hfull : l.filter (closesAt ring i) = done ++ c :: rest) :
    placeB l ring c.a i = done.length := by
  unfold placeB
  rw [← List.filter_filter, hfull]
  have := closes_sorted hl ring i
  rw [hfull] at this
  rw [rising_filter_lt (fun x => x.a) done c rest this]

/-- The place of a ring number that opens: behind all that close at its atom,
and behind those that open there before it. -/
theorem placeA_eq {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool) {i : Nat}
    {done : List Bond} {c : Bond} {rest : List Bond}
    (hfull : l.filter (opensAt ring i) = done ++ c :: rest) :
    placeA l ring i c.b = (l.filter (closesAt ring i)).length + done.length := by
  unfold placeA
  congr 1
  rw [← List.filter_filter, hfull]
  have := opens_sorted hl ring i
  rw [hfull] at this
  rw [rising_filter_lt (fun x => x.b) done c rest this]

/-- Keeping one more entry of a list: the entries that were kept, and that
one. -/
theorem nodup_filter_or_beq_perm {l : List Bond} (hnd : l.Nodup) {e : Bond} (he : e ∈ l)
    (q : Bond → Bool) (hq : q e = false) :
    (l.filter fun x => q x || x == e).Perm (e :: l.filter q) := by
  induction l with
  | nil => cases he
  | cons y ys ih =>
    rw [List.nodup_cons] at hnd
    by_cases hye : y = e
    · subst hye
      have hsame : ys.filter (fun x => q x || x == y) = ys.filter q := by
        apply List.filter_congr
        intro x hx
        have : (x == y) = false := by
          have : x ≠ y := fun e' => hnd.1 (e' ▸ hx)
          simpa using this
        rw [this, Bool.or_false]
      simp only [List.filter_cons, hq, beq_self_eq_true, Bool.or_true, ↓reduceIte,
        Bool.false_eq_true, hsame]
      exact List.Perm.refl _
    · have hey : e ∈ ys := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hye
        · exact h
      have hb : (y == e) = false := by simpa using hye
      have ih' := ih hnd.2 hey
      cases hqy : q y with
      | true =>
        simp only [List.filter_cons, hqy, Bool.true_or, ↓reduceIte]
        exact (ih'.cons y).trans (List.Perm.swap e y _)
      | false =>
        simp only [List.filter_cons, hqy, hb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        exact ih'

/-! ## The notes of the reader, between two tokens -/

/-- What the reader has noted about stereo marks. `p` says which bonds it has
read, and `W` is the writer's table of the ring numbers that are open.

* For every bond that is read and that is written with a ring number, the
  places of its two numbers.
* A direction for exactly the bonds that are read and that carry a mark.
* For every ring number that is open, its place, and the mark in front of
  it. -/
structure NotesAt (l : List Bond) (ring : Bond → Bool) (marks : List ((Nat × Nat) × Bool))
    (p : Bond → Bool) (W : List (Nat × Bond)) (s : Reading) : Prop where
  ringBonds : s.ringBonds.Perm ((l.filter fun e => ring e && p e).map (ringEntry l ring))
  marked : ∀ d ∈ s.directions, ∃ e ∈ l, p e = true ∧ d.a = e.a ∧ d.b = e.b ∧
    markAmong marks (e.a, e.b) = some d.above
  noted : ∀ e ∈ l, p e = true → ∀ up, markAmong marks (e.a, e.b) = some up →
    ∃ d ∈ s.directions, d.a = e.a ∧ d.b = e.b ∧ d.above = up
  opened : ∀ k e, ringAt k W = some e → ∃ note, ringAt k s.rings = some note ∧
    note.place = placeA l ring e.a e.b ∧ note.mark.map (·.1) = markAmong marks (e.a, e.b)

/-- The same notes, for a state with the same notes and another way of saying
which bonds are read. -/
theorem NotesAt.congr {l : List Bond} {ring : Bond → Bool} {marks : List ((Nat × Nat) × Bool)}
    {p p' : Bond → Bool} {W : List (Nat × Bond)} {s s' : Reading}
    (h : NotesAt l ring marks p W s) (hp : ∀ e ∈ l, p e = p' e)
    (hringBonds : s'.ringBonds = s.ringBonds) (hdirections : s'.directions = s.directions)
    (hrings : s'.rings = s.rings) : NotesAt l ring marks p' W s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hringBonds]
    have : (l.filter fun e => ring e && p' e) = l.filter fun e => ring e && p e := by
      apply List.filter_congr
      intro e he
      rw [hp e he]
    rw [this]
    exact h.ringBonds
  · intro d hd
    rw [hdirections] at hd
    obtain ⟨e, he, hpe, rest⟩ := h.marked d hd
    exact ⟨e, he, by rw [← hp e he]; exact hpe, rest⟩
  · intro e he hpe up hup
    rw [hdirections]
    exact h.noted e he (by rw [hp e he]; exact hpe) up hup
  · intro k e hk
    rw [hrings]
    exact h.opened k e hk

/-- A ring number opens: the reader notes its place and the mark in front of
it. -/
theorem NotesAt.add {l : List Bond} {ring : Bond → Bool} {marks : List ((Nat × Nat) × Bool)}
    {p : Bond → Bool} {W : List (Nat × Bond)} {s s' : Reading} (h : NotesAt l ring marks p W s)
    {k : Nat} {c : Bond} {mark : Option (Bool × Nat)} (hringBonds : s'.ringBonds = s.ringBonds)
    (hdirections : s'.directions = s.directions)
    {atom position : Nat} {order : Option BondOrder}
    (hrings : s'.rings = (k, ⟨atom, order, position, placeA l ring c.a c.b, mark⟩) :: s.rings)
    (hmark : mark.map (·.1) = markAmong marks (c.a, c.b)) :
    NotesAt l ring marks p ((k, c) :: W) s' := by
  refine ⟨by rw [hringBonds]; exact h.ringBonds, ?_, ?_, ?_⟩
  · intro d hd
    rw [hdirections] at hd
    exact h.marked d hd
  · intro e he hpe up hup
    rw [hdirections]
    exact h.noted e he hpe up hup
  · intro k' e hk'
    rw [ringAt_cons] at hk'
    rw [hrings, ringAt_cons]
    by_cases hkk : k = k'
    · simp only [hkk, ↓reduceIte, Option.some.injEq] at hk' ⊢
      subst hk'
      exact ⟨_, rfl, rfl, hmark⟩
    · simp only [hkk, ↓reduceIte] at hk' ⊢
      exact h.opened k' e hk'

/-- A ring number closes: its bond is read, and the reader notes the places of
its two numbers, and its direction if the number that opened it had a mark. -/
theorem NotesAt.close {l : List Bond} {ring : Bond → Bool} {marks : List ((Nat × Nat) × Bool)}
    {p : Bond → Bool} {W : List (Nat × Bond)} {s s' : Reading} (hl : l.Pairwise Bond.before)
    (h : NotesAt l ring marks p W s) {k : Nat} {e : Bond} {note : OpenRing} (hel : e ∈ l)
    (hre : ring e = true) (hpe : p e = false)
    (hnmark : note.mark.map (·.1) = markAmong marks (e.a, e.b))
    (hringBonds : s'.ringBonds = ringEntry l ring e :: s.ringBonds)
    (hdirections : s'.directions = noteDirections e.a e.b note.mark s.directions)
    (hrings : s'.rings = withoutRing k s.rings) :
    NotesAt l ring marks (fun x => p x || x == e) (withoutRing k W) s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hringBonds]
    have h1 : (l.filter fun x => ring x && (p x || x == e))
        = l.filter fun x => (ring x && p x) || x == e := by
      apply List.filter_congr
      intro x _
      by_cases hxe : x = e
      · subst hxe
        simp [hre]
      · have : (x == e) = false := by simpa using hxe
        simp [this]
    have h2 := nodup_filter_or_beq_perm (nodup_of_ordered hl) hel (fun x => ring x && p x)
      (by simp [hpe])
    rw [h1]
    exact (h.ringBonds.cons _).trans (h2.map _).symm
  · intro d hd
    rw [hdirections] at hd
    have hold : d ∈ s.directions → ∃ e' ∈ l, (p e' || e' == e) = true ∧ d.a = e'.a ∧ d.b = e'.b ∧
        markAmong marks (e'.a, e'.b) = some d.above := by
      intro hd'
      obtain ⟨e', he', hpe', rest⟩ := h.marked d hd'
      exact ⟨e', he', by simp [hpe'], rest⟩
    unfold noteDirections at hd
    cases hm : note.mark with
    | none =>
      rw [hm] at hd
      exact hold hd
    | some found =>
      rw [hm] at hd
      rcases List.mem_cons.1 hd with rfl | hd'
      · refine ⟨e, hel, by simp, rfl, rfl, ?_⟩
        rw [← hnmark, hm]
        rfl
      · exact hold hd'
  · intro e' he' hpe' up hup
    rw [hdirections]
    have hin : ∀ d, d ∈ s.directions → d ∈ noteDirections e.a e.b note.mark s.directions := by
      intro d hd
      unfold noteDirections
      cases note.mark with
      | none => exact hd
      | some found => exact List.mem_cons_of_mem _ hd
    by_cases hee : e' = e
    · subst hee
      rw [← hnmark] at hup
      cases hm : note.mark with
      | none => rw [hm] at hup; cases hup
      | some found =>
        rw [hm] at hup
        simp only [Option.map_some, Option.some.injEq] at hup
        refine ⟨⟨e'.a, e'.b, found.1, found.2⟩, ?_, rfl, rfl, hup⟩
        unfold noteDirections
        exact List.mem_cons_self
    · have hb : (e' == e) = false := by simpa using hee
      rw [hb, Bool.or_false] at hpe'
      obtain ⟨d, hd, rest⟩ := h.noted e' he' hpe' up hup
      exact ⟨d, hin d hd, rest⟩
  · intro k' e' hk'
    rw [ringAt_withoutRing] at hk'
    rw [hrings, ringAt_withoutRing]
    by_cases hkk : k = k'
    · simp [hkk] at hk'
    · simp only [hkk, ↓reduceIte] at hk' ⊢
      exact h.opened k' e' hk'

/-- An atom is written next to an earlier atom: the bond between the two is
read. It has no ring number, and the reader notes its direction if a mark
stands in front of the atom. -/
theorem NotesAt.chain {l : List Bond} {ring : Bond → Bool} {marks : List ((Nat × Nat) × Bool)}
    {p : Bond → Bool} {W : List (Nat × Bond)} {s s' : Reading} (h : NotesAt l ring marks p W s)
    {e : Bond} (hel : e ∈ l) (hre : ring e = false) (hringBonds : s'.ringBonds = s.ringBonds)
    (hrings : s'.rings = s.rings)
    (hdirections : (markAmong marks (e.a, e.b) = none ∧ s'.directions = s.directions) ∨
      ∃ up position, markAmong marks (e.a, e.b) = some up ∧
        s'.directions = ⟨e.a, e.b, up, position⟩ :: s.directions) :
    NotesAt l ring marks (fun x => p x || x == e) W s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hringBonds]
    have h1 : (l.filter fun x => ring x && (p x || x == e)) = l.filter fun x => ring x && p x := by
      apply List.filter_congr
      intro x _
      by_cases hxe : x = e
      · subst hxe
        simp [hre]
      · have : (x == e) = false := by simpa using hxe
        simp [this]
    rw [h1]
    exact h.ringBonds
  · intro d hd
    have hold : d ∈ s.directions → ∃ e' ∈ l, (p e' || e' == e) = true ∧ d.a = e'.a ∧ d.b = e'.b ∧
        markAmong marks (e'.a, e'.b) = some d.above := by
      intro hd'
      obtain ⟨e', he', hpe', rest⟩ := h.marked d hd'
      exact ⟨e', he', by simp [hpe'], rest⟩
    rcases hdirections with ⟨_, hsame⟩ | ⟨up, position, hup, hnew⟩
    · rw [hsame] at hd
      exact hold hd
    · rw [hnew] at hd
      rcases List.mem_cons.1 hd with rfl | hd'
      · exact ⟨e, hel, by simp, rfl, rfl, hup⟩
      · exact hold hd'
  · intro e' he' hpe' up hup
    by_cases hee : e' = e
    · subst hee
      rcases hdirections with ⟨hnone, _⟩ | ⟨up', position, hup', hnew⟩
      · rw [hnone] at hup
        cases hup
      · rw [hup'] at hup
        cases hup
        rw [hnew]
        exact ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩
    · have hb : (e' == e) = false := by simpa using hee
      rw [hb, Bool.or_false] at hpe'
      obtain ⟨d, hd, rest⟩ := h.noted e' he' hpe' up hup
      rcases hdirections with ⟨_, hsame⟩ | ⟨_, _, _, hnew⟩
      · exact ⟨d, by rw [hsame]; exact hd, rest⟩
      · exact ⟨d, by rw [hnew]; exact List.mem_cons_of_mem _ hd, rest⟩
  · intro k e' hk
    rw [hrings]
    exact h.opened k e' hk

/-! ## The ring numbers of one atom -/

/-- The ring numbers that close at atom `i`: the reader puts each bond at its
place, and notes it. For that, what the reader noted at the number that
opened must give the order of the bond. `done` holds the bonds whose numbers
were closed at this atom before: the reader has counted one ring number at
the atom for each of them. -/
theorem closeRings_notes {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool)
    (marks : List ((Nat × Nat) × Bool)) (noted : Bond → Option BondOrder → Prop) (i : Nat) :
    ∀ (cs done : List Bond) (W W' : List (Nat × Bond)) (tokens : List Token) (s : Reading)
      (Q : Bond → Prop) (p : Bond → Bool),
      closeRings W cs = some (tokens, W') →
      l.filter (closesAt ring i) = done ++ cs → s.numbersAtAtom = done.length →
      TableHolds l Q W → Mirrors noted W s.rings → AtAtom i s → s.bonds = l.filter p →
      NotesAt l ring marks p W s →
      (∀ c ∈ cs, c ∈ l ∧ c.a < i ∧ c.b = i ∧ p c = false) → cs.Nodup →
      (∀ c ∈ cs, ∀ o, noted c o →
        ringOrder o none (assumedOrder s.atoms c.a i) = some c.order) →
      Reads s tokens (fun s' => Mirrors noted W' s'.rings ∧
        TableHolds l (fun e => Q e ∧ e ∉ cs) W' ∧ AtAtom i s' ∧ s'.atoms = s.atoms ∧
        s'.branches = s.branches ∧ s'.bonds = l.filter (fun e => p e || cs.contains e) ∧
        s'.numbersAtAtom = done.length + cs.length ∧ s'.marked = s.marked ∧
        NotesAt l ring marks (fun e => p e || cs.contains e) W' s') := by
  intro cs
  induction cs with
  | nil =>
    intro done W W' tokens s Q p hw _ hnumbers hinv hrel hat hbonds hn _ _ _
    simp only [closeRings, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact Reads.nil
      ⟨hrel, hinv.mono (fun e _ h => ⟨h, by simp⟩), hat, rfl, rfl, by simpa using hbonds,
        by simpa using hnumbers, rfl, hn.congr (fun e _ => by simp) rfl rfl rfl⟩
  | cons c cs ih =>
    intro done W W' tokens s Q p hw hfull hnumbers hinv hrel hat hbonds hn hcs hnd hsym
    simp only [closeRings] at hw
    cases hk : numberOf W c with
    | none => simp [hk] at hw
    | some k =>
      simp only [hk] at hw
      cases hrest : closeRings (withoutRing k W) cs with
      | none => simp [hrest] at hw
      | some r =>
        obtain ⟨tokens', W1⟩ := r
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hcl, hca, hcb, hpc⟩ := hcs c List.mem_cons_self
        -- the bond that stands under the number k is c itself
        obtain ⟨e, hke, hea, heb⟩ := numberOf_some hk
        have hec : e = c := key_unique hl (hinv.1 k e hke).1 hcl hea heb
        subst hec
        obtain ⟨opened, hopened, hoa, hok⟩ := hrel.2 k e hke
        obtain ⟨note, hnote, hplace, hnmark⟩ := hn.opened k e hke
        obtain rfl : opened = note := by
          rw [hopened] at hnote
          exact Option.some.inj hnote
        obtain ⟨hecs, hnd'⟩ := List.nodup_cons.mp hnd
        have hbond : (⟨opened.atom, i, e.order⟩ : Bond) = e := by rw [hoa, ← hcb]
        have horder : ringOrder opened.order none (assumedOrder s.atoms opened.atom i)
            = some e.order := by
          rw [hoa]
          exact hsym e List.mem_cons_self opened.order hok
        have hre : ring e = true := by
          have : e ∈ l.filter (closesAt ring i) := by
            rw [hfull]
            exact List.mem_append_right _ List.mem_cons_self
          have := (List.mem_filter.1 this).2
          simp only [closesAt, Bool.and_eq_true] at this
          exact this.2
        -- the reader notes the places of the two ring numbers of the bond
        have hentry : (⟨opened.atom, i, opened.place, s.numbersAtAtom⟩ : RingBond)
            = ringEntry l ring e := by
          have hB := placeB_eq hl ring hfull
          simp only [ringEntry, hoa, hplace, hnumbers]
          rw [← hcb] at hB ⊢
          rw [hB]
        refine Reads.cons (Q := fun s1 => AtAtom i s1 ∧ s1.atoms = s.atoms ∧
            s1.branches = s.branches ∧ s1.bonds = insertBond e s.bonds ∧
            s1.rings = withoutRing k s.rings ∧ s1.numbersAtAtom = s.numbersAtAtom + 1 ∧
            s1.marked = s.marked ∧ s1.ringBonds = ringEntry l ring e :: s.ringBonds ∧
            s1.directions = noteDirections e.a e.b opened.mark s.directions) ?_ ?_
        · intro position
          refine ⟨_, step_ringClose_eq position hat hopened (by omega) horder (by
              intro y hy hkey
              rw [hbonds] at hy
              obtain ⟨hyl, hpy⟩ := List.mem_filter.mp hy
              have hye : y = e := key_unique hl hyl hcl (by omega) (by omega)
              rw [hye, hpc] at hpy
              exact absurd hpy (by simp)), ?_⟩
          refine ⟨⟨hat.previous, rfl, rfl, rfl⟩, rfl, rfl, by rw [← hbond], rfl, rfl, rfl,
            by rw [← hentry], ?_⟩
          show noteDirections opened.atom i opened.mark s.directions = _
          rw [hoa, hcb]
        · intro s1 ⟨hat1, hatoms1, hbranches1, hbonds1, hrings1, hnumbers1, hmarked1,
            hringBonds1, hdirections1⟩
          have hb1 : s1.bonds = l.filter (fun x => p x || x == e) := by
            rw [hbonds1, hbonds]
            exact insertBond_filter hl p hcl hpc
          have hn1 : NotesAt l ring marks (fun x => p x || x == e) (withoutRing k W) s1 :=
            NotesAt.close hl hn hcl hre hpc hnmark hringBonds1 hdirections1 hrings1
          refine (ih (done ++ [e]) (withoutRing k W) W1 tokens' s1 (fun x => Q x ∧ x ≠ e)
            (fun x => p x || x == e) hrest (by rw [hfull]; simp)
            (by rw [hnumbers1, hnumbers]; simp) (hinv.without hke) (hrings1 ▸ hrel.without k) hat1
            hb1 hn1 ?_ hnd' ?_).mono ?_
          · intro c' hc'
            obtain ⟨h1, h2, h3, h4⟩ := hcs c' (List.mem_cons_of_mem _ hc')
            refine ⟨h1, h2, h3, ?_⟩
            have hne' : c' ≠ e := fun h => hecs (h ▸ hc')
            simp [h4, hne']
          · intro c' hc' o ho
            rw [hatoms1]
            exact hsym c' (List.mem_cons_of_mem _ hc') o ho
          · intro s' ⟨hrel', hinv', hat', hatoms', hbranches', hbonds', hnumbers', hmarked', hn'⟩
            have hpred : ∀ x ∈ l, ((p x || x == e) || cs.contains x)
                = (p x || (e :: cs).contains x) := by
              intro x _
              by_cases hxe : x = e
              · simp [hxe]
              · have hb : (x == e) = false := by simpa using hxe
                simp [hb, hxe]
            refine ⟨hrel', hinv'.mono ?_, hat', by rw [hatoms', hatoms1],
              by rw [hbranches', hbranches1], ?_, ?_, by rw [hmarked', hmarked1],
              hn'.congr hpred rfl rfl rfl⟩
            · intro x _ hx
              refine ⟨hx.1.1, ?_⟩
              simp only [List.mem_cons, not_or]
              exact ⟨hx.1.2, hx.2⟩
            · rw [hbonds']
              apply List.filter_congr
              intro x hx
              exact hpred x hx
            · rw [hnumbers']
              simp
              omega

/-- The ring numbers that open at atom `i`: the reader notes each one, with
the atom, and with the bond symbol or the mark, if one is written. In front
of a number stands the mark of its bond if it carries one, and otherwise what
`symbol` writes: the symbol of the bond, or nothing. `done` holds the bonds
whose numbers were opened at this atom before. -/
theorem openRings_notes {l : List Bond} (hl : l.Pairwise Bond.before) (ring : Bond → Bool)
    (marks : List ((Nat × Nat) × Bool)) (noted : Bond → Option BondOrder → Prop)
    (symbol : Bond → List Token) (i : Nat) :
    ∀ (os done : List Bond) (W W' : List (Nat × Bond)) (tokens : List Token) (s : Reading)
      (Q : Bond → Prop) (p : Bond → Bool),
      openRings (markedSymbol marks symbol) W os = some (tokens, W') →
      l.filter (opensAt ring i) = done ++ os →
      s.numbersAtAtom = (l.filter (closesAt ring i)).length + done.length →
      TableHolds l Q W → Mirrors noted W s.rings → AtAtom i s → NotesAt l ring marks p W s →
      (∀ c ∈ os, c ∈ l ∧ c.a = i ∧ ¬ Q c) → os.Nodup →
      (∀ c ∈ os, markAmong marks (c.a, c.b) = none →
        (symbol c = [.bond (.order c.order)] ∧ noted c (some c.order)) ∨
        (symbol c = [] ∧ noted c none)) →
      (∀ c ∈ os, ∀ up, markAmong marks (c.a, c.b) = some up → noted c none) →
      Reads s tokens (fun s' => Mirrors noted W' s'.rings ∧
        TableHolds l (fun e => Q e ∨ e ∈ os) W' ∧ AtAtom i s' ∧ s'.atoms = s.atoms ∧
        s'.branches = s.branches ∧ s'.bonds = s.bonds ∧ s'.marked = s.marked ∧
        NotesAt l ring marks p W' s') := by
  intro os
  induction os with
  | nil =>
    intro done W W' tokens s Q p hw _ _ hinv hrel hat hn _ _ _ _
    simp only [openRings, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact Reads.nil ⟨hrel, hinv.mono (fun e _ h => Or.inl h), hat, rfl, rfl, rfl, rfl, hn⟩
  | cons c os ih =>
    intro done W W' tokens s Q p hw hfull hnumbers hinv hrel hat hn hos hnd hsym hmarked
    simp only [openRings] at hw
    cases hk : freeNumber W with
    | none => simp [hk] at hw
    | some k =>
      simp only [hk] at hw
      cases hrest : openRings (markedSymbol marks symbol) ((k, c) :: W) os with
      | none => simp [hrest] at hw
      | some r =>
        obtain ⟨tokens', W1⟩ := r
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hcl, hca, hnq⟩ := hos c List.mem_cons_self
        have hfree : ringAt k W = none := freeNumber_some hk
        obtain ⟨hcos, hnd'⟩ := List.nodup_cons.mp hnd
        -- the place of the ring number of c among the ring numbers of the atom
        have hplace : s.numbersAtAtom = placeA l ring c.a c.b := by
          rw [hnumbers, hca, placeA_eq hl ring hfull]
        -- what is read after the ring number of c, whichever way it was written
        have hafter : ∀ s2, (AtAtom i s2 ∧ s2.atoms = s.atoms ∧ s2.bonds = s.bonds ∧
            s2.branches = s.branches ∧ Mirrors noted ((k, c) :: W) s2.rings ∧
            s2.marked = s.marked ∧ s2.numbersAtAtom = s.numbersAtAtom + 1 ∧
            NotesAt l ring marks p ((k, c) :: W) s2) →
            Reads s2 tokens' (fun s' => Mirrors noted W1 s'.rings ∧
              TableHolds l (fun e => Q e ∨ e ∈ c :: os) W1 ∧ AtAtom i s' ∧
              s'.atoms = s.atoms ∧ s'.branches = s.branches ∧ s'.bonds = s.bonds ∧
              s'.marked = s.marked ∧ NotesAt l ring marks p W1 s') := by
          intro s2 ⟨hat2, hatoms2, hbonds2, hbranches2, hrel2, hmarked2, hnumbers2, hn2⟩
          refine (ih (done ++ [c]) ((k, c) :: W) W1 tokens' s2 (fun x => Q x ∨ x = c) p hrest
            (by rw [hfull]; simp) (by rw [hnumbers2, hnumbers]; simp; omega)
            (hinv.add k hcl hnq) hrel2 hat2 hn2 ?_ hnd'
            (fun c' hc' => hsym c' (List.mem_cons_of_mem _ hc'))
            (fun c' hc' => hmarked c' (List.mem_cons_of_mem _ hc'))).mono ?_
          · intro c' hc'
            obtain ⟨h1, h2, h3⟩ := hos c' (List.mem_cons_of_mem _ hc')
            refine ⟨h1, h2, ?_⟩
            intro h
            rcases h with h | h
            · exact h3 h
            · exact hcos (h ▸ hc')
          · intro s' ⟨hrel', hinv', hat', hatoms', hbranches', hbonds', hmarked', hn'⟩
            refine ⟨hrel', hinv'.mono ?_, hat', by rw [hatoms', hatoms2],
              by rw [hbranches', hbranches2], by rw [hbonds', hbonds2],
              by rw [hmarked', hmarked2], hn'⟩
            intro x _ hx
            simp only [List.mem_cons]
            rcases hx with (h | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        unfold markedSymbol
        cases hm : markAmong marks (c.a, c.b) with
        | some up =>
          -- the direction mark, then the ring number
          show Reads s (markToken up :: Token.ring k :: tokens') _
          refine Reads.cons (Q := fun s1 => s1.atoms = s.atoms ∧ s1.bonds = s.bonds ∧
              s1.rings = s.rings ∧ s1.previous = some i ∧ s1.branches = s.branches ∧
              s1.pending = none ∧ s1.last = .bondAfterAtom ∧
              (∃ markAt, s1.mark = some (up, markAt)) ∧ s1.numbersAtAtom = s.numbersAtAtom ∧
              s1.ringBonds = s.ringBonds ∧
              s1.directions = s.directions ∧ s1.marked = s.marked) ?_ ?_
          · intro position
            exact ⟨_, step_mark_eq up position hat.last, rfl, rfl, rfl, hat.previous, rfl,
              hat.pending, rfl, ⟨position, rfl⟩, rfl, rfl, rfl, rfl⟩
          · intro s1 ⟨hatoms1, hbonds1, hrings1, hprev1, hbranches1, hpend1, hlast1,
              ⟨markAt, hmark1⟩, hnumbers1, hringBonds1, hdirections1, hmarked1⟩
            refine Reads.cons ?_ hafter
            intro position
            refine ⟨_, step_ringOpen_eq position hprev1 (Or.inr hlast1)
              (hrings1 ▸ hrel.1 k hfree), ⟨hprev1, rfl, rfl, rfl⟩, hatoms1, hbonds1, hbranches1,
              ?_, hmarked1, by rw [← hnumbers1], ?_⟩
            · show Mirrors noted ((k, c) :: W)
                ((k, ⟨i, s1.pending.map (·.1), position, s1.numbersAtAtom, s1.mark⟩) :: s1.rings)
              rw [hpend1, hrings1, ← hca]
              exact hrel.add k c none position _ _ (hmarked c List.mem_cons_self up hm)
            · refine hn.add (mark := some (up, markAt)) (atom := i)
                (order := s1.pending.map (·.1)) (position := position) hringBonds1
                hdirections1 ?_ (by rw [hm]; rfl)
              show (k, (⟨i, s1.pending.map (·.1), position, s1.numbersAtAtom, s1.mark⟩ : OpenRing))
                :: s1.rings = _
              rw [hnumbers1, hmark1, hrings1, hplace]
        | none =>
          rcases hsym c List.mem_cons_self hm with ⟨hwritten, hok⟩ | ⟨homitted, hok⟩
          · -- the bond symbol, then the ring number
            simp only [hwritten]
            show Reads s (Token.bond (.order c.order) :: Token.ring k :: tokens') _
            refine Reads.cons (Q := fun s1 => s1.atoms = s.atoms ∧ s1.bonds = s.bonds ∧
                s1.rings = s.rings ∧ s1.previous = some i ∧ s1.branches = s.branches ∧
                (∃ symbolAt, s1.pending = some (c.order, symbolAt)) ∧
                s1.last = .bondAfterAtom ∧ s1.mark = none ∧ s1.numbersAtAtom = s.numbersAtAtom ∧
                s1.ringBonds = s.ringBonds ∧
                s1.directions = s.directions ∧ s1.marked = s.marked) ?_ ?_
            · intro position
              exact ⟨_, step_order_eq c.order position hat.last, rfl, rfl, rfl, hat.previous, rfl,
                ⟨position, rfl⟩, rfl, hat.mark, rfl, rfl, rfl, rfl⟩
            · intro s1 ⟨hatoms1, hbonds1, hrings1, hprev1, hbranches1, ⟨symbolAt, hpend1⟩, hlast1,
                hmark1, hnumbers1, hringBonds1, hdirections1, hmarked1⟩
              refine Reads.cons ?_ hafter
              intro position
              refine ⟨_, step_ringOpen_eq position hprev1 (Or.inr hlast1)
                (hrings1 ▸ hrel.1 k hfree), ⟨hprev1, rfl, rfl, rfl⟩, hatoms1, hbonds1,
                hbranches1, ?_, hmarked1, by rw [← hnumbers1], ?_⟩
              · show Mirrors noted ((k, c) :: W)
                  ((k, ⟨i, s1.pending.map (·.1), position, s1.numbersAtAtom, s1.mark⟩) :: s1.rings)
                rw [hpend1, hrings1, ← hca]
                exact hrel.add k c (some c.order) position _ _ hok
              · refine hn.add (mark := none) (atom := i) (order := s1.pending.map (·.1))
                  (position := position) hringBonds1 hdirections1 ?_ (by rw [hm]; rfl)
                show (k, (⟨i, s1.pending.map (·.1), position, s1.numbersAtAtom, s1.mark⟩ :
                    OpenRing)) :: s1.rings = _
                rw [hnumbers1, hmark1, hrings1, hplace]
          · -- the ring number alone
            simp only [homitted]
            show Reads s (Token.ring k :: tokens') _
            refine Reads.cons ?_ hafter
            intro position
            refine ⟨_, step_ringOpen_eq position hat.previous (Or.inl hat.last) (hrel.1 k hfree),
              ⟨hat.previous, rfl, rfl, rfl⟩, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
            · show Mirrors noted ((k, c) :: W)
                ((k, ⟨i, s.pending.map (·.1), position, s.numbersAtAtom, s.mark⟩) :: s.rings)
              rw [hat.pending, ← hca]
              exact hrel.add k c none position _ _ hok
            · refine hn.add (mark := none) (atom := i) (order := s.pending.map (·.1))
                (position := position) rfl rfl ?_ (by rw [hm]; rfl)
              show (k, (⟨i, s.pending.map (·.1), position, s.numbersAtAtom, s.mark⟩ : OpenRing))
                :: s.rings = _
              rw [hat.mark, hplace]

end VeriMol
