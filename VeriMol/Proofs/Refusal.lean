import VeriMol.Core.Run
import VeriMol.Proofs.Read

/-!
# A `Mol` that the reader returns has no atom that the writer refuses

Theorems 10 and 18 of CLAIMS.md.

For a `Mol` without stereo facts the writer refuses for four reasons (SPEC.md,
section 9.4): it is not well formed; an atom has more than 9 hydrogens or a
charge beyond +99 or -99; a hydrogen atom has hydrogens of its own; more than
99 ring numbers are needed. A `Mol` that the reader returned is well formed
(theorem 8). This file shows that it has no atom of the two kinds in the
middle (`read_no_refusal`, theorem 10). So for a text that was read as a `Mol`
without stereo facts, `rewrite` and `plain` can refuse with one message only,
the one about ring numbers (`run_rewrite_of_read`, theorem 18). When this
message comes is theorem 19 (`VeriMol/Proofs/RingNumbers.lean`): in both
spellings, exactly when more than 99 ring numbers are open behind some atom.

The proof follows the text: every atom that `cut` finds is within the limits,
because `cut` takes at most one digit for the hydrogens, refuses a hydrogen
count at a hydrogen atom, and takes at most two digits for the charge; the
reader keeps the atoms as they are written; and the hydrogens that it works
out for an atom without square brackets are at most 6.
-/

namespace VeriMol

/-- An atom, as it is written, within the limits of the writer: at most 9
hydrogens, none at a hydrogen atom, and a charge from -99 to +99. The lemmas
below call such an atom fine. -/
structure WrittenAtom.WithinLimits (w : WrittenAtom) : Prop where
  hydrogens : ∀ h, w.hydrogens = some h → h ≤ 9 ∧ (w.element = .H → h = 0)
  charge : w.charge.natAbs ≤ 99

theorem fine_bare (e : Element) (a : Bool) : WrittenAtom.WithinLimits (.bare e a) :=
  ⟨by intro n hn; simp [WrittenAtom.bare] at hn, by simp [WrittenAtom.bare]⟩

/-! ## The characters -/

theorem digitValue_le {c : Char} (h : c.isDigit = true) : digitValue c ≤ 9 := by
  unfold Char.isDigit at h
  unfold digitValue
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h
  have h2 : c.val.toNat ≤ 57 := h.2
  show c.val.toNat - 48 ≤ 9
  omega

theorem readUpToTwoDigits_le (text : List Char) (n : Nat)
    (hn : (readUpToTwoDigits text).1 = some n) : n ≤ 99 := by
  unfold readUpToTwoDigits at hn
  split at hn
  · split at hn
    · rename_i hd
      simp only [Option.some.injEq] at hn
      have h1 := digitValue_le hd.1
      have h2 := digitValue_le hd.2
      omega
    · split at hn
      · rename_i hd
        simp only [Option.some.injEq] at hn
        have h1 := digitValue_le hd
        omega
      · simp at hn
  · split at hn
    · rename_i hd
      simp only [Option.some.injEq] at hn
      have h1 := digitValue_le hd
      omega
    · simp at hn
  · simp at hn

theorem readCharge_le (text : List Char) : (readCharge text).1.natAbs ≤ 99 := by
  unfold readCharge
  split
  · show (2 : Int).natAbs ≤ 99
    decide
  · show (-2 : Int).natAbs ≤ 99
    decide
  · rename_i rest _
    cases h : (readUpToTwoDigits rest).1 with
    | none => simp
    | some n =>
      have := readUpToTwoDigits_le rest n h
      simp
      omega
  · rename_i rest _
    cases h : (readUpToTwoDigits rest).1 with
    | none => simp
    | some n =>
      have := readUpToTwoDigits_le rest n h
      simp
      omega
  · simp

theorem readHydrogens_fine {element : Element} {text rest : List Char} {n : Nat}
    (hr : readHydrogens element text = some (n, rest)) : n ≤ 9 ∧ (element = .H → n = 0) := by
  unfold readHydrogens at hr
  split at hr
  · split at hr
    · cases hr
    · rename_i hne
      split at hr
      · split at hr
        · rename_i hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, _⟩ := hr
          exact ⟨digitValue_le hd, fun he => absurd he hne⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, _⟩ := hr
          exact ⟨by omega, fun he => absurd he hne⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, _⟩ := hr
        exact ⟨by omega, fun he => absurd he hne⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, _⟩ := hr
    exact ⟨by omega, fun _ => rfl⟩

theorem readCountAndCharge_fine {element : Element} {text : List Char} {n : Nat} {c : Int}
    (hr : readCountAndCharge element text = .ok (n, c)) :
    (n ≤ 9 ∧ (element = .H → n = 0)) ∧ c.natAbs ≤ 99 := by
  unfold readCountAndCharge at hr
  split at hr
  · cases hr
  · rename_i hydrogens afterHydrogens hh
    split at hr
    · rename_i charge hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨readHydrogens_fine hh, ?_⟩
      have := readCharge_le afterHydrogens
      rw [hc] at this
      exact this
    · cases hr

theorem bracketAtom_fine {start : Nat} {inside : List Char} {w : WrittenAtom} {p : Nat}
    (h : bracketAtom start inside = .ok (w, p)) : WrittenAtom.WithinLimits w := by
  unfold bracketAtom at h
  dsimp only at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine ⟨?_, ?_⟩
    · intro n hn
      simp only [Option.some.injEq] at hn
      subst hn
      exact (readCountAndCharge_fine (by assumption)).1
    · exact (readCountAndCharge_fine (by assumption)).2

theorem oneCharacter_fine {c : Char} {w : WrittenAtom} (h : oneCharacter c = some (.atom w)) :
    WrittenAtom.WithinLimits w := by
  unfold oneCharacter at h
  split at h
  all_goals first
    | (simp only [Option.some.injEq, Token.atom.injEq] at h; subst h; exact fine_bare _ _)
    | (simp at h; done)
    | (split at h <;> simp at h)

theorem firstToken_fine {start : Nat} {c : Char} {rest : List Char} {placed : Placed} {n : Nat}
    {w : WrittenAtom} (h : firstToken start c rest = .ok (placed, n))
    (hw : placed.token = .atom w) : WrittenAtom.WithinLimits w := by
  unfold firstToken at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i atom position hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [Token.atom.injEq] at hw
        subst hw
        exact bracketAtom_fine hb
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [Token.atom.injEq] at hw
      subst hw
      exact fine_bare _ _
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [Token.atom.injEq] at hw
        subst hw
        exact fine_bare _ _
      · split at h
        · repeat' split at h
          all_goals first | (cases h; done) | skip
          all_goals
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            simp at hw
        · split at h
          · rename_i token ho
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            simp only at hw
            subst hw
            exact oneCharacter_fine ho
          · cases h

theorem cutFrom_fine : ∀ (text : List Char) (position skip : Nat) (placed : Placed)
    (w : WrittenAtom), placed ∈ (cutFrom position skip text).tokens → placed.token = .atom w →
    WrittenAtom.WithinLimits w := by
  intro text
  induction text with
  | nil =>
    intro position skip placed w hm
    simp [cutFrom] at hm
  | cons c rest ih =>
    intro position skip placed w hm hw
    unfold cutFrom at hm
    split at hm
    · exact ih _ _ placed w hm hw
    · split at hm
      · simp at hm
      · rename_i token length hf
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact firstToken_fine hf hw
        · exact ih _ _ placed w hm hw

/-! ## The reader -/

/-- The reader keeps the atoms as they are written (`steps_atoms`), so every
atom that it holds is within the limits if every atom among the tokens is. -/
theorem steps_fine {tokens : List Placed} {reading next : Reading}
    (h : ∀ w ∈ reading.atoms, WrittenAtom.WithinLimits w)
    (ht : ∀ placed ∈ tokens, ∀ w, placed.token = .atom w → WrittenAtom.WithinLimits w)
    (hs : steps reading tokens = .ok next) : ∀ w ∈ next.atoms, WrittenAtom.WithinLimits w := by
  intro w hw
  rw [steps_atoms hs] at hw
  rcases List.mem_append.mp hw with hin | hin
  · exact h w hin
  · obtain ⟨placed, hp, hatom⟩ := List.mem_filterMap.mp hin
    apply ht placed hp w
    unfold atomOf at hatom
    split at hatom
    · rename_i written htoken
      cases hatom
      exact htoken
    · cases hatom

/-! ## The end of the text -/

theorem bareHydrogens_le (e : Element) (a : Bool) (sum : Nat) : bareHydrogens e a sum ≤ 6 := by
  unfold bareHydrogens
  split
  · omega
  · rename_i valence hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hv : valence ≤ 6 := by
      cases e <;> simp [Element.valences] at hmem <;> omega
    split <;> omega

theorem toAtom_refusal {w : WrittenAtom} (h : WrittenAtom.WithinLimits w) (sum : Nat) :
    (w.toAtom sum).refusal = none := by
  have hh : (w.toAtom sum).hydrogens ≤ 9 ∧ (w.element = .H → (w.toAtom sum).hydrogens = 0) := by
    unfold WrittenAtom.toAtom
    cases hw : w.hydrogens with
    | some n => exact h.hydrogens n hw
    | none =>
      refine ⟨?_, ?_⟩
      · have := bareHydrogens_le w.element w.aromatic sum
        show bareHydrogens w.element w.aromatic sum ≤ 9
        omega
      · intro he
        show bareHydrogens w.element w.aromatic sum = 0
        simp [he, bareHydrogens, Element.valences]
  have h1 : ¬ (9 < (w.toAtom sum).hydrogens ∨ 99 < (w.toAtom sum).charge.natAbs) := by
    intro hor
    rcases hor with h9 | h99
    · omega
    · have hc := h.charge
      have : (w.toAtom sum).charge = w.charge := rfl
      rw [this] at h99
      omega
  have h2 : ¬ ((w.toAtom sum).element = .H ∧ 0 < (w.toAtom sum).hydrogens) := by
    intro ⟨he, hpos⟩
    have := hh.2 he
    omega
  simp only [Atom.refusal, h1, h2, ↓reduceIte]

theorem finishAtoms_fine (bonds : List Bond) : ∀ (number : Nat) (atoms : List WrittenAtom),
    (∀ w ∈ atoms, WrittenAtom.WithinLimits w) →
      ∀ a ∈ finishAtoms bonds number atoms, a.refusal = none := by
  intro number atoms
  induction atoms generalizing number with
  | nil =>
    intro _ a ha
    simp [finishAtoms] at ha
  | cons written rest ih =>
    intro h a ha
    simp only [finishAtoms, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact toAtom_refusal (h written (by simp)) _
    · exact ih (number + 1) (fun w hw => h w (by simp [hw])) a ha

/-- Theorem 10 of CLAIMS.md. A `Mol` that the reader returns has no atom that
the writer refuses. -/
theorem read_no_refusal (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    ∀ a ∈ mol.atoms, a.refusal = none := by
  unfold VeriMol.read readCut at h
  split at h
  · cases h
  · rename_i reading hsteps
    split at h
    · cases h
    · have hfine := steps_fine (tokens := (cut text).tokens)
        (by intro w hw; simp [Reading.start] at hw)
        (fun placed hp w hw => cutFrom_fine text 0 0 placed w hp hw) hsteps
      unfold finish withStereo at h
      repeat' split at h
      all_goals first | (cases h; done) | skip
      cases h
      exact finishAtoms_fine _ 0 _ hfine

/-! ## So a text that was read is written back, or refused for ring numbers only

This is about a `Mol` without stereo facts. For a `Mol` with stereo facts the
writer has more reasons to refuse (SPEC.md, section 12.3), and no theorem says
which of them can come for a text that was read. -/

/-- A `Mol` without orientations has none at any atom. -/
theorem Mol.orientationAt_of_none {mol : Mol} (h : mol.orientations = []) (number : Nat) :
    mol.orientationAt number = none := by
  simp [Mol.orientationAt, h]

/-- A `Mol` without geometries gets no mark at any bond. -/
theorem chooseMarks_of_no_geometries {mol : Mol} (h : mol.geometries = []) :
    chooseMarks mol = .ok [] := by
  have hnone : mol.bonds.filterMap (fun _ => (none : Option (Nat × Nat))) = [] :=
    List.filterMap_eq_nil_iff.2 fun _ _ => rfl
  unfold chooseMarks
  simp [h, wouldGetGeometry, hnone, markGroups]

/-- What a spelling writes for an atom of a `Mol` without orientations, and for
the atoms behind it: what stands in front of the atom, the atom, the ring
numbers that close and those that open. Only the ring numbers can fail. -/
theorem tokensFrom_cons {mol : Mol} (h : mol.orientations = []) (spelling : Spelling)
    (marks : Marks) (parents : List (Option Nat)) (i : Nat) (atom : Atom)
    (parent : Option Nat) (rest : List (Atom × Option Nat)) (W : List (Nat × Bond)) :
    tokensFrom spelling mol marks parents i ((atom, parent) :: rest) W =
      match closeRings W (mol.bonds.filter fun bond => bond.b == i && ringBond parents bond) with
      | none => .error Message.tooManyRingNumbers
      | some (closing, afterClosing) =>
        match openRings (markedSymbol marks (spelling.symbol mol)) afterClosing
            (mol.bonds.filter fun bond => bond.a == i && ringBond parents bond) with
        | none => .error Message.tooManyRingNumbers
        | some (opening, afterOpening) =>
          match tokensFrom spelling mol marks parents (i + 1) rest afterOpening with
          | .error message => .error message
          | .ok behind =>
            .ok (beforeAtom spelling mol marks i parent (rest.map (·.2))
              ++ spelling.atom mol.bonds i atom :: closing ++ opening ++ behind) := by
  simp only [tokensFrom, Mol.orientationAt_of_none h]
  rfl

/-- For a `Mol` without orientations a spelling makes its tokens, or it
answers with the message about ring numbers, and with no other. -/
theorem tokensFrom_of_noOrientations {mol : Mol} (h : mol.orientations = [])
    (spelling : Spelling) (marks : Marks) (parents : List (Option Nat)) :
    ∀ (atoms : List (Atom × Option Nat)) (i : Nat) (W : List (Nat × Bond)),
      (∃ tokens, tokensFrom spelling mol marks parents i atoms W = .ok tokens) ∨
        tokensFrom spelling mol marks parents i atoms W = .error Message.tooManyRingNumbers
  | [], _, _ => .inl ⟨[], rfl⟩
  | (atom, parent) :: rest, i, W => by
    rw [tokensFrom_cons h]
    split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · rename_i afterOpening _
        rcases tokensFrom_of_noOrientations h spelling marks parents rest (i + 1) afterOpening
          with ⟨tokens, ht⟩ | ht
        · rw [ht]
          exact .inl ⟨_, rfl⟩
        · rw [ht]
          exact .inr rfl

/-- A well formed `Mol` without stereo facts whose atoms can all be written
gets a text from a spelling, or the message about ring numbers, and no
other. -/
theorem Spelling.write_of_fine (spelling : Spelling) {mol : Mol} (hw : mol.WellFormed)
    (hr : ∀ a ∈ mol.atoms, a.refusal = none)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ written, spelling.write mol = .ok written) ∨
      spelling.write mol = .error Message.tooManyRingNumbers := by
  have hnone : mol.atoms.findSome? Atom.refusal = none := List.findSome?_eq_none_iff.2 hr
  unfold Spelling.write
  simp only [hw, not_true_eq_false, ↓reduceIte, hnone, chooseMarks_of_no_geometries hgeometries]
  rcases tokensFrom_of_noOrientations horientations spelling [] (spelling.parents mol)
      (mol.atoms.zip (spelling.parents mol)) 0 [] with ⟨ts, ht⟩ | ht
  · rw [Spelling.tokens, ht]
    simp only
    split
    · exact .inl ⟨_, rfl⟩
    · exact .inr rfl
  · rw [Spelling.tokens, ht]
    exact .inr rfl

/-- Theorem 18 of CLAIMS.md, for the two spellings: a `Mol` without stereo
facts that the reader returned is written, or refused with the message about
ring numbers, and with no other message. -/
theorem Spelling.write_of_read (spelling : Spelling) (text : List Char) (mol : Mol)
    (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ written, spelling.write mol = .ok written) ∨
      spelling.write mol = .error Message.tooManyRingNumbers :=
  spelling.write_of_fine (read_wellFormed text mol h) (read_no_refusal text mol h) horientations
    hgeometries

/-- Theorem 18 of CLAIMS.md. For a text that is read as a `Mol` without stereo
facts, the commands `rewrite` and `plain` print a text, or the error about ring
numbers, and nothing else (SPEC.md, section 9.4). -/
theorem run_rewrite_of_read (word text : List Char) (mol : Mol)
    (hword : word = "rewrite".toList ∨ word = "plain".toList) (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ written, run [word, text] = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) ∨
      run [word, text] =
        { stdout := [],
          stderr := "error: more than 99 ring numbers are needed at the same time\n".toList,
          exitCode := 1 } := by
  have hmessage : Output.error Message.tooManyRingNumbers =
      { stdout := [],
        stderr := "error: more than 99 ring numbers are needed at the same time\n".toList,
        exitCode := 1 } := by
    rfl
  rcases hword with rfl | rfl
  · rcases Spelling.brackets.write_of_read text mol h horientations hgeometries
      with ⟨written, hw⟩ | he
    · left
      exact ⟨written, by simp [run, rewritten, write, h, hw, Output.ok]⟩
    · right
      rw [← hmessage]
      simp [run, rewritten, write, h, he]
  · rcases Spelling.plain.write_of_read text mol h horientations hgeometries
      with ⟨written, hw⟩ | he
    · left
      exact ⟨written, by simp [run, rewritten, writePlain, h, hw, Output.ok]⟩
    · right
      rw [← hmessage]
      simp [run, rewritten, writePlain, h, he]

end VeriMol
