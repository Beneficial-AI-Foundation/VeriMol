import VeriMol.Core
import VeriMol.Proofs.ReadMarks

/-!
# A `Mol` that the reader returns is well formed

This file proves theorem 8 of CLAIMS.md: `read_wellFormed`. Behind it come
theorem 9 (`read_atoms`: the atoms of the `Mol` are the atoms among the
tokens of the text), a fact about the inside of the reader
(`steps_previous`), and single examples of what the reader gives: theorems
36 to 38, and the first statement of theorem 39.

The way to theorem 8:

1. Putting a bond at its place in a list that is in order keeps the list in
   order, as long as its two atoms are not bonded yet (`insertBond_ordered`).
2. `Reading.Valid` says what is true of the reader's state after every token:
   the bonds are in order, each joins two different atoms that exist, and
   the atoms that the reader holds for the tokens to come exist: `previous`,
   the atom of every open ring number, and the atom in front of every open
   round bracket.
3. It is true at the start (`Reading.start_valid`), and every token keeps it
   true (`step_valid`).
4. At the end of the text it is what "well formed" asks of the atoms and the
   bonds, and the two lists of stereo facts are made as "well formed" asks
   (`stereoFacts_wellFormed` in `VeriMol/Proofs/ReadMarks.lean`;
   `finish_wellFormed`).
-/

namespace VeriMol

/-! ## Bonds in order -/

theorem mem_insertBond (new x : Bond) (bonds : List Bond) :
    x ∈ insertBond new bonds ↔ x = new ∨ x ∈ bonds := by
  induction bonds with
  | nil => simp [insertBond]
  | cons bond rest ih =>
    by_cases hb : new.before bond
    · simp [insertBond, hb]
    · simp [insertBond, hb, ih]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- Putting a bond between two atoms that are not bonded yet keeps the list in
order. -/
theorem insertBond_ordered {bonds : List Bond} (h : bonds.Pairwise Bond.before) (new : Bond)
    (hnew : ∀ bond ∈ bonds, ¬(bond.a = new.a ∧ bond.b = new.b)) :
    (insertBond new bonds).Pairwise Bond.before := by
  induction bonds with
  | nil => simp [insertBond]
  | cons bond rest ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hbond, hrest⟩ := h
    by_cases hb : new.before bond
    · have hinsert : insertBond new (bond :: rest) = new :: bond :: rest := by
        simp [insertBond, hb]
      rw [hinsert, List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hbond, hrest⟩⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hb
      · have hbx := hbond x h
        unfold Bond.before at *
        omega
    · have hinsert : insertBond new (bond :: rest) = bond :: insertBond new rest := by
        simp [insertBond, hb]
      rw [hinsert, List.pairwise_cons]
      refine ⟨?_, ih hrest (fun x hx => hnew x (List.mem_cons_of_mem _ hx))⟩
      intro x hx
      rcases (mem_insertBond new x rest).mp hx with h | h
      · have hkey := hnew bond List.mem_cons_self
        rw [h]
        unfold Bond.before at *
        omega
      · exact hbond x h

/-! ## Ring numbers -/

/-- A number that is looked up and found stands in the table, with what was found. -/
theorem mem_of_ringAt {α : Type} {number : Nat} {rings : List (Nat × α)} {ring : α}
    (h : ringAt number rings = some ring) : (number, ring) ∈ rings := by
  induction rings with
  | nil => simp [ringAt] at h
  | cons entry rest ih =>
    obtain ⟨other, opened⟩ := entry
    unfold ringAt at h
    split at h
    · rename_i hother
      cases h
      simp [hother]
    · exact List.mem_cons_of_mem _ (ih h)

/-! ## What stays true while reading -/

/-- What is true of the reader's state after every token. -/
structure Reading.Valid (reading : Reading) : Prop where
  /-- every bond joins two different atoms that exist -/
  inRange : ∀ bond ∈ reading.bonds, bond.a < bond.b ∧ bond.b < reading.atoms.length
  /-- the bonds are in order -/
  ordered : reading.bonds.Pairwise Bond.before
  /-- the atom that the next atom is bonded to exists -/
  previous : ∀ atom, reading.previous = some atom → atom < reading.atoms.length
  /-- the atom of every open ring number exists -/
  rings : ∀ entry ∈ reading.rings, entry.2.atom < reading.atoms.length
  /-- the atom in front of every open round bracket exists -/
  branches : ∀ entry ∈ reading.branches, ∀ atom, entry.1 = some atom →
    atom < reading.atoms.length

theorem Reading.start_valid : Reading.start.Valid := by
  constructor <;> simp [Reading.start]

/-- When a ring number closes without a problem: its two atoms are different
and not bonded yet, and its two ends give one bond order. The bond is put at
its place, the number is taken out of the open rings, `last` is `.atom`, and
no bond symbol and no direction mark is left waiting. The atoms, `previous`
and the open round brackets stay as they were. What the reader notes for the
stereo facts (`numbersAtAtom`, `ringBonds`, `directions`, `marked`) is not
named here. -/
theorem closeRing_ok {reading next : Reading} {number : Nat} {opened : OpenRing}
    {atom position : Nat} (hs : closeRing reading number opened atom position = .ok next) :
    opened.atom ≠ atom ∧ ∃ order,
      ringOrder opened.order (reading.pending.map (·.1))
        (assumedOrder reading.atoms opened.atom atom) = some order ∧
      (∀ bond ∈ reading.bonds, ¬(bond.a = min opened.atom atom ∧ bond.b = max opened.atom atom)) ∧
      next.atoms = reading.atoms ∧
      next.bonds = insertBond ⟨min opened.atom atom, max opened.atom atom, order⟩ reading.bonds ∧
      next.previous = reading.previous ∧ next.pending = none ∧ next.last = .atom ∧
      next.rings = withoutRing number reading.rings ∧ next.branches = reading.branches ∧
      next.mark = none := by
  unfold closeRing at hs
  simp only at hs
  repeat' split at hs
  all_goals first | (cases hs; done) | skip
  all_goals
    have hany : ¬ (reading.bonds.any fun bond =>
        decide (bond.a = min opened.atom atom ∧ bond.b = max opened.atom atom)) = true := by
      assumption
    cases hs
    simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at hany
    exact ⟨by assumption, _, by assumption, fun bond hbond hkey => hany bond hbond hkey.1 hkey.2,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem closeRing_valid {reading next : Reading} {number : Nat} {opened : OpenRing}
    {atom position : Nat} (h : reading.Valid) (hopened : opened.atom < reading.atoms.length)
    (hatom : atom < reading.atoms.length)
    (hs : closeRing reading number opened atom position = .ok next) : next.Valid := by
  obtain ⟨hne, order, -, hnew, hatoms, hbonds, hprevious, -, -, hrings, hbranches, -⟩ :=
    closeRing_ok hs
  constructor
  · intro bond hbond
    rw [hbonds] at hbond
    rw [hatoms]
    rcases (mem_insertBond _ _ _).mp hbond with rfl | hbond
    · simp only; omega
    · exact h.inRange bond hbond
  · rw [hbonds]
    exact insertBond_ordered h.ordered _ (fun bond hbond hkey => hnew bond hbond hkey)
  · rw [hprevious, hatoms]
    exact h.previous
  · intro entry hentry
    rw [hrings] at hentry
    rw [hatoms]
    exact h.rings entry (List.mem_filter.mp hentry).1
  · rw [hbranches, hatoms]
    exact h.branches

theorem step_valid {reading next : Reading} {placed : Placed} (h : reading.Valid)
    (hs : step reading placed = .ok next) : next.Valid := by
  unfold step at hs
  simp only at hs
  split at hs
  · cases hs
  split at hs
  · -- an atom
    cases hs
    constructor
    · intro bond hbond
      simp only [List.length_append, List.length_cons, List.length_nil]
      split at hbond
      · have := h.inRange bond hbond
        omega
      · rename_i previous hprevious
        rcases (mem_insertBond _ _ _).mp hbond with rfl | hbond
        · have := h.previous previous hprevious
          simp only
          omega
        · have := h.inRange bond hbond
          omega
    · simp only
      split
      · exact h.ordered
      · rename_i previous hprevious
        refine insertBond_ordered h.ordered _ (fun bond hbond hkey => ?_)
        have := h.inRange bond hbond
        simp only at hkey
        omega
    · intro atom hatom
      simp only [Option.some.injEq] at hatom
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro entry hentry
      have := h.rings entry hentry
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro entry hentry atom hatom
      have := h.branches entry hentry atom hatom
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · -- a bond symbol, or a direction mark
    split at hs <;> (cases hs; exact ⟨h.inRange, h.ordered, h.previous, h.rings, h.branches⟩)
  · -- a ring number
    split at hs
    · cases hs
    · rename_i atom hprevious
      split at hs
      · cases hs
        refine ⟨h.inRange, h.ordered, h.previous, ?_, h.branches⟩
        intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact h.previous atom hprevious
        · exact h.rings entry hentry
      · rename_i opened hopened
        exact closeRing_valid h (h.rings _ (mem_of_ringAt hopened)) (h.previous atom hprevious) hs
  · -- (
    cases hs
    refine ⟨h.inRange, h.ordered, h.previous, h.rings, ?_⟩
    intro entry hentry atom hatom
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact h.previous atom hatom
    · exact h.branches entry hentry atom hatom
  · -- )
    split at hs
    · cases hs
    · rename_i previous position rest hbranches
      cases hs
      refine ⟨h.inRange, h.ordered, ?_, h.rings, ?_⟩
      · intro atom hatom
        exact h.branches (previous, position) (by simp [hbranches]) atom hatom
      · intro entry hentry
        exact h.branches entry (by simp [hbranches, hentry])
  · -- a dot
    cases hs
    exact ⟨h.inRange, h.ordered, by simp, h.rings, h.branches⟩

theorem steps_valid {tokens : List Placed} : ∀ {reading next : Reading}, reading.Valid →
    steps reading tokens = .ok next → next.Valid := by
  induction tokens with
  | nil =>
    intro reading next h hs
    simp only [steps, Except.ok.injEq] at hs
    exact hs ▸ h
  | cons placed rest ih =>
    intro reading next h hs
    unfold steps at hs
    split at hs
    · cases hs
    · rename_i middle hstep
      exact ih (step_valid h hstep) hs

/-! ## The end of the text -/

theorem finishAtoms_length (bonds : List Bond) (number : Nat) (atoms : List WrittenAtom) :
    (finishAtoms bonds number atoms).length = atoms.length := by
  induction atoms generalizing number with
  | nil => rfl
  | cons written rest ih => simp [finishAtoms, ih]

theorem finish_wellFormed {reading : Reading} {mol : Mol} (h : reading.Valid)
    (hf : finish reading = .ok mol) : mol.WellFormed := by
  unfold finish at hf
  repeat' split at hf
  all_goals first | (cases hf; done) | skip
  unfold withStereo at hf
  split at hf
  · cases hf
  · rename_i facts hfacts
    cases hf
    obtain ⟨h1, h2, h3, h4⟩ := stereoFacts_wellFormed (mol := reading.graph) h.ordered hfacts
    refine ⟨fun bond hbond => ?_, h.ordered, h1, h2, h3, h4⟩
    show bond.a < bond.b ∧ bond.b < (finishAtoms reading.bonds 0 reading.atoms).length
    rw [finishAtoms_length]
    exact h.inRange bond hbond

/-- Theorem 8 of CLAIMS.md: whatever the text, a `Mol` that the reader returns
is well formed. -/
theorem read_wellFormed (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    mol.WellFormed := by
  unfold read readCut at h
  split at h
  · cases h
  · rename_i reading hsteps
    split at h
    · cases h
    · exact finish_wellFormed (steps_valid Reading.start_valid hsteps) h

/-! ## The atoms are the atoms written -/

/-- The atom that a token is, if it is one. The proofs use this name; the
statement of `read_atoms` writes the same `match` out. -/
def atomOf (placed : Placed) : Option WrittenAtom :=
  match placed.token with
  | .atom written => some written
  | _ => none

theorem closeRing_same {reading next : Reading} {number : Nat} {opened : OpenRing}
    {atom position : Nat} (h : closeRing reading number opened atom position = .ok next) :
    next.atoms = reading.atoms ∧ next.previous = reading.previous ∧
      next.branches = reading.branches := by
  obtain ⟨-, -, -, -, hatoms, -, hprevious, -, -, -, hbranches, -⟩ := closeRing_ok h
  exact ⟨hatoms, hprevious, hbranches⟩

theorem step_atoms {reading next : Reading} {placed : Placed}
    (hs : step reading placed = .ok next) :
    next.atoms = reading.atoms ++ (atomOf placed).toList := by
  unfold step at hs
  dsimp only at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i written htoken
      cases hs
      simp [atomOf, htoken]
    · rename_i symbol htoken
      split at hs <;> (cases hs; simp [atomOf, htoken])
    · rename_i number htoken
      split at hs
      · cases hs
      · split at hs
        · cases hs
          simp [atomOf, htoken]
        · rw [(closeRing_same hs).1]
          simp [atomOf, htoken]
    · rename_i htoken
      cases hs
      simp [atomOf, htoken]
    · rename_i htoken
      split at hs
      · cases hs
      · cases hs
        simp [atomOf, htoken]
    · rename_i htoken
      cases hs
      simp [atomOf, htoken]

theorem steps_atoms {tokens : List Placed} : ∀ {reading next : Reading},
    steps reading tokens = .ok next → next.atoms = reading.atoms ++ tokens.filterMap atomOf := by
  induction tokens with
  | nil =>
    intro reading next hs
    simp only [steps, Except.ok.injEq] at hs
    subst hs
    simp
  | cons placed rest ih =>
    intro reading next hs
    unfold steps at hs
    split at hs
    · cases hs
    · rename_i middle hstep
      rw [ih hs, step_atoms hstep]
      cases h : atomOf placed <;> simp [h]

theorem finishAtoms_getElem? (bonds : List Bond) :
    ∀ (atoms : List WrittenAtom) (start number : Nat),
    (finishAtoms bonds start atoms)[number]? =
      (atoms[number]?).map fun written => written.toAtom (bondSum bonds (start + number)) := by
  intro atoms
  induction atoms with
  | nil => intro start number; simp [finishAtoms]
  | cons written rest ih =>
    intro start number
    cases number with
    | zero => simp [finishAtoms]
    | succ n =>
      simp only [finishAtoms, List.getElem?_cons_succ]
      rw [ih (start + 1) n]
      have : start + 1 + n = start + (n + 1) := by omega
      rw [this]

/-- Theorem 9 of CLAIMS.md. The atoms of the `Mol` are the atoms among the
tokens into which `cut` cuts the text, in the order of the text. Element,
isotope and charge are those of the token. So are the hydrogens of an atom in
square brackets. The hydrogens of an atom without square brackets are what
`bareHydrogens` gives for the sum of the bonds of the `Mol` at that atom
(`bondSum`) and for whether its symbol is written in lowercase; the two are
the program's functions for rule 7 of SPEC.md, section 5.

The theorem takes `cut`, the bonds of the `Mol`, `bondSum` and `bareHydrogens`
as they are. It does not say which characters make a token, which bonds the
`Mol` has, or that the two functions follow rule 7. -/
theorem read_atoms (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    mol.atoms =
      ((cut text).tokens.filterMap fun placed =>
        match placed.token with
        | .atom written => some written
        | _ => none).mapIdx fun number written =>
          { element := written.element
            isotope := written.isotope
            charge := written.charge
            hydrogens :=
              match written.hydrogens with
              | some hydrogens => hydrogens
              | none =>
                bareHydrogens written.element written.aromatic (bondSum mol.bonds number) } := by
  unfold VeriMol.read readCut at h
  split at h
  · cases h
  · rename_i reading hsteps
    split at h
    · cases h
    · have hatoms : reading.atoms = (cut text).tokens.filterMap atomOf := by
        have := steps_atoms hsteps
        simp only [Reading.start, List.nil_append] at this
        exact this
      unfold finish at h
      repeat' split at h
      all_goals first | (cases h; done) | skip
      unfold withStereo at h
      split at h
      · cases h
      cases h
      show finishAtoms reading.bonds 0 reading.atoms
        = ((cut text).tokens.filterMap atomOf).mapIdx fun number written =>
          written.toAtom (bondSum reading.bonds number)
      rw [← hatoms]
      apply List.ext_getElem?
      intro number
      have hget := finishAtoms_getElem? reading.bonds reading.atoms 0 number
      simp only [Nat.zero_add] at hget
      rw [hget, List.getElem?_mapIdx]

/-! ## The reader always knows the atom the text goes on from -/

/-- What the reader knows between two tokens: the atom that the text goes on
from, except at the start and behind a dot; and for every open branch, the
atom at which it was opened. -/
structure Reading.KnowsPrevious (reading : Reading) : Prop where
  previous : reading.last = .nothing ∨ (∃ position, reading.last = .dot position) ∨
    reading.previous.isSome
  branches : ∀ entry ∈ reading.branches, entry.1.isSome

theorem start_knows : Reading.KnowsPrevious Reading.start :=
  ⟨Or.inl rfl, by intro entry hentry; simp [Reading.start] at hentry⟩

theorem previous_of_allows {reading : Reading} (h : Reading.KnowsPrevious reading) {token : Token}
    (hallow : reading.last.allows token = true) (hnot : ∀ w, token ≠ .atom w) :
    reading.previous.isSome := by
  rcases h.previous with hn | ⟨p, hd⟩ | hs
  · rw [hn] at hallow
    cases token with
    | atom w => exact absurd rfl (hnot w)
    | _ => simp [Last.allows] at hallow
  · rw [hd] at hallow
    cases token with
    | atom w => exact absurd rfl (hnot w)
    | _ => simp [Last.allows] at hallow
  · exact hs

theorem step_knows {reading next : Reading} {placed : Placed} (h : Reading.KnowsPrevious reading)
    (hs : step reading placed = .ok next) : Reading.KnowsPrevious next := by
  unfold step at hs
  dsimp only at hs
  split at hs
  · cases hs
  · rename_i hallow
    have hallow' : reading.last.allows placed.token = true := by simpa using hallow
    split at hs
    · cases hs
      exact ⟨Or.inr (Or.inr rfl), h.branches⟩
    · rename_i symbol htoken
      have hp := previous_of_allows h hallow' (by intro w hw; rw [htoken] at hw; cases hw)
      split at hs <;> (cases hs; exact ⟨Or.inr (Or.inr hp), h.branches⟩)
    · rename_i number htoken
      have hp := previous_of_allows h hallow' (by intro w hw; rw [htoken] at hw; cases hw)
      split at hs
      · cases hs
      · split at hs
        · cases hs
          exact ⟨Or.inr (Or.inr hp), h.branches⟩
        · obtain ⟨_, e1, e2⟩ := closeRing_same hs
          exact ⟨Or.inr (Or.inr (e1 ▸ hp)), e2 ▸ h.branches⟩
    · rename_i htoken
      have hp := previous_of_allows h hallow' (by intro w hw; rw [htoken] at hw; cases hw)
      cases hs
      refine ⟨Or.inr (Or.inr hp), ?_⟩
      intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | hentry
      · exact hp
      · exact h.branches entry hentry
    · rename_i htoken
      split at hs
      · cases hs
      · rename_i previous position rest hbranches
        cases hs
        refine ⟨Or.inr (Or.inr ?_), ?_⟩
        · exact h.branches (previous, position) (by simp [hbranches])
        · intro entry hentry
          exact h.branches entry (by simp [hbranches, hentry])
    · cases hs
      exact ⟨Or.inr (Or.inl ⟨_, rfl⟩), h.branches⟩

theorem steps_knows {tokens : List Placed} : ∀ {reading next : Reading},
    Reading.KnowsPrevious reading → steps reading tokens = .ok next →
      Reading.KnowsPrevious next := by
  induction tokens with
  | nil =>
    intro reading next h hs
    simp only [steps, Except.ok.injEq] at hs
    exact hs ▸ h
  | cons placed rest ih =>
    intro reading next h hs
    unfold steps at hs
    split at hs
    · cases hs
    · rename_i middle hstep
      exact ih (step_knows h hstep) hs

/-- While tokens are read, the reader always knows the atom that the text
goes on from, except at the start and behind a dot. So a ring number always
finds the atom it stands at: that is why the place in `step` where it would
find none is marked "cannot happen". And the `Option` in an entry of
`Reading.branches` is never `none`. -/
theorem steps_previous (tokens : List Placed) (reading : Reading)
    (h : steps Reading.start tokens = .ok reading) :
    (reading.last = .nothing ∨ (∃ position, reading.last = .dot position) ∨ reading.previous.isSome)
      ∧ ∀ entry ∈ reading.branches, entry.1.isSome :=
  ⟨(steps_knows start_knows h).previous, (steps_knows start_knows h).branches⟩

/-! ## Single examples

A test says what the program does for one text when it is run. These say the
same as theorems: Lean works the answer out itself while it checks the proof. -/

/-- Theorem 39 of CLAIMS.md, for what the text is read as: reading `CC(=O)O`
gives the `Mol` that SPEC.md, section 7, shows. -/
theorem read_aceticAcid :
    read "CC(=O)O".toList = .ok
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 1, b := 3, order := .single } ] } := by
  rfl

/-! ### Written out by hand

Theorems 36 and 37 of CLAIMS.md. Most of the theorems compare the program with
itself: the reader with the writer. The seven examples of theorem 36 do not,
and neither does `read_aceticAcid` above. The `Mol` of each is written out by
hand from the rules of SPEC.md, section 5, and RDKit and Open Babel read each
text as that `Mol` (`reference/check_spec.py` compares them). Theorem 37
compares two readings. -/

/-- Theorem 36 of CLAIMS.md. `CC` is read as two carbon atoms with three
hydrogens each, joined by a single bond: ethane. Theorem 37 says that `C-C` is
read as `CC` is; this says what that is. -/
theorem read_ethane :
    read "CC".toList = .ok
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
        bonds := [
          { a := 0, b := 1, order := .single } ] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. `=` is a double bond and `#` a triple bond:
acrylonitrile. -/
theorem read_acrylonitrile :
    read "C=CC#N".toList = .ok
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 2 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .N, isotope := none, charge := 0, hydrogens := 0 } ],
        bonds := [
          { a := 0, b := 1, order := .double },
          { a := 1, b := 2, order := .single },
          { a := 2, b := 3, order := .triple } ] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. Lowercase letters and a ring number: benzene. Its
six bonds are aromatic, and every atom has one hydrogen. -/
theorem read_benzene :
    read "c1ccccc1".toList = .ok
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .aromatic },
          { a := 0, b := 5, order := .aromatic },
          { a := 1, b := 2, order := .aromatic },
          { a := 2, b := 3, order := .aromatic },
          { a := 3, b := 4, order := .aromatic },
          { a := 4, b := 5, order := .aromatic } ] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. Charges, and a dot between two pieces: table
salt. -/
theorem read_salt :
    read "[Na+].[Cl-]".toList = .ok
      { atoms := [
          { element := .Na, isotope := none, charge := 1, hydrogens := 0 },
          { element := .Cl, isotope := none, charge := -1, hydrogens := 0 } ],
        bonds := [] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. A mass number, and hydrogens that are atoms of
their own: heavy water. -/
theorem read_heavyWater :
    read "[2H]O[2H]".toList = .ok
      { atoms := [
          { element := .H, isotope := some 2, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .H, isotope := some 2, charge := 0, hydrogens := 0 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .single } ] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. A count of hydrogens and a charge in square
brackets: the ammonium ion. -/
theorem read_ammonium :
    read "[NH4+]".toList = .ok
      { atoms := [
          { element := .N, isotope := none, charge := 1, hydrogens := 4 } ],
        bonds := [] } := by
  rfl

/-- Theorem 36 of CLAIMS.md. `$` is a quadruple bond. -/
theorem read_quadrupleBond :
    read "[Mo]$[Mo]".toList = .ok
      { atoms := [
          { element := .Mo, isotope := none, charge := 0, hydrogens := 0 },
          { element := .Mo, isotope := none, charge := 0, hydrogens := 0 } ],
        bonds := [
          { a := 0, b := 1, order := .quadruple } ] } := by
  rfl

/-- Theorem 37 of CLAIMS.md. Two cases of one rule: in `C-C` the `-` is the
single bond that `CC` has without it, and in `c:1:c:c:c:c:c:1` every `:` is the
aromatic bond that `c1ccccc1` has without it. -/
theorem read_writtenOutSymbols :
    read "C-C".toList = read "CC".toList ∧
    read "c:1:c:c:c:c:c:1".toList = read "c1ccccc1".toList := by
  constructor <;> rfl

/-! ## Single examples with stereo marks

As above, each `Mol` is written out by hand from the rules of SPEC.md, here
from those of section 12, and Lean works out that the reader returns it.
Without such examples, every other theorem of the project could hold for a
reader and a writer that both took clockwise for anticlockwise, or the same
side of a double bond for opposite sides. -/

/-- Theorem 38 of CLAIMS.md, for a stereo mark at an atom: alanine. The text
writes the places of atom 1 in the order nitrogen, hydrogen, atom 2, atom 3,
and `@@` says that seen from the nitrogen the other three follow each other
clockwise. The `Mol` says it for the fixed order: the hydrogen first, then the
atoms 0, 2 and 3. One swap leads from the one order to the other, so the stored
orientation is the other one. -/
theorem read_alanine :
    read "N[C@@H](C)C(=O)O".toList = .ok
      { atoms := [
          { element := .N, isotope := none, charge := 0, hydrogens := 2 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .single },
          { a := 1, b := 3, order := .single },
          { a := 3, b := 4, order := .double },
          { a := 3, b := 5, order := .single } ],
        orientations := [
          { atom := 1, orientation := .anticlockwise } ],
        geometries := [] } := by
  rfl

/-- Theorem 38 of CLAIMS.md, for direction marks: the two fluorine atoms on
opposite sides of the double bond. The first `/` says that atom 1 lies above
atom 0, so atom 0 lies below atom 1; the second says that atom 3 lies above
atom 2. -/
theorem read_transDifluoroethene :
    read "F/C=C/F".toList = .ok
      { atoms := [
          { element := .F, isotope := none, charge := 0, hydrogens := 0 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .F, isotope := none, charge := 0, hydrogens := 0 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 2, b := 3, order := .single } ],
        orientations := [],
        geometries := [
          { a := 1, b := 2, geometry := .oppositeSides } ] } := by
  rfl

/-- Theorem 38 of CLAIMS.md, for direction marks: the two fluorine atoms on the
same side of the double bond. Here `\` says that atom 3 lies below atom 2, as
atom 0 lies below atom 1. -/
theorem read_cisDifluoroethene :
    read "F/C=C\\F".toList = .ok
      { atoms := [
          { element := .F, isotope := none, charge := 0, hydrogens := 0 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .C, isotope := none, charge := 0, hydrogens := 1 },
          { element := .F, isotope := none, charge := 0, hydrogens := 0 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 2, b := 3, order := .single } ],
        orientations := [],
        geometries := [
          { a := 1, b := 2, geometry := .sameSide } ] } := by
  rfl

end VeriMol
