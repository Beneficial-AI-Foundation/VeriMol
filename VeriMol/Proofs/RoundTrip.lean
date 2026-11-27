import VeriMol.Proofs.Brackets
import VeriMol.Proofs.Notes
import VeriMol.Proofs.Spell

/-!
# Reading a written text gives the `Mol` back

This file proves theorems 11 and 12 of CLAIMS.md: if the spelling with round
brackets gives a text for a `Mol`, reading that text returns exactly that
`Mol`, with its stereo facts (`read_write`), and the same for the plain
spelling (`read_writePlain`). Both are cases of one proof, for the one writer
of both spellings (`Spelling.read_write`). So the program returns what it
writes without reading it back (`VeriMol/Core/Write.lean`).

## The idea

The reader follows the writer, atom by atom. Between two atoms, when `i` atoms
are written, these things hold (`WrittenAt`):

1. the reader has read exactly the first `i` atoms, as they were written;
2. its list of bonds is exactly the list of the `Mol`'s bonds among those
   atoms;
3. its table of open ring numbers mirrors the writer's table (`Mirrors`), and
   every entry of the writer's table is a bond of the `Mol` that is open at
   this point, with no bond under two numbers (`TableHolds`);
4. the reader has a branch open for every round bracket that is open in the
   text, and it remembers for each the atom in front of it (the plain
   spelling writes no round bracket, so there none is open);
5. what the reader has noted about stereo marks is exactly what the writer
   wrote so far (`NotesAt`, `MarkedUpTo`);
6. for every atom with an orientation among them, the writer asked whether
   it can be written where it stands, and was not refused (`CentreAsked`).

What is written for one atom keeps these: what stands in front of the atom
and the atom itself, the ring numbers that close, and the ring numbers that
open. At the end of the text no ring number can be open, because an open bond
would end at an atom that does not exist, and no round bracket, because one
is open only where an atom is still to come. The reader's list of bonds is
then the whole list (`AtEnd`), and its notes give the stereo facts back.
That the text is cut into exactly the tokens that were spelled is theorem 7
(`cut_spell`).

A direction mark stands where a bond symbol stands, and the reader gives the
bond the order that it would have without a symbol. A bond with a mark has
that order: the writer marks no other bond (`order_of_marked`).

## Where the parts stand

* `VeriMol/Proofs/Follow.lean`: the bonds in order, reading tokens wherever
  they stand (`Reads`), and the two tables of ring numbers.
* `VeriMol/Proofs/Brackets.lean`: what the spelling with round brackets has
  and the plain one has not: atoms without square brackets, bond symbols that
  are left out, and the path from which its round brackets follow.
* `VeriMol/Proofs/Notes.lean`: the state of the reader after each kind of
  token, and the ring numbers of one atom (`closeRings_notes`,
  `openRings_notes`), with what the reader notes about stereo marks
  (`NotesAt`).
* `VeriMol/Proofs/Facts.lean`: at the end of the text these notes give the
  stereo facts back (`stereoFacts_back`).
-/

namespace VeriMol

/-! ## Atoms with a mark -/

/-- The token of an atom with an orientation: the atom in square brackets,
with its orientation said for the order in which the spelling writes its
places. -/
theorem orientedAtom_eq (mol : Mol) (number : Nat) (atom : Atom) (stored : Orientation)
    (key : Place → Nat × Nat) :
    orientedAtom mol number atom stored key
      = .atom { atom.inBrackets (writtenLowercase mol.bonds number atom) with
          mark := some (stored.turnedIf
            (fallingKeys ((mol.places number).map key) % 2 == 1)) } := rfl

/-- The mark that a spelling writes at an atom, if the atom has an
orientation. `key` says where the spelling writes each place of the atom. -/
def markFor (mol : Mol) (key : Nat → Place → Nat × Nat) (number : Nat) : Option Orientation :=
  (mol.orientationAt number).map fun stored =>
    (stored.turnedIf (fallingKeys ((mol.places number).map (key number)) % 2 == 1))

/-- An atom in square brackets, with the mark that a spelling writes for it. -/
def markedInBrackets (mol : Mol) (key : Nat → Place → Nat × Nat) (number : Nat) (atom : Atom) :
    WrittenAtom :=
  { atom.inBrackets (writtenLowercase mol.bonds number atom) with mark := markFor mol key number }

/-- An atom in square brackets is read as it was written, whatever its mark. -/
theorem toAtom_markedInBrackets (mol : Mol) (key : Nat → Place → Nat × Nat) (number : Nat)
    (atom : Atom) (sum : Nat) : (markedInBrackets mol key number atom).toAtom sum = atom := by
  cases atom
  rfl

/-! ## The order of a bond with a mark -/

/-- A bond with a mark has the order that a missing symbol means: the writer
marks no other bond. -/
theorem order_of_marked {mol : Mol} (w : mol.GraphWellFormed) {marks : Marks}
    (hc : MarksChosen mol marks) {e : Bond} (he : e ∈ mol.bonds) {up : Bool}
    (hup : markAmong marks (e.a, e.b) = some up) :
    e.order = mol.assumedOrder e.a e.b := by
  have hlt := (w.1 e he).1
  have hkey : bondKey e.a e.b = (e.a, e.b) := by
    unfold bondKey
    rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)]
  have hcan := hc.canCarry e.a e.b up (by rw [hkey]; exact hup)
  unfold canCarryMark at hcan
  rw [hkey] at hcan
  simp only at hcan
  obtain ⟨bond, hbond, hp⟩ := List.any_eq_true.1 hcan
  rw [Bool.and_eq_true, Bool.and_eq_true] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have this : bond = e := key_unique w.2 hbond he (eq_of_beq h1) (eq_of_beq h2)
  have h3' := eq_of_beq h3
  rw [this] at h3'
  exact h3'

/-! ## The atoms with a mark that the reader has noted -/

/-- The reader has noted `@` or `@@` for exactly the atoms before atom `i`
that have an orientation, each with the mark that the spelling writes. -/
structure MarkedUpTo (mol : Mol) (key : Nat → Place → Nat × Nat) (i : Nat)
    (marked : List MarkedAtom) : Prop where
  without : ∀ atom, markFor mol key atom = none ∨ i ≤ atom →
    marked.find? (fun found => found.atom == atom) = none
  withOne : ∀ atom mark, atom < i → markFor mol key atom = some mark →
    ∃ position, marked.find? (fun found => found.atom == atom) = some ⟨atom, mark, position⟩

/-- Before the first atom the reader has noted no mark. -/
theorem MarkedUpTo.start (mol : Mol) (key : Nat → Place → Nat × Nat) : MarkedUpTo mol key 0 [] :=
  ⟨fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- One atom more: if the spelling writes a mark at it, the reader notes it. -/
theorem MarkedUpTo.step {mol : Mol} {key : Nat → Place → Nat × Nat} {i : Nat}
    {marked : List MarkedAtom} (h : MarkedUpTo mol key i marked) (written : WrittenAtom)
    (position : Nat) (hmark : written.mark = markFor mol key i) :
    MarkedUpTo mol key (i + 1) (markedWith marked i written position) := by
  unfold markedWith
  cases hm : written.mark with
  | none =>
    simp only
    rw [hm] at hmark
    constructor
    · intro atom hatom
      rcases hatom with hnone | hle
      · exact h.without atom (Or.inl hnone)
      · exact h.without atom (Or.inr (by omega))
    · intro atom mark hlt hsome
      by_cases hai : atom = i
      · subst hai
        rw [← hmark] at hsome
        cases hsome
      · exact h.withOne atom mark (by omega) hsome
  | some found =>
    simp only
    rw [hm] at hmark
    constructor
    · intro atom hatom
      have hne : atom ≠ i := by
        rcases hatom with hnone | hle
        · intro e
          subst e
          rw [← hmark] at hnone
          cases hnone
        · omega
      have hold := h.without atom (by
        rcases hatom with hnone | hle
        · exact Or.inl hnone
        · exact Or.inr (by omega))
      rw [List.find?_append, hold]
      have : (i == atom) = false := by
        have : ¬ i = atom := fun e => hne e.symm
        simpa using this
      simp [this]
    · intro atom mark hlt hsome
      by_cases hai : atom = i
      · subst hai
        rw [← hmark] at hsome
        cases hsome
        refine ⟨position, ?_⟩
        rw [List.find?_append, h.without atom (Or.inr (Nat.le_refl _))]
        simp
      · obtain ⟨position', hfound⟩ := h.withOne atom mark (by omega) hsome
        refine ⟨position', ?_⟩
        rw [List.find?_append, hfound]
        rfl

/-- At the end of the text the reader has noted a mark for exactly the atoms
with an orientation. -/
theorem MarkedUpTo.noted {mol : Mol} (w : mol.WellFormed) {par : Nat → Option Nat}
    {marked : List MarkedAtom} (h : MarkedUpTo mol (parKey par) mol.atoms.length marked) :
    MarkedNoted mol par marked := by
  constructor
  · intro atom hnone
    refine h.without atom (Or.inl ?_)
    unfold markFor
    rw [hnone]
    rfl
  · intro atom stored hsome
    have hlt : atom < mol.atoms.length :=
      Mol.orientation_lt w ((Mol.orientationAt_eq_some w).1 hsome)
    refine h.withOne atom _ hlt ?_
    unfold markFor
    rw [hsome]
    rfl

/-! ## The atoms as a spelling writes them -/

/-- What the proof needs to know about the way a spelling writes its atoms.
`f number atom` is atom `number` as it is written, and `key` says where the
spelling writes each place of an atom. -/
structure WritesAtoms (mol : Mol) (key : Nat → Place → Nat × Nat)
    (f : Nat → Atom → WrittenAtom) : Prop where
  /-- an atom is written in lowercase exactly where the writer says so -/
  aromatic : ∀ number atom, (f number atom).aromatic = writtenLowercase mol.bonds number atom
  /-- reading gives the atom back, once the bonds of the atom are all there -/
  toAtom : ∀ number atom, (f number atom).toAtom (bondSum mol.bonds number) = atom
  /-- the atom carries the mark that the spelling writes for it, or none -/
  mark : ∀ number atom, (f number atom).mark = markFor mol key number

/-- The atoms as a spelling writes them, from atom number `number` on. -/
def writtenWith (f : Nat → Atom → WrittenAtom) : Nat → List Atom → List WrittenAtom
  | _, [] => []
  | number, atom :: rest => f number atom :: writtenWith f (number + 1) rest

/-- The same with one atom more at the end. -/
theorem writtenWith_concat (f : Nat → Atom → WrittenAtom) (number : Nat) (atoms : List Atom)
    (atom : Atom) :
    writtenWith f number (atoms ++ [atom])
      = writtenWith f number atoms ++ [f (number + atoms.length) atom] := by
  induction atoms generalizing number with
  | nil => simp [writtenWith]
  | cons a rest ih =>
    simp only [List.cons_append, writtenWith, ih, List.length_cons]
    have : number + 1 + rest.length = number + (rest.length + 1) := by omega
    rw [this]

/-- Atom number `j` among them. -/
theorem getElem?_writtenWith (f : Nat → Atom → WrittenAtom) (number : Nat) (atoms : List Atom)
    (j : Nat) : (writtenWith f number atoms)[j]? = atoms[j]?.map (f (number + j)) := by
  induction atoms generalizing number j with
  | nil => simp [writtenWith]
  | cons a rest ih =>
    cases j with
    | zero => simp [writtenWith]
    | succ j =>
      simp only [writtenWith, List.getElem?_cons_succ, ih]
      have : number + 1 + j = number + (j + 1) := by omega
      rw [this]

/-- There are as many of them as atoms. -/
theorem writtenWith_length (f : Nat → Atom → WrittenAtom) (number : Nat) (atoms : List Atom) :
    (writtenWith f number atoms).length = atoms.length := by
  induction atoms generalizing number with
  | nil => rfl
  | cons a rest ih => simp [writtenWith, ih]

/-- The atoms written so far, with one atom more. -/
theorem writtenWith_take_succ (f : Nat → Atom → WrittenAtom) (atoms : List Atom) {i : Nat}
    {atom : Atom} (hatom : atoms[i]? = some atom) :
    writtenWith f 0 (atoms.take (i + 1)) = writtenWith f 0 (atoms.take i) ++ [f i atom] := by
  have hi : i < atoms.length := (List.getElem?_eq_some_iff.mp hatom).1
  rw [List.take_add_one, hatom, Option.toList, writtenWith_concat]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

/-- At the end of the text the reader works out the hydrogens, and gets every
atom back. -/
theorem finishAtoms_writtenWith {mol : Mol} {key : Nat → Place → Nat × Nat}
    {f : Nat → Atom → WrittenAtom} (hf : WritesAtoms mol key f) (number : Nat)
    (atoms : List Atom) : finishAtoms mol.bonds number (writtenWith f number atoms) = atoms := by
  induction atoms generalizing number with
  | nil => rfl
  | cons atom rest ih => simp only [writtenWith, finishAtoms, ih, hf.toAtom]

/-- The reader sees an atom as lowercase exactly if the writer writes its
symbol in lowercase. -/
theorem isLowercase_writtenWith {mol : Mol} {key : Nat → Place → Nat × Nat}
    {f : Nat → Atom → WrittenAtom} (hf : WritesAtoms mol key f) {m j : Nat} (hj : j < m) :
    isLowercase (writtenWith f 0 (mol.atoms.take m)) j = lowercaseAt mol j := by
  unfold isLowercase lowercaseAt
  rw [getElem?_writtenWith, List.getElem?_take]
  simp only [hj, ite_true]
  cases mol.atoms[j]? <;> simp [hf.aromatic]

/-- So the reader assumes the same order as the writer did. -/
theorem assumedOrder_writtenWith {mol : Mol} {key : Nat → Place → Nat × Nat}
    {f : Nat → Atom → WrittenAtom} (hf : WritesAtoms mol key f) {m a b : Nat} (ha : a < m)
    (hb : b < m) :
    assumedOrder (writtenWith f 0 (mol.atoms.take m)) a b = mol.assumedOrder a b := by
  unfold assumedOrder Mol.assumedOrder
  rw [isLowercase_writtenWith hf ha, isLowercase_writtenWith hf hb]

/-! ## One atom, with what stands in front of it -/

/-- Two states of the reader that differ only in where the text goes on: the
atoms, the bonds, the open ring numbers and all notes are the same. -/
structure SameNotes (s s' : Reading) : Prop where
  atoms : s'.atoms = s.atoms
  bonds : s'.bonds = s.bonds
  rings : s'.rings = s.rings
  pending : s'.pending = s.pending
  mark : s'.mark = s.mark
  ringBonds : s'.ringBonds = s.ringBonds
  directions : s'.directions = s.directions
  marked : s'.marked = s.marked

/-- A state has the same notes as itself. -/
theorem SameNotes.refl (s : Reading) : SameNotes s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- If `s1` has the notes of `s`, and `s2` those of `s1`, then `s2` has the
notes of `s`. -/
theorem SameNotes.trans {s s1 s2 : Reading} (h : SameNotes s s1) (h2 : SameNotes s1 s2) :
    SameNotes s s2 :=
  ⟨h2.atoms.trans h.atoms, h2.bonds.trans h.bonds, h2.rings.trans h.rings,
    h2.pending.trans h.pending, h2.mark.trans h.mark,
    h2.ringBonds.trans h.ringBonds, h2.directions.trans h.directions,
    h2.marked.trans h.marked⟩

/-- The notes of the reader are the same notes in such a state. -/
theorem SameNotes.notesAt {s s' : Reading} (h : SameNotes s s') {l : List Bond}
    {ring : Bond → Bool} {marks : Marks} {p : Bond → Bool}
    {W : List (Nat × Bond)} (hn : NotesAt l ring marks p W s) : NotesAt l ring marks p W s' :=
  hn.congr (fun _ _ => rfl) h.ringBonds h.directions h.rings

/-- An atom with nothing in front of it that bonds it: the first atom, or an
atom behind a dot. The reader notes its mark, if it has one. -/
theorem alone_notes {mol : Mol} {key : Nat → Place → Nat × Nat} {f : Nat → Atom → WrittenAtom}
    (hf : WritesAtoms mol key f) {ring : Bond → Bool} {marks : Marks}
    {p : Bond → Bool} {W : List (Nat × Bond)} {i : Nat} {atom : Atom} {s : Reading}
    (hatom : mol.atoms[i]? = some atom)
    (hatoms : s.atoms = writtenWith f 0 (mol.atoms.take i)) (hprev : s.previous = none)
    (hn : NotesAt mol.bonds ring marks p W s) (hm : MarkedUpTo mol key i s.marked) :
    Reads s [Token.atom (f i atom)] (fun s' =>
      AtAtom i s' ∧ s'.atoms = writtenWith f 0 (mol.atoms.take (i + 1)) ∧ s'.rings = s.rings ∧
      s'.bonds = s.bonds ∧ s'.branches = s.branches ∧ s'.numbersAtAtom = 0 ∧
      NotesAt mol.bonds ring marks p W s' ∧ MarkedUpTo mol key (i + 1) s'.marked) := by
  have hi : i < mol.atoms.length := (List.getElem?_eq_some_iff.mp hatom).1
  have hlen : s.atoms.length = i := by
    rw [hatoms, writtenWith_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  refine Reads.single ?_
  intro position
  refine ⟨_, step_atom_alone_eq (f i atom) position hprev, ⟨?_, rfl, rfl, rfl⟩, ?_, rfl, rfl,
    rfl, rfl, hn.congr (fun _ _ => rfl) rfl rfl rfl, ?_⟩
  · show some s.atoms.length = some i
    rw [hlen]
  · show s.atoms ++ [f i atom] = _
    rw [writtenWith_take_succ f mol.atoms hatom, hatoms]
  · show MarkedUpTo mol key (i + 1) (markedWith s.marked s.atoms.length (f i atom) position)
    rw [hlen]
    exact hm.step (f i atom) position (hf.mark i atom)

/-- The mark or the bond symbol, if one is written, and the atom. The reader
gets the bond to the atom that this one is written next to, with its order,
and notes the direction mark and the mark of the atom. `symbol` is what the
spelling writes for a bond without a mark: its symbol, or nothing where the
bond has the order that a reader assumes. -/
theorem symbol_atom_notes {mol : Mol} (w : mol.GraphWellFormed)
    {key : Nat → Place → Nat × Nat} {f : Nat → Atom → WrittenAtom} (hf : WritesAtoms mol key f)
    {ring : Bond → Bool} {marks : Marks} (hc : MarksChosen mol marks)
    {symbol : Bond → List Token} {p : Bond → Bool} {W : List (Nat × Bond)} {i q : Nat}
    {bond : Bond} {atom : Atom} {s : Reading}
    (hmem : bond ∈ mol.bonds) (hbond : bond.a = q ∧ bond.b = i) (hq : q < i)
    (hsymbol : symbol bond = [Token.bond (.order bond.order)] ∨
      (symbol bond = [] ∧ bond.order = mol.assumedOrder bond.a bond.b))
    (hring : ring bond = false) (hatom : mol.atoms[i]? = some atom)
    (hatoms : s.atoms = writtenWith f 0 (mol.atoms.take i))
    (hprev : s.previous = some q) (hpend : s.pending = none) (hmark : s.mark = none)
    (hlast : s.last = .atom ∨ s.last = .branchOpen ∨ s.last = .branchClose)
    (hn : NotesAt mol.bonds ring marks p W s) (hm : MarkedUpTo mol key i s.marked) :
    Reads s (markedSymbol marks symbol bond ++ [Token.atom (f i atom)]) (fun s' =>
      AtAtom i s' ∧ s'.atoms = writtenWith f 0 (mol.atoms.take (i + 1)) ∧ s'.rings = s.rings ∧
      s'.bonds = insertBond bond s.bonds ∧ s'.branches = s.branches ∧ s'.numbersAtAtom = 0 ∧
      NotesAt mol.bonds ring marks (fun x => p x || x == bond) W s' ∧
      MarkedUpTo mol key (i + 1) s'.marked) := by
  have hi : i < mol.atoms.length := (List.getElem?_eq_some_iff.mp hatom).1
  have hlen : s.atoms.length = i := by
    rw [hatoms, writtenWith_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hnext : s.atoms ++ [f i atom] = writtenWith f 0 (mol.atoms.take (i + 1)) := by
    rw [writtenWith_take_succ f mol.atoms hatom, hatoms]
  have hsame : ∀ order, order = bond.order → (⟨q, i, order⟩ : Bond) = bond := by
    intro order ho
    rw [ho, ← hbond.1, ← hbond.2]
  have hassumed : assumedOrder (s.atoms ++ [f i atom]) q s.atoms.length
      = mol.assumedOrder bond.a bond.b := by
    rw [hnext, hlen, assumedOrder_writtenWith hf (by omega) (by omega), hbond.1, hbond.2]
  unfold markedSymbol
  cases hup : markAmong marks (bond.a, bond.b) with
  | some up =>
    -- the direction mark, then the atom: the bond gets the order that a
    -- reader assumes
    have horder : bond.order = mol.assumedOrder bond.a bond.b := order_of_marked w hc hmem hup
    show Reads s [markToken up, Token.atom (f i atom)] _
    refine Reads.cons (Q := fun s1 => s1.atoms = s.atoms ∧ s1.bonds = s.bonds ∧
        s1.rings = s.rings ∧ s1.previous = some q ∧ s1.branches = s.branches ∧
        s1.pending = none ∧ (∃ markAt, s1.mark = some (up, markAt)) ∧
        s1.ringBonds = s.ringBonds ∧ s1.directions = s.directions ∧ s1.marked = s.marked) ?_ ?_
    · intro position
      rcases hlast with hlast | hlast | hlast
      · exact ⟨_, step_mark_eq up position hlast, rfl, rfl, rfl, hprev, rfl, hpend,
          ⟨position, rfl⟩, rfl, rfl, rfl⟩
      · exact ⟨_, step_mark_open_eq up position hlast, rfl, rfl, rfl, hprev, rfl, hpend,
          ⟨position, rfl⟩, rfl, rfl, rfl⟩
      · exact ⟨_, step_mark_close_eq up position hlast, rfl, rfl, rfl, hprev, rfl, hpend,
          ⟨position, rfl⟩, rfl, rfl, rfl⟩
    · intro s1 ⟨hatoms1, hbonds1, hrings1, hprev1, hbranches1, hpend1, ⟨markAt, hmark1⟩,
        hringBonds1, hdirections1, hmarked1⟩
      refine Reads.single ?_
      intro position
      refine ⟨_, step_atom_marked_eq (f i atom) position hprev1 hpend1 hmark1
        (by rw [hatoms1, hlen]; exact hq), ⟨?_, rfl, rfl, rfl⟩, ?_, hrings1, ?_, hbranches1, rfl,
        ?_, ?_⟩
      · show some s1.atoms.length = some i
        rw [hatoms1, hlen]
      · show s1.atoms ++ [f i atom] = _
        rw [hatoms1, hnext]
      · show insertBond ⟨q, s1.atoms.length,
            assumedOrder (s1.atoms ++ [f i atom]) q s1.atoms.length⟩ s1.bonds
          = insertBond bond s.bonds
        rw [hatoms1, hbonds1, hassumed, hlen, hsame _ horder.symm]
      · refine hn.chain hmem hring hringBonds1 hrings1 (Or.inr ⟨up, markAt, hup, ?_⟩)
        show (⟨q, s1.atoms.length, up, markAt⟩ : Direction) :: s1.directions = _
        rw [hatoms1, hlen, hdirections1, hbond.1, hbond.2]
      · show MarkedUpTo mol key (i + 1)
          (markedWith s1.marked s1.atoms.length (f i atom) position)
        rw [hmarked1, hatoms1, hlen]
        exact hm.step (f i atom) position (hf.mark i atom)
  | none =>
    rcases hsymbol with hwritten | ⟨homitted, horder⟩
    · -- the bond symbol, then the atom
      simp only [hwritten]
      show Reads s [Token.bond (.order bond.order), Token.atom (f i atom)] _
      refine Reads.cons (Q := fun s1 => s1.atoms = s.atoms ∧ s1.bonds = s.bonds ∧
          s1.rings = s.rings ∧ s1.previous = some q ∧ s1.branches = s.branches ∧
          (∃ symbolAt, s1.pending = some (bond.order, symbolAt)) ∧ s1.mark = none ∧
          s1.ringBonds = s.ringBonds ∧ s1.directions = s.directions ∧ s1.marked = s.marked) ?_ ?_
      · intro position
        rcases hlast with hlast | hlast | hlast
        · exact ⟨_, step_order_eq bond.order position hlast, rfl, rfl, rfl, hprev, rfl,
            ⟨position, rfl⟩, hmark, rfl, rfl, rfl⟩
        · exact ⟨_, step_order_open_eq bond.order position hlast, rfl, rfl, rfl, hprev, rfl,
            ⟨position, rfl⟩, hmark, rfl, rfl, rfl⟩
        · exact ⟨_, step_order_close_eq bond.order position hlast, rfl, rfl, rfl, hprev, rfl,
            ⟨position, rfl⟩, hmark, rfl, rfl, rfl⟩
      · intro s1 ⟨hatoms1, hbonds1, hrings1, hprev1, hbranches1, ⟨symbolAt, hpend1⟩, hmark1,
          hringBonds1, hdirections1, hmarked1⟩
        refine Reads.single ?_
        intro position
        refine ⟨_, step_atom_bonded_eq (f i atom) position hprev1 hpend1 hmark1,
          ⟨?_, rfl, rfl, rfl⟩, ?_, hrings1, ?_, hbranches1, rfl, ?_, ?_⟩
        · show some s1.atoms.length = some i
          rw [hatoms1, hlen]
        · show s1.atoms ++ [f i atom] = _
          rw [hatoms1, hnext]
        · show insertBond ⟨q, s1.atoms.length, bond.order⟩ s1.bonds = insertBond bond s.bonds
          rw [hatoms1, hbonds1, hlen, hsame _ rfl]
        · exact hn.chain hmem hring hringBonds1 hrings1 (Or.inl ⟨hup, hdirections1⟩)
        · show MarkedUpTo mol key (i + 1)
            (markedWith s1.marked s1.atoms.length (f i atom) position)
          rw [hmarked1, hatoms1, hlen]
          exact hm.step (f i atom) position (hf.mark i atom)
    · -- no bond symbol: the reader assumes the order
      simp only [homitted]
      show Reads s [Token.atom (f i atom)] _
      refine Reads.single ?_
      intro position
      refine ⟨_, step_atom_assumed_eq (f i atom) position hprev hpend hmark,
        ⟨?_, rfl, rfl, rfl⟩, hnext, rfl, ?_, rfl, rfl, ?_, ?_⟩
      · show some s.atoms.length = some i
        rw [hlen]
      · show insertBond ⟨q, s.atoms.length,
            assumedOrder (s.atoms ++ [f i atom]) q s.atoms.length⟩ s.bonds
          = insertBond bond s.bonds
        rw [hassumed, hlen, hsame _ horder.symm]
      · exact hn.chain hmem hring rfl rfl (Or.inl ⟨hup, rfl⟩)
      · show MarkedUpTo mol key (i + 1)
          (markedWith s.marked s.atoms.length (f i atom) position)
        rw [hlen]
        exact hm.step (f i atom) position (hf.mark i atom)

/-! ## The end of the text -/

/-- What holds at the end of a written text: the reader has read all atoms
and all bonds, nothing is open, and its notes are those of the spelling. -/
structure AtEnd (mol : Mol) (marks : Marks) (ring : Bond → Bool)
    (par : Nat → Option Nat) (f : Nat → Atom → WrittenAtom) (s : Reading) : Prop where
  atoms : s.atoms = writtenWith f 0 mol.atoms
  bonds : s.bonds = mol.bonds
  pending : s.pending = none
  mark : s.mark = none
  noDot : ∀ position, s.last ≠ .dot position
  branches : s.branches = []
  rings : s.rings = []
  notes : ∃ W, NotesAt mol.bonds ring marks (fun e => decide (e.b < mol.atoms.length)) W s
  marked : MarkedUpTo mol (parKey par) mol.atoms.length s.marked
  centres : ∀ number stored, number < mol.atoms.length →
    mol.orientationAt number = some stored → CentreAsked mol ring number

/-- The stereo step of the reader looks at the atoms and the bonds of the
`Mol` only. -/
theorem stereoFacts_graph (mol : Mol) (rings : List RingBond) (directions : List Direction)
    (marked : List MarkedAtom) :
    stereoFacts { atoms := mol.atoms, bonds := mol.bonds } rings directions marked
      = stereoFacts mol rings directions marked := by
  cases mol
  rfl

/-- If a spelling gives a text, then the `Mol` is well formed, the marks were
chosen, the writer made tokens, and the text is those tokens, spelled. -/
theorem tokens_of_write {spelling : Spelling} {mol : Mol} {text : List Char}
    (h : spelling.write mol = .ok text) :
    mol.WellFormed ∧ ∃ marks written, chooseMarks mol = .ok marks ∧
      spelling.tokens mol marks = .ok written ∧ spell written = some text := by
  unfold Spelling.write at h
  split at h
  · cases h
  · rename_i hwf
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i marks hmarks
        split at h
        · cases h
        · rename_i written hwritten
          split at h
          · rename_i spelled hspell
            cases h
            exact ⟨Decidable.of_not_not hwf, marks, written, hmarks, hwritten, hspell⟩
          · cases h

/-- **From the end of the text to the `Mol`.** If the reader follows the
tokens of a spelling to the end, with nothing open and with the notes of that
spelling, then reading the text gives the `Mol`. -/
theorem read_of_atEnd {mol : Mol} (w : mol.WellFormed) {marks : Marks}
    (hmarks : chooseMarks mol = .ok marks) {par : Nat → Option Nat} {ring : Bond → Bool}
    (hw : Written mol par ring) {f : Nat → Atom → WrittenAtom}
    (hf : WritesAtoms mol (parKey par) f) {text : List Char} {tokens : List Token}
    (hspell : spell tokens = some text)
    (hreads : Reads Reading.start tokens (fun s => AtEnd mol marks ring par f s)) :
    read text = .ok mol := by
  -- the text is cut into the tokens that were spelled (theorem 7)
  obtain ⟨hproblem, hcut⟩ := cut_spell tokens text hspell
  obtain ⟨s', hsteps, hend⟩ := hreads (cut text).tokens hcut
  obtain ⟨W, hn⟩ := hend.notes
  have hrange := w.1
  -- the atoms and the bonds
  have hgraph : s'.graph = { atoms := mol.atoms, bonds := mol.bonds } := by
    simp only [Reading.graph, hend.atoms, hend.bonds, finishAtoms_writtenWith hf]
  -- the notes
  have hr : RingsNoted mol.bonds ring s'.ringBonds := by
    unfold RingsNoted
    have hsame : (mol.bonds.filter fun e => ring e && decide (e.b < mol.atoms.length))
        = mol.bonds.filter ring := by
      apply List.filter_congr
      intro e he
      have := (hrange e he).2
      simp [this]
    rw [← hsame]
    exact hn.ringBonds
  have hd : DirectionsNoted mol marks s'.directions := by
    constructor
    · intro d hd
      obtain ⟨e, he, _, rest⟩ := hn.marked d hd
      exact ⟨e, he, rest⟩
    · intro e he up hup
      have := (hrange e he).2
      exact hn.noted e he (by simpa using this) up hup
  have hm : MarkedNoted mol par s'.marked := MarkedUpTo.noted w hend.marked
  have hfacts := stereoFacts_back w hmarks hw hr hd hm (fun atom stored hs =>
    hend.centres atom stored (Mol.orientation_lt w ((Mol.orientationAt_eq_some w).1 hs)) hs)
  have hwith : withStereo s' = .ok mol := by
    unfold withStereo
    rw [hgraph, stereoFacts_graph, hfacts]
  -- the end of the text: nothing is open
  unfold VeriMol.read readCut
  rw [hsteps]
  simp only [hproblem]
  cases hlast : s'.last <;>
    first
    | exact absurd hlast (hend.noDot _)
    | simp [finish, hlast, hend.pending, hend.mark, hend.branches, hend.rings, firstOpened,
        hwith]

/-! ## The two spellings -/

/-- The bonds along which the text of a spelling runs: all of them, or in the
plain spelling those between two atoms that follow each other. -/
def Spelling.along (spelling : Spelling) (mol : Mol) : List Bond :=
  mol.bonds.filter spelling.runsAlong

/-- Two atoms that are joined by a bond along which the text runs are bonded. -/
theorem bonded_of_along (spelling : Spelling) (mol : Mol) {p i : Nat}
    (h : bonded (spelling.along mol) p i = true) : bonded mol.bonds p i = true := by
  unfold bonded Spelling.along at *
  obtain ⟨e, he, hpe⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨e, (List.mem_filter.1 he).1, hpe⟩

/-- A spelling writes a bond with a ring number unless its later atom is
written next to its earlier atom. -/
def Spelling.ring (spelling : Spelling) (mol : Mol) (e : Bond) : Bool :=
  ringBond (spelling.parents mol) e

/-- The parent of an atom is an earlier atom, and the atom is bonded to it. -/
theorem parentOf_parent (spelling : Spelling) (mol : Mol) {x p : Nat}
    (h : parentOf (spelling.parents mol) x = some p) :
    p < x ∧ bonded mol.bonds p x = true := by
  unfold parentOf at h
  cases hx : (spelling.parents mol)[x]? with
  | none =>
    rw [hx] at h
    cases h
  | some v =>
    rw [hx] at h
    simp only [Option.getD_some] at h
    subst h
    have := parentsFrom_parent (spelling.along mol) mol.atoms 0 [] (by simp) x p hx
    exact ⟨by simpa using this.1, bonded_of_along spelling mol (by simpa using this.2)⟩

/-- In both spellings an atom is written next to its parent, and every other
bond gets a ring number. -/
theorem written_spelling (spelling : Spelling) (mol : Mol) :
    Written mol (parentOf (spelling.parents mol)) (spelling.ring mol) := by
  constructor
  · intro e _
    unfold Spelling.ring ringBond
    simp
  · intro x p h
    exact (parentOf_parent spelling mol h).1

/-- Where a spelling writes a place of an atom, in the words of
`VeriMol/Proofs/Facts.lean`. -/
theorem placeKey_eq (parents : List (Option Nat)) (atom : Nat) (place : Place) :
    placeKey parents atom place = parKey (parentOf parents) atom place := by
  cases place <;> rfl

/-- The bonds that close at atom `i` with a ring number, as the writer picks
them. -/
theorem closes_eq (spelling : Spelling) (mol : Mol) (i : Nat) :
    (mol.bonds.filter fun bond => bond.b == i && ringBond (spelling.parents mol) bond)
      = mol.bonds.filter (closesAt (spelling.ring mol) i) := rfl

/-- The bonds that open at atom `i` with a ring number, as the writer picks
them. -/
theorem opens_eq (spelling : Spelling) (mol : Mol) (i : Nat) :
    (mol.bonds.filter fun bond => bond.a == i && ringBond (spelling.parents mol) bond)
      = mol.bonds.filter (opensAt (spelling.ring mol) i) := rfl

/-- The bonds that close at atom `i` with a ring number: the bonds that end at
the atom, the one to its parent aside. -/
theorem closes_of_parent (spelling : Spelling) (mol : Mol) {i : Nat} {parent : Option Nat}
    (hparent : parentOf (spelling.parents mol) i = parent) :
    mol.bonds.filter (closesAt (spelling.ring mol) i)
      = mol.bonds.filter fun bond => bond.b == i && parent != some bond.a := by
  apply List.filter_congr
  intro e _
  unfold closesAt Spelling.ring ringBond
  by_cases h : e.b = i
  · rw [h, hparent]
  · have : (e.b == i) = false := by simpa using h
    simp [this]

/-- The bonds that open at atom `i` with a ring number: the bonds that begin at
the atom, those to an atom whose parent it is aside. -/
theorem opens_of_parent (spelling : Spelling) (mol : Mol) (i : Nat) :
    mol.bonds.filter (opensAt (spelling.ring mol) i)
      = mol.bonds.filter fun bond =>
          bond.a == i && parentOf (spelling.parents mol) bond.b != some i := by
  apply List.filter_congr
  intro e _
  unfold opensAt Spelling.ring ringBond
  by_cases h : e.a = i
  · rw [h]
  · have : (e.a == i) = false := by simpa using h
    simp [this]

/-- An atom without an orientation, as a spelling writes it: in square
brackets in the plain spelling, and without them where that is safe in the
spelling with round brackets. -/
def Spelling.unmarked (spelling : Spelling) (bonds : List Bond) (number : Nat) (atom : Atom) :
    WrittenAtom :=
  match spelling with
  | .plain => atom.inBrackets (writtenLowercase bonds number atom)
  | .brackets => writtenAs bonds number atom

/-- The token that the spelling writes for such an atom. -/
theorem Spelling.atom_eq (spelling : Spelling) (bonds : List Bond) (number : Nat) (atom : Atom) :
    spelling.atom bonds number atom = .atom (spelling.unmarked bonds number atom) := by
  cases spelling <;> rfl

/-- How a spelling writes an atom: one with an orientation in square brackets
with its mark, and every other atom as `Spelling.unmarked` says. -/
def Spelling.written (spelling : Spelling) (mol : Mol) (number : Nat) (atom : Atom) :
    WrittenAtom :=
  match mol.orientationAt number with
  | none => spelling.unmarked mol.bonds number atom
  | some _ => markedInBrackets mol (parKey (parentOf (spelling.parents mol))) number atom

/-- A spelling writes its atoms as the proof needs it (`WritesAtoms`). -/
theorem writesAtoms_spelling (spelling : Spelling) (mol : Mol) :
    WritesAtoms mol (parKey (parentOf (spelling.parents mol))) (spelling.written mol) := by
  refine ⟨?_, ?_, ?_⟩
  · intro number atom
    unfold Spelling.written
    split
    · cases spelling
      · rfl
      · exact writtenAs_aromatic _ _ _
    · rfl
  · intro number atom
    unfold Spelling.written
    split
    · cases spelling
      · cases atom
        rfl
      · exact toAtom_writtenAs _ _ _
    · exact toAtom_markedInBrackets _ _ _ _ _
  · intro number atom
    unfold Spelling.written
    split
    · rename_i hnone
      have hmark : (spelling.unmarked mol.bonds number atom).mark = none := by
        cases spelling
        · rfl
        · exact writtenAs_mark _ _ _
      rw [hmark]
      unfold markFor
      rw [hnone]
      rfl
    · rfl

/-- The symbol that a spelling writes for a bond without a mark: the symbol
of the bond, or nothing where the bond has the order that a reader assumes. -/
theorem Spelling.symbol_cases (spelling : Spelling) (mol : Mol) (bond : Bond) :
    spelling.symbol mol bond = [Token.bond (.order bond.order)] ∨
      (spelling.symbol mol bond = [] ∧ bond.order = mol.assumedOrder bond.a bond.b) := by
  cases spelling
  · exact Or.inl rfl
  · simp only [Spelling.symbol]
    rw [shortSymbol_eq]
    by_cases hassumed : bond.order = mol.assumedOrder bond.a bond.b
    · exact Or.inr ⟨by simp only [hassumed, ↓reduceIte], hassumed⟩
    · exact Or.inl (by simp only [hassumed, ↓reduceIte, plainSymbol])

/-! ## Atom by atom -/

/-- What stands in front of an atom in a spelling, and the atom itself. The
reader ends behind the atom, with the bond to its parent read and its marks
noted, and with exactly those branches open at which a round bracket is open
in the text. -/
theorem beforeAtom_reads (spelling : Spelling) {mol : Mol} (w : mol.GraphWellFormed)
    {marks : Marks} (hc : MarksChosen mol marks) {W : List (Nat × Bond)}
    {i : Nat} {path : List Nat} {s : Reading} {atom : Atom} {parent : Option Nat}
    {laterP : List (Option Nat)} (hpathAt : PathAt i path) (hatom : mol.atoms[i]? = some atom)
    (hparent : parent = path.find? (fun earlier => bonded (spelling.along mol) earlier i))
    (hparentOf : parentOf (spelling.parents mol) i = parent)
    (hlater : ∀ q, some q ∈ laterP → q ∈ nextPath i path parent ∨ i + 1 ≤ q)
    (hatoms : s.atoms = writtenWith (spelling.written mol) 0 (mol.atoms.take i))
    (hprev : s.previous = prevOf i) (hpend : s.pending = none) (hmark : s.mark = none)
    (hlast : s.last = lastOf i)
    (hbonds : s.bonds = mol.bonds.filter (fun e => decide (e.b < i)))
    (hbranches : s.branches.map (·.1) = (openOn path (parent :: laterP)).map some)
    (hn : NotesAt mol.bonds (spelling.ring mol) marks (fun e => decide (e.b < i)) W s)
    (hm : MarkedUpTo mol (parKey (parentOf (spelling.parents mol))) i s.marked) :
    Reads s (beforeAtom spelling mol marks i parent laterP
        ++ [Token.atom (spelling.written mol i atom)]) (fun s' =>
      AtAtom i s' ∧ s'.atoms = writtenWith (spelling.written mol) 0 (mol.atoms.take (i + 1)) ∧
      s'.rings = s.rings ∧
      s'.bonds = mol.bonds.filter
        (fun e => decide (e.b < i) || decide (e.b = i ∧ parent = some e.a)) ∧
      s'.branches.map (·.1) = (openOn (nextPath i path parent) laterP).map some ∧
      s'.numbersAtAtom = 0 ∧
      NotesAt mol.bonds (spelling.ring mol) marks
        (fun e => decide (e.b < i) || decide (e.b = i ∧ parent = some e.a)) W s' ∧
      MarkedUpTo mol (parKey (parentOf (spelling.parents mol))) (i + 1) s'.marked) := by
  have hl := w.2
  have hf := writesAtoms_spelling spelling mol
  cases parent with
  | none =>
    -- no round bracket is open here
    have hbr : s.branches = [] := by
      rw [openOn_none hpathAt hlater] at hbranches
      simpa using hbranches
    have hnone : openOn (nextPath i path none) laterP = [] := by simp [nextPath, openOn]
    rw [hnone]
    have hpred : ∀ e ∈ mol.bonds, decide (e.b < i)
        = (decide (e.b < i) || decide (e.b = i ∧ (none : Option Nat) = some e.a)) := by
      intro e _
      simp
    -- the atom, read with no atom before it to bond to
    have hatomStep : ∀ s2 : Reading, (SameNotes s s2 ∧ s2.previous = none ∧ s2.branches = []) →
        Reads s2 [Token.atom (spelling.written mol i atom)] (fun s' =>
          AtAtom i s' ∧
          s'.atoms = writtenWith (spelling.written mol) 0 (mol.atoms.take (i + 1)) ∧
          s'.rings = s.rings ∧
          s'.bonds = mol.bonds.filter
            (fun e => decide (e.b < i) || decide (e.b = i ∧ (none : Option Nat) = some e.a)) ∧
          s'.branches.map (·.1) = ([] : List Nat).map some ∧ s'.numbersAtAtom = 0 ∧
          NotesAt mol.bonds (spelling.ring mol) marks
            (fun e => decide (e.b < i) || decide (e.b = i ∧ (none : Option Nat) = some e.a))
            W s' ∧
          MarkedUpTo mol (parKey (parentOf (spelling.parents mol))) (i + 1) s'.marked) := by
      intro s2 ⟨hsame, h4, h5⟩
      refine (alone_notes hf hatom (hsame.atoms.trans hatoms) h4 (hsame.notesAt hn)
        (by rw [hsame.marked]; exact hm)).mono ?_
      intro s' ⟨hat, hatoms', hrings', hbonds', hbranches', hnumbers', hn', hm'⟩
      refine ⟨hat, hatoms', hrings'.trans hsame.rings, ?_, by rw [hbranches', h5]; rfl,
        hnumbers', hn'.congr hpred rfl rfl rfl, hm'⟩
      rw [hbonds', hsame.bonds, hbonds]
      apply List.filter_congr
      exact hpred
    cases i with
    | zero =>
      simp only [beforeAtom, ↓reduceIte, List.nil_append]
      exact hatomStep s ⟨SameNotes.refl s, by rw [hprev]; rfl, hbr⟩
    | succ k =>
      have hlast' : s.last = .atom := by rw [hlast]; rfl
      simp only [beforeAtom, Nat.add_one_ne_zero, ↓reduceIte]
      refine Reads.append (Q := fun s2 => SameNotes s s2 ∧ s2.previous = none ∧
          s2.branches = []) ?_ hatomStep
      refine Reads.single ?_
      intro position
      exact ⟨_, step_dot_eq position (Or.inl hlast'),
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, hbr⟩
  | some p =>
    have hfind : path.find? (fun earlier => bonded (spelling.along mol) earlier i) = some p :=
      hparent.symm
    have hp : p ∈ path := List.mem_of_find?_eq_some hfind
    have hpi : p < i := hpathAt.below p hp
    have hbonded : bonded mol.bonds p i = true :=
      bonded_of_along spelling mol
        (List.find?_some (p := fun earlier => bonded (spelling.along mol) earlier i) hfind)
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hlast' : s.last = .atom := by rw [hlast]; rfl
    -- the bond between the atom and its parent
    obtain ⟨bond, hfb, hmem, hbond⟩ : ∃ bond,
        mol.bonds.find? (fun bond => bond.a == p && bond.b == k + 1) = some bond ∧
        bond ∈ mol.bonds ∧ (bond.a = p ∧ bond.b = k + 1) := by
      cases hfb : mol.bonds.find? (fun bond => bond.a == p && bond.b == k + 1) with
      | none =>
        have hnone := List.find?_eq_none.mp hfb
        simp only [bonded, List.any_eq_true] at hbonded
        obtain ⟨x, hx, hpx⟩ := hbonded
        exact absurd hpx (hnone x hx)
      | some bond =>
        have hpred := List.find?_some hfb
        simp at hpred
        exact ⟨bond, rfl, List.mem_of_find?_eq_some hfb, hpred⟩
    obtain ⟨Y, hY1, hY2, hY3⟩ := openOn_parent laterP hpathAt hp hlater
    -- 1. the round bracket that closes, if the parent is not the atom just
    -- before
    have hA : Reads s (if p + 1 = k + 1 then [] else [Token.branchClose])
        (fun s1 => SameNotes s s1 ∧ s1.previous = some p ∧
          (s1.last = .atom ∨ s1.last = .branchClose) ∧
          s1.branches.map (·.1) = Y.map some) := by
      by_cases hnext : p + 1 = k + 1
      · simp only [hnext, ↓reduceIte]
        refine Reads.nil ⟨SameNotes.refl s, ?_, Or.inl hlast', ?_⟩
        · rw [hprev]
          simp only [prevOf, Option.some.injEq]
          omega
        · rw [hbranches, hY1 hnext]
      · simp only [hnext, ↓reduceIte]
        rw [hY2 hnext, List.map_cons] at hbranches
        obtain ⟨entry, rest, hsplit, hentry, hrest⟩ := List.map_eq_cons_iff.mp hbranches
        refine Reads.single ?_
        intro position
        exact ⟨_, step_branchClose_eq (saved := entry.1) (openedAt := entry.2) position
          (Or.inl hlast') hsplit, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hentry,
          Or.inr rfl, hrest⟩
    -- 2. the round bracket that opens, if a later atom has the same parent
    have hB : ∀ s1 : Reading, (SameNotes s s1 ∧ s1.previous = some p ∧
          (s1.last = .atom ∨ s1.last = .branchClose) ∧
          s1.branches.map (·.1) = Y.map some) →
        Reads s1 (if laterP.contains (some p) then [Token.branchOpen] else [])
          (fun s2 => SameNotes s s2 ∧ s2.previous = some p ∧
          (s2.last = .atom ∨ s2.last = .branchOpen ∨ s2.last = .branchClose) ∧
          s2.branches.map (·.1)
            = (openOn (nextPath (k + 1) path (some p)) laterP).map some) := by
      intro s1 ⟨hsame, h5, h6, h7⟩
      by_cases hl2 : laterP.contains (some p) = true
      · simp only [hl2, ↓reduceIte, hY3]
        refine Reads.single ?_
        intro position
        refine ⟨_, step_branchOpen_eq position h6,
          hsame.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h5, Or.inr (Or.inl rfl), ?_⟩
        show ((s1.previous, position) :: s1.branches).map (·.1) = _
        rw [h5]
        simp [h7]
      · have hl2' : laterP.contains (some p) = false := Bool.eq_false_iff.mpr hl2
        simp only [hl2', Bool.false_eq_true, ↓reduceIte, hY3]
        refine Reads.nil ⟨hsame, h5, ?_, h7⟩
        rcases h6 with h6 | h6
        · exact Or.inl h6
        · exact Or.inr (Or.inr h6)
    -- what `beforeAtom` gives
    have hbeforeEq : beforeAtom spelling mol marks (k + 1) (some p) laterP
        = (if p + 1 = k + 1 then [] else [Token.branchClose])
          ++ (if laterP.contains (some p) then [Token.branchOpen] else [])
          ++ markedSymbol marks (spelling.symbol mol) bond := by
      simp only [beforeAtom, hfb]
    rw [hbeforeEq]
    -- 3. the mark or the bond symbol, if one is written, and the atom
    rw [List.append_assoc]
    refine Reads.append (Reads.append hA hB) ?_
    intro s2 ⟨hsame, h5, h6, h7⟩
    have hsymbol := spelling.symbol_cases mol bond
    have hring : spelling.ring mol bond = false := by
      unfold Spelling.ring ringBond
      rw [hbond.2, hparentOf, hbond.1]
      simp
    refine (symbol_atom_notes w hf hc hmem hbond hpi hsymbol hring hatom
      (hsame.atoms.trans hatoms) h5 (hsame.pending.trans hpend) (hsame.mark.trans hmark) h6
      (hsame.notesAt hn) (by rw [hsame.marked]; exact hm)).mono ?_
    intro s' ⟨hat, hatoms', hrings', hbonds', hbranches', hnumbers', hn', hm'⟩
    refine ⟨hat, hatoms', hrings'.trans hsame.rings, ?_, by rw [hbranches', h7], hnumbers',
      hn'.congr (parent_bond_pred hl hmem hbond) rfl rfl rfl, hm'⟩
    rw [hbonds', hsame.bonds, hbonds, insert_parent_bond hl hmem hbond]

/-- What holds between two atoms of a spelling, when `i` atoms are written.
The reader has read exactly these atoms and all bonds among them. It has those
ring numbers open that the writer has, and a branch for every round bracket
that is open in the text (`openOn`). `path` is the path of the writer at this
point: the writer does not keep it while it writes, but its round brackets
follow from it. And the reader's notes are those of the spelling so far. -/
structure WrittenAt (spelling : Spelling) (mol : Mol) (marks : Marks) (i : Nat)
    (path : List Nat) (W : List (Nat × Bond)) (s : Reading) : Prop where
  atoms : s.atoms = writtenWith (spelling.written mol) 0 (mol.atoms.take i)
  previous : s.previous = prevOf i
  pending : s.pending = none
  last : s.last = lastOf i
  mark : s.mark = none
  bonds : s.bonds = mol.bonds.filter (fun e => decide (e.b < i))
  rel : Mirrors (notedSymbol mol) W s.rings
  inv : TableHolds mol.bonds
    (fun e => e.a < i ∧ i ≤ e.b ∧ parentOf (spelling.parents mol) e.b ≠ some e.a) W
  branches : s.branches.map (·.1) = (openOn path ((spelling.parents mol).drop i)).map some
  pathAt : PathAt i path
  later : (spelling.parents mol).drop i = parentsFrom (spelling.along mol) i path (mol.atoms.drop i)
  notes : NotesAt mol.bonds (spelling.ring mol) marks (fun e => decide (e.b < i)) W s
  marked : MarkedUpTo mol (parKey (parentOf (spelling.parents mol))) i s.marked
  centres : ∀ number stored, number < i → mol.orientationAt number = some stored →
    CentreAsked mol (spelling.ring mol) number

/-- All atoms of a spelling, one after the other. -/
theorem tokensFrom_reads (spelling : Spelling) {mol : Mol} (w : mol.WellFormed)
    {marks : Marks} (hc : MarksChosen mol marks) :
    ∀ (rest : List (Atom × Option Nat)) (i : Nat) (path : List Nat) (W : List (Nat × Bond))
      (s : Reading) (tokens : List Token),
      tokensFrom spelling mol marks (spelling.parents mol) i rest W = .ok tokens →
      mol.atoms.drop i = rest.map (·.1) → (spelling.parents mol).drop i = rest.map (·.2) →
      i ≤ mol.atoms.length → WrittenAt spelling mol marks i path W s →
      Reads s tokens (fun s' =>
        AtEnd mol marks (spelling.ring mol) (parentOf (spelling.parents mol)) (spelling.written mol)
          s') := by
  have hrange := w.1
  have hl := w.2.1
  have hf := writesAtoms_spelling spelling mol
  intro rest
  induction rest with
  | nil =>
    intro i path W s tokens hw hA hP hle hb
    have hge : mol.atoms.length ≤ i := by
      have := congrArg List.length hA
      simp at this
      omega
    obtain rfl : i = mol.atoms.length := by omega
    -- no atom is still to come, so no round bracket is open
    have hbr : s.branches = [] := by
      have hnone : openOn path [] = [] := by
        unfold openOn
        rw [List.filter_eq_nil_iff]
        intro a _
        simp
      have := hb.branches
      rw [hP, List.map_nil, hnone] at this
      simpa using this
    simp only [tokensFrom, Except.ok.injEq] at hw
    subst hw
    refine Reads.nil ⟨?_, ?_, hb.pending, hb.mark, ?_, hbr, ?_, ⟨W, hb.notes⟩, hb.marked,
      hb.centres⟩
    · rw [hb.atoms, List.take_of_length_le (Nat.le_refl _)]
    · rw [hb.bonds, List.filter_eq_self]
      intro e he
      have := (hrange e he).2
      simpa using this
    · intro position hdot
      have := hb.last
      rw [hdot] at this
      cases hn : mol.atoms.length <;> simp [hn, lastOf] at this
    · apply eq_nil_of_ringAt_none
      intro k
      apply hb.rel.1
      cases hk : ringAt k W with
      | none => rfl
      | some e =>
        obtain ⟨hel, hq⟩ := hb.inv.1 k e hk
        have := (hrange e hel).2
        omega
  | cons head rest ih =>
    obtain ⟨atom, parent⟩ := head
    intro i path W s tokens hw hA hP hle hb
    -- what the two lists say about atom i
    have hatom : mol.atoms[i]? = some atom := by
      have := congrArg List.head? hA
      simpa [List.head?_drop] using this
    have hA' : mol.atoms.drop (i + 1) = rest.map (·.1) := by
      have := congrArg List.tail hA
      simpa [List.tail_drop] using this
    have hparentAt : (spelling.parents mol)[i]? = some parent := by
      have := congrArg List.head? hP
      simpa [List.head?_drop] using this
    have hP' : (spelling.parents mol).drop (i + 1) = rest.map (·.2) := by
      have := congrArg List.tail hP
      simpa [List.tail_drop] using this
    have hparentOf : parentOf (spelling.parents mol) i = parent := by simp [parentOf, hparentAt]
    have hi : i < mol.atoms.length := (List.getElem?_eq_some_iff.mp hatom).1
    -- the parent of atom i, and the path behind it
    have hlater := hb.later
    rw [hP, hA] at hlater
    simp only [List.map_cons] at hlater
    obtain ⟨hparent, hlater'⟩ := parentsFrom_cons_eq hlater.symm
    -- the parents of the atoms still to come are on the path behind atom i,
    -- or come later
    have hlaterMem : ∀ q, some q ∈ rest.map (·.2) → q ∈ nextPath i path parent ∨ i + 1 ≤ q := by
      intro q hq
      rw [hlater'] at hq
      exact mem_parentsFrom (spelling.along mol) _ (i + 1) _ q hq
    have hbranches : s.branches.map (·.1)
        = (openOn path (parent :: rest.map (·.2))).map some := by
      have := hb.branches
      rw [hP] at this
      exact this
    -- what the writer writes for atom i
    simp only [tokensFrom] at hw
    split at hw
    · cases hw
    · rename_i token htoken
      split at hw
      · cases hw
      · rename_i closing W1 h1
        split at hw
        · cases hw
        · rename_i opening W2 h2
          split at hw
          · cases hw
          · rename_i behind h3
            cases hw
            -- the atom, and whether it could be written where it stands
            have htok : token = Token.atom (spelling.written mol i atom) ∧
                ∀ stored, mol.orientationAt i = some stored →
                  centreRefusal mol i parent.isSome
                    ((mol.bonds.filter (closesAt (spelling.ring mol) i)).length
                      + (mol.bonds.filter (opensAt (spelling.ring mol) i)).length)
                    = none := by
              split at htoken
              · rename_i hnone
                cases htoken
                refine ⟨?_, fun stored hs => by rw [hnone] at hs; cases hs⟩
                simp only [Spelling.atom_eq, Spelling.written, hnone]
              · rename_i stored hsome
                split at htoken
                · cases htoken
                · rename_i hrefusal
                  cases htoken
                  refine ⟨?_, fun stored' hs => by
                    rw [hsome] at hs
                    cases hs
                    exact hrefusal⟩
                  rw [orientedAtom_eq]
                  unfold Spelling.written markedInBrackets markFor
                  rw [hsome, show placeKey (spelling.parents mol) i
                      = parKey (parentOf (spelling.parents mol)) i
                    from funext (placeKey_eq (spelling.parents mol) i)]
                  rfl
            obtain ⟨rfl, hasked⟩ := htok
            rw [closes_eq] at h1
            rw [opens_eq] at h2
            have hnodup := nodup_of_ordered hl
            have htokens : beforeAtom spelling mol marks i parent (rest.map (·.2))
                  ++ Token.atom (spelling.written mol i atom) :: closing ++ opening ++ behind
                = (beforeAtom spelling mol marks i parent (rest.map (·.2))
                    ++ [Token.atom (spelling.written mol i atom)])
                  ++ (closing ++ (opening ++ behind)) := by
              simp
            rw [htokens]
            refine Reads.append (beforeAtom_reads spelling w.graph hc hb.pathAt hatom hparent
              hparentOf hlaterMem hb.atoms hb.previous hb.pending hb.mark hb.last hb.bonds
              hbranches hb.notes hb.marked) ?_
            intro sA ⟨hatA, hatomsA, hringsA, hbondsA, hbranchesA, hnumbersA, hnA, hmA⟩
            -- the ring numbers that close
            refine Reads.append
              (closeRings_notes hl (spelling.ring mol) marks (notedSymbol mol) i _ [] W W1 closing
                sA _ _ h1 (List.nil_append _).symm hnumbersA hb.inv (hringsA ▸ hb.rel) hatA
                hbondsA hnA ?_ (hnodup.sublist List.filter_sublist) ?_) ?_
            · intro c hc'
              obtain ⟨hcl, hcp⟩ := List.mem_filter.mp hc'
              simp [closesAt, Spelling.ring, ringBond] at hcp
              have hc2 := (hrange c hcl).1
              have hne : ¬ parent = some c.a := by
                rw [← hparentOf, ← hcp.1]
                exact hcp.2
              refine ⟨hcl, by omega, hcp.1, ?_⟩
              simp [hcp.1]
              exact hne
            · intro c hc' o ho
              obtain ⟨hcl, hcp⟩ := List.mem_filter.mp hc'
              simp [closesAt] at hcp
              have hc2 := (hrange c hcl).1
              rw [hatomsA, assumedOrder_writtenWith hf (by omega) (by omega)]
              rcases ho with ho | ⟨ho, hassumed⟩
              · rw [ho]
                rfl
              · rw [ho, hassumed, hcp.1]
                rfl
            -- the ring numbers that open
            intro sB ⟨hrelB, hinvB, hatB, hatomsB, hbranchesB, hbondsB, hnumbersB, hmarkedB, hnB⟩
            refine Reads.append
              (openRings_notes hl (spelling.ring mol) marks (notedSymbol mol) (spelling.symbol mol)
                i _ [] W1 W2 opening sB _ _ h2 (List.nil_append _).symm (by rw [hnumbersB]; simp)
                hinvB hrelB hatB hnB ?_ (hnodup.sublist List.filter_sublist) ?_ ?_) ?_
            · intro c hc'
              obtain ⟨hcl, hcp⟩ := List.mem_filter.mp hc'
              simp [opensAt] at hcp
              refine ⟨hcl, hcp.1, ?_⟩
              intro hq
              have := hq.1.1
              omega
            · intro c _ _
              rcases spelling.symbol_cases mol c with hwritten | ⟨hleft, hassumed⟩
              · exact Or.inl ⟨hwritten, Or.inl rfl⟩
              · exact Or.inr ⟨hleft, Or.inr ⟨rfl, hassumed⟩⟩
            · intro c hc' up hup
              exact Or.inr ⟨rfl, order_of_marked w.graph hc (List.mem_filter.mp hc').1 hup⟩
            -- the reader stands between atom i and the next one
            intro sC ⟨hrelC, hinvC, hatC, hatomsC, hbranchesC, hbondsC, hmarkedC, hnC⟩
            have hpred : ∀ e ∈ mol.bonds,
                ((decide (e.b < i) || decide (e.b = i ∧ parent = some e.a))
                  || (mol.bonds.filter (closesAt (spelling.ring mol) i)).contains e)
                = decide (e.b < i + 1) := by
              intro e he
              have he2 := (hrange e he).1
              rw [closes_of_parent spelling mol hparentOf, Bool.eq_iff_iff]
              simp [List.mem_filter, he]
              constructor
              · rintro ((h | h) | h) <;> omega
              · intro h
                by_cases hlt : e.b < i
                · exact Or.inl (Or.inl hlt)
                · by_cases hpar : parent = some e.a
                  · exact Or.inl (Or.inr ⟨by omega, hpar⟩)
                  · exact Or.inr ⟨by omega, hpar⟩
            refine ih (i + 1) (nextPath i path parent) W2 sC behind h3 hA' hP' (by omega) ?_
            refine { atoms := by rw [hatomsC, hatomsB, hatomsA], previous := hatC.previous,
                     pending := hatC.pending, last := hatC.last, mark := hatC.mark, bonds := ?_,
                     rel := hrelC, inv := ?_,
                     branches := by rw [hbranchesC, hbranchesB, hbranchesA, hP'],
                     pathAt := hb.pathAt.next parent,
                     later := by rw [hP', hA']; exact hlater',
                     notes := hnC.congr hpred rfl rfl rfl,
                     marked := by rw [hmarkedC, hmarkedB]; exact hmA, centres := ?_ }
            · rw [hbondsC, hbondsB]
              apply List.filter_congr
              exact hpred
            · refine hinvC.mono ?_
              intro e he hq
              have he2 := (hrange e he).1
              rcases hq with ⟨⟨h1', h2', h3'⟩, hnot⟩ | hopened
              · refine ⟨by omega, ?_, h3'⟩
                by_cases hbi : e.b = i
                · exfalso
                  apply hnot
                  rw [closes_of_parent spelling mol hparentOf, List.mem_filter]
                  refine ⟨he, ?_⟩
                  rw [hbi, hparentOf] at h3'
                  simp [hbi]
                  exact h3'
                · omega
              · rw [opens_of_parent] at hopened
                obtain ⟨hel, hcp⟩ := List.mem_filter.mp hopened
                simp at hcp
                refine ⟨by omega, by omega, ?_⟩
                rw [hcp.1]
                exact hcp.2
            · intro number stored hlt hs
              by_cases hni : number = i
              · subst hni
                refine ⟨parent.isSome, _, ?_, ?_, hasked stored hs⟩
                · constructor
                  · intro hsome
                    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsome
                    have hbonded := (parentOf_parent spelling mol (hparentOf.trans hp)).2
                    unfold bonded at hbonded
                    obtain ⟨e, he, hpe⟩ := List.any_eq_true.1 hbonded
                    rw [Bool.and_eq_true] at hpe
                    refine ⟨e, he, eq_of_beq hpe.2, ?_⟩
                    unfold Spelling.ring ringBond
                    rw [eq_of_beq hpe.2, hparentOf, hp, eq_of_beq hpe.1]
                    simp
                  · rintro ⟨e, he, hb', hr⟩
                    unfold Spelling.ring ringBond at hr
                    rw [hb', hparentOf] at hr
                    have hpar : parent = some e.a := by simpa using hr
                    rw [hpar]
                    rfl
                · rfl
              · exact hb.centres number stored (by omega) hs

/-! ## The round trip -/

/-- **Reading undoes writing, in both spellings.** If a spelling gives a text
for a `Mol`, reading that text returns exactly the `Mol` that was written,
with its stereo facts. Theorems 11 and 12 of CLAIMS.md are its two cases. -/
theorem Spelling.read_write (spelling : Spelling) (mol : Mol) (text : List Char)
    (h : spelling.write mol = .ok text) : read text = .ok mol := by
  obtain ⟨hmol, marks, tokens, hmarks, htokens, hspell⟩ := tokens_of_write h
  have hc := marksChosen hmol hmarks
  have hlenP : (spelling.parents mol).length = mol.atoms.length := parentsFrom_length _ _ _ _
  have h0 : WrittenAt spelling mol marks 0 [] [] Reading.start :=
    { atoms := rfl, previous := rfl, pending := rfl, last := rfl, mark := rfl,
      bonds := by simp [Reading.start],
      rel := ⟨fun _ _ => rfl, fun k e hk => by simp [ringAt] at hk⟩,
      inv := ⟨fun k e hk => by simp [ringAt] at hk,
        fun k k' e hk => by simp [ringAt] at hk⟩,
      branches := rfl,
      pathAt := ⟨List.nodup_nil, by simp, rfl⟩,
      later := rfl,
      notes := ⟨by simp [Reading.start], fun d hd => by simp [Reading.start] at hd,
        fun e _ hpe => by simp at hpe, fun k e hk => by simp [ringAt] at hk⟩,
      marked := MarkedUpTo.start mol _,
      centres := fun number _ hlt => absurd hlt (Nat.not_lt_zero _) }
  exact read_of_atEnd hmol hmarks (written_spelling spelling mol)
    (writesAtoms_spelling spelling mol) hspell
    (tokensFrom_reads spelling hmol hc (mol.atoms.zip (spelling.parents mol)) 0 [] []
      Reading.start tokens htokens (by simp [List.map_fst_zip, hlenP])
      (by simp [List.map_snd_zip, hlenP]) (Nat.zero_le _) h0)

/-- Theorem 11 of CLAIMS.md. The spelling with round brackets, which the
commands `rewrite` and `canonical` print: if it gives a text, reading that text
returns exactly the `Mol` that was written, with its stereo facts.

This holds for every `Mol`: one that is not well formed gets no text. -/
theorem read_write (mol : Mol) (text : List Char) (h : write mol = .ok text) :
    read text = .ok mol :=
  Spelling.brackets.read_write mol text h

/-- Theorem 12 of CLAIMS.md. The same for the plain spelling, which the
command `plain` prints: if it gives a text, reading that text returns exactly
the `Mol` that was written, with its stereo facts. -/
theorem read_writePlain (mol : Mol) (text : List Char) (h : writePlain mol = .ok text) :
    read text = .ok mol :=
  Spelling.plain.read_write mol text h

end VeriMol
