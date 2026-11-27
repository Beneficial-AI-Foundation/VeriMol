import VeriMol.Proofs.Follow

/-!
# The spelling with round brackets: what the writer does for it

That a spelling is read back as the same `Mol` is proven in
`VeriMol/Proofs/RoundTrip.lean`, for both spellings at once (theorems 11 and
12 of CLAIMS.md). This file holds what that proof needs to know about the
three things that the spelling with round brackets has and the plain one has
not (`VeriMol/Core/WriteParts.lean`, `VeriMol/Core/Write.lean`).

1. **Atoms without square brackets.** The reader works out the hydrogens of
   such an atom at the end of the text, from the bonds it has then. The
   writer leaves the square brackets out only where that gives the atom back
   (`toAtom_writtenAs`, from `writtenBare`).
2. **Bond symbols that are left out.** The reader assumes an order from the
   two atoms. The writer leaves a symbol out exactly if the bond has that
   order (`shortSymbol_eq`, with `Mol.assumedOrder`).
3. **Round brackets.** SPEC.md, section 9.2, describes them with a path: the
   atom just written, the atom it stands next to, and so on. The writer finds
   the parents with the path (`parentsFrom`). While it writes, it keeps
   neither the path nor the round brackets that are open: it writes a `(` in
   front of an atom whose parent has another atom to come, and a `)` when the
   text comes back to a parent. The proof keeps the path (`PathAt`). A round
   bracket is open at the atoms of the path, without its first, that are the
   parent of an atom still to come (`openOn`). A parent of an atom still to
   come is an atom of the path or a later atom (`mem_parentsFrom`). So when
   the text comes back to a parent, the innermost round bracket that is open
   is the one of this parent (`openOn_parent`), and one `)` brings the
   reader, which remembers for every `(` the atom in front of it, back to
   the parent. And in front of an atom without a parent no round bracket is
   open (`openOn_none`). `VeriMol/Proofs/BracketRules.lean` rests on these
   as well, and `VeriMol/Proofs/RingNumbers.lean` on three of the lemmas
   about the parents (`parentsFrom_length`, `parentsFrom_parent`,
   `parentsFrom_previous`).
-/

namespace VeriMol

/-! ## Atoms, with or without square brackets -/

/-- How the spelling with round brackets writes an atom that has no
orientation: without square brackets where that is safe, otherwise in them.
An atom with an orientation stands in square brackets with its mark
(`Spelling.written` in `VeriMol/Proofs/RoundTrip.lean`). -/
def writtenAs (bonds : List Bond) (number : Nat) (atom : Atom) : WrittenAtom :=
  if writtenBare bonds number atom then .bare atom.element (writtenLowercase bonds number atom)
  else atom.inBrackets (writtenLowercase bonds number atom)

/-- Such an atom carries no stereo mark. -/
theorem writtenAs_mark (bonds : List Bond) (number : Nat) (atom : Atom) :
    (writtenAs bonds number atom).mark = none := by
  unfold writtenAs
  split <;> rfl

/-- Either way the atom is lowercase exactly if it has an aromatic bond and its
element has a lowercase symbol. -/
theorem writtenAs_aromatic (bonds : List Bond) (number : Nat) (atom : Atom) :
    (writtenAs bonds number atom).aromatic = writtenLowercase bonds number atom := by
  unfold writtenAs
  split <;> rfl

/-- Reading gives the atom back, once the bonds of the atom are all there. For
an atom without square brackets that is what the first three conditions of
SPEC.md, section 9.2, are for. -/
theorem toAtom_writtenAs (bonds : List Bond) (number : Nat) (atom : Atom) :
    (writtenAs bonds number atom).toAtom (bondSum bonds number) = atom := by
  unfold writtenAs
  split
  · rename_i hbare
    simp only [writtenBare, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hbare
    obtain ⟨⟨⟨⟨⟨_, hisotope⟩, hcharge⟩, hhydrogens⟩, _⟩, _⟩ := hbare
    cases atom
    simp_all [WrittenAtom.toAtom, WrittenAtom.bare]
  · cases atom
    rfl

/-! ## Bond symbols that are left out -/

/-- The bond symbol is left out exactly if the bond has the order that a
reader assumes (`Mol.assumedOrder`). -/
theorem shortSymbol_eq (mol : Mol) (bond : Bond) :
    shortSymbol mol bond
      = if bond.order = mol.assumedOrder bond.a bond.b then [] else plainSymbol bond := rfl

/-- What the reader has noted as the bond symbol of an open ring bond, in both
spellings: the symbol, or nothing if the bond has the order that a reader
assumes. No symbol stands in front of a ring number where the spelling with
round brackets leaves it out, and in both spellings where a direction mark
takes its place (`order_of_marked` in `VeriMol/Proofs/RoundTrip.lean`). -/
def notedSymbol (mol : Mol) (e : Bond) (symbol : Option BondOrder) : Prop :=
  symbol = some e.order ∨ (symbol = none ∧ e.order = mol.assumedOrder e.a e.b)

/-! ## The path of the writer -/

/-- A path with `p` in it: what stands above `p`, and what stands below. -/
theorem path_split {path : List Nat} {p : Nat} (hp : p ∈ path) :
    ∃ above below, path = above ++ p :: below ∧ p ∉ above ∧
      path.dropWhile (· != p) = p :: below := by
  induction path with
  | nil => simp at hp
  | cons x xs ih =>
    by_cases hx : x = p
    · subst hx
      exact ⟨[], xs, rfl, by simp, by simp [List.dropWhile]⟩
    · have hp' : p ∈ xs := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨above, below, hxs, hnot, hdrop⟩ := ih hp'
      have hxb : (x != p) = true := by simpa using hx
      refine ⟨x :: above, below, by rw [hxs]; rfl, ?_, ?_⟩
      · simp [hnot, Ne.symm hx]
      · simp [List.dropWhile, hxb, hdrop]

/-- Every atom gets an entry: its parent, or none. -/
theorem parentsFrom_length (bonds : List Bond) (i : Nat) (path : List Nat) (atoms : List Atom) :
    (parentsFrom bonds i path atoms).length = atoms.length := by
  induction atoms generalizing i path with
  | nil => rfl
  | cons a rest ih =>
    simp only [parentsFrom]
    split <;> simp [ih]

/-- The path for the atoms behind atom `i`, whose parent is `parent`: cut back
to the parent with atom `i` in front, or atom `i` alone. -/
def nextPath (i : Nat) (path : List Nat) : Option Nat → List Nat
  | some p => i :: path.dropWhile (· != p)
  | none => [i]

/-- One step of finding the parents: the parent of the atom, and the path for
the atoms behind it. -/
theorem parentsFrom_cons_eq {bonds : List Bond} {i : Nat} {path : List Nat} {atom : Atom}
    {rest : List Atom} {parent : Option Nat} {laterP : List (Option Nat)}
    (h : parentsFrom bonds i path (atom :: rest) = parent :: laterP) :
    parent = path.find? (fun earlier => bonded bonds earlier i) ∧
    laterP = parentsFrom bonds (i + 1) (nextPath i path parent) rest := by
  unfold parentsFrom at h
  split at h
  · rename_i q hq
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hq.symm, rfl⟩
  · rename_i hq
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hq.symm, rfl⟩

/-- A parent is an atom of the path, or an atom that is written later. So an
atom that has left the path is the parent of no atom still to come. -/
theorem mem_parentsFrom (bonds : List Bond) : ∀ (atoms : List Atom) (i : Nat) (path : List Nat)
    (q : Nat), some q ∈ parentsFrom bonds i path atoms → q ∈ path ∨ i ≤ q
  | [], _, _, _, h => by simp [parentsFrom] at h
  | _ :: rest, i, path, q, h => by
    unfold parentsFrom at h
    split at h
    · rename_i parent hfind
      rcases List.mem_cons.mp h with h | h
      · have hq : q = parent := by simpa using h
        subst hq
        exact Or.inl (List.mem_of_find?_eq_some hfind)
      · rcases mem_parentsFrom bonds rest (i + 1) _ q h with h | h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (by omega)
          · exact Or.inl ((List.dropWhile_sublist _).subset h)
        · exact Or.inr (by omega)
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · rcases mem_parentsFrom bonds rest (i + 1) _ q h with h | h
        · have hq : q = i := by simpa using h
          exact Or.inr (by omega)
        · exact Or.inr (by omega)

/-- What is known about the path when `i` atoms are written. -/
structure PathAt (i : Nat) (path : List Nat) : Prop where
  nodup : path.Nodup
  below : ∀ a ∈ path, a < i
  head : path.head? = prevOf i

/-- It is known again behind the next atom. -/
theorem PathAt.next {i : Nat} {path : List Nat} (h : PathAt i path) (parent : Option Nat) :
    PathAt (i + 1) (nextPath i path parent) := by
  cases parent with
  | none => exact ⟨by simp [nextPath], by simp [nextPath], rfl⟩
  | some p =>
    have hsub : (path.dropWhile (· != p)).Sublist path := List.dropWhile_sublist _
    refine ⟨?_, ?_, rfl⟩
    · simp only [nextPath, List.nodup_cons]
      refine ⟨fun hmem => ?_, h.nodup.sublist hsub⟩
      exact Nat.lt_irrefl i (h.below i (hsub.subset hmem))
    · intro a ha
      simp only [nextPath, List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · have := h.below a (hsub.subset ha)
        omega

/-- The atoms of the path at which a round bracket is open: all but the first
one that are the parent of an atom still to come. -/
def openOn (path : List Nat) (toCome : List (Option Nat)) : List Nat :=
  (path.drop 1).filter (fun a => toCome.contains (some a))

/-- In front of an atom without a parent no round bracket is open: the path
starts again with this atom, and no atom of the path before it is the parent
of an atom that comes behind it. -/
theorem openOn_none {i : Nat} {path : List Nat} {laterP : List (Option Nat)} (h : PathAt i path)
    (hlater : ∀ q, some q ∈ laterP → q ∈ nextPath i path none ∨ i + 1 ≤ q) :
    openOn path (none :: laterP) = [] := by
  unfold openOn
  rw [List.filter_eq_nil_iff]
  intro a ha hc
  have hlt : a < i := h.below a (List.mem_of_mem_drop ha)
  have hmem : some a ∈ laterP := by simpa using hc
  rcases hlater a hmem with h1 | h1
  · have : a = i := by simpa [nextPath] using h1
    omega
  · omega

/-- The open round brackets, seen from an atom whose parent is `p`. `Y` holds
the ones below `p`. If `p` is the atom just before, no other is open.
Otherwise the round bracket of `p` is open as well, and it is the innermost:
the atoms above `p` leave the path here, so none of them is the parent of an
atom still to come. And behind the atom the ones below `p` are open, and that
of `p` again if a later atom has the same parent. -/
theorem openOn_parent {i : Nat} {path : List Nat} {p : Nat} (laterP : List (Option Nat))
    (h : PathAt i path) (hp : p ∈ path)
    (hlater : ∀ q, some q ∈ laterP → q ∈ nextPath i path (some p) ∨ i + 1 ≤ q) :
    ∃ Y, (p + 1 = i → openOn path (some p :: laterP) = Y) ∧
      (p + 1 ≠ i → openOn path (some p :: laterP) = p :: Y) ∧
      openOn (nextPath i path (some p)) laterP
        = (if laterP.contains (some p) then p :: Y else Y) := by
  obtain ⟨above, below, hpath, hnot, hdrop⟩ := path_split hp
  have hnodup := h.nodup
  rw [hpath] at hnodup
  have hbelow : ∀ a ∈ below, a ≠ p := by
    intro a ha hap
    subst hap
    have := (List.nodup_append.mp hnodup).2.1
    simp at this
    exact this.1 ha
  -- for an atom below p it makes no difference whether atom i is still to come
  have hsame : below.filter (fun a => (some p :: laterP).contains (some a))
      = below.filter (fun a => laterP.contains (some a)) := by
    apply List.filter_congr
    intro a ha
    simp [hbelow a ha]
  refine ⟨below.filter (fun a => laterP.contains (some a)), ?_, ?_, ?_⟩
  · intro hpi
    cases above with
    | nil =>
      rw [hpath]
      simpa [openOn] using hsame
    | cons x above' =>
      have hx := h.head
      rw [hpath] at hx
      have := prevOf_eq_some hx.symm
      exact absurd (show x = p by omega) (fun hxp => hnot (hxp ▸ List.mem_cons_self))
  · intro hpi
    cases above with
    | nil =>
      have hx := h.head
      rw [hpath] at hx
      have := prevOf_eq_some hx.symm
      omega
    | cons x above' =>
      -- no atom above p is the parent of an atom still to come
      have habove : above'.filter (fun a => (some p :: laterP).contains (some a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha hc
        have hain : a ∈ x :: above' := List.mem_cons_of_mem _ ha
        have hap : a ≠ p := fun e => hnot (e ▸ hain)
        have hmem : some a ∈ laterP := by simpa [hap] using hc
        have hlt : a < i := h.below a (by rw [hpath]; simp [ha])
        rcases hlater a hmem with h1 | h1
        · simp only [nextPath, hdrop, List.mem_cons] at h1
          rcases h1 with h1 | h1 | h1
          · omega
          · exact hap h1
          · exact (List.nodup_append.mp hnodup).2.2 a hain a (List.mem_cons_of_mem _ h1) rfl
        · omega
      rw [hpath]
      simp only [openOn, List.cons_append, List.drop_succ_cons, List.drop_zero, List.filter_append,
        habove, List.nil_append]
      rw [List.filter_cons_of_pos (by simp), hsame]
  · simp only [nextPath, openOn, hdrop, List.drop_succ_cons, List.drop_zero, List.filter_cons]

/-- A parent is an earlier atom, and the atom is bonded to it. -/
theorem parentsFrom_parent (bonds : List Bond) : ∀ (atoms : List Atom) (i : Nat)
    (path : List Nat), (∀ a ∈ path, a < i) →
    ∀ j q, (parentsFrom bonds i path atoms)[j]? = some (some q) →
      q < i + j ∧ bonded bonds q (i + j) = true
  | [], _, _, _, _, _, h => by simp [parentsFrom] at h
  | _ :: rest, i, path, hpath, j, q, h => by
    unfold parentsFrom at h
    split at h
    · rename_i parent hfind
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp only [Nat.add_zero]
        exact ⟨hpath _ (List.mem_of_find?_eq_some hfind),
          List.find?_some (p := fun earlier => bonded bonds earlier i) hfind⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        have := parentsFrom_parent bonds rest (i + 1) _ (by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · have := hpath a ((List.dropWhile_sublist _).subset ha)
            omega) j q h
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e] at this
        exact this
    · cases j with
      | zero => simp at h
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        have := parentsFrom_parent bonds rest (i + 1) [i] (by
          intro a ha
          have : a = i := by simpa using ha
          omega) j q h
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e] at this
        exact this

/-- With the atom just before it on top of the path, an atom that is bonded to
that atom has it as its parent. -/
theorem parentsFrom_previous (bonds : List Bond) : ∀ (atoms : List Atom) (i : Nat)
    (path : List Nat), (∀ k, i = k + 1 → path.head? = some k) →
    ∀ j k, i + j = k + 1 → j < atoms.length → bonded bonds k (k + 1) = true →
      (parentsFrom bonds i path atoms)[j]? = some (some k)
  | [], _, _, _, _, _, _, hj, _ => by simp at hj
  | _ :: rest, i, path, hhead, j, k, hk, hj, hb => by
    cases j with
    | zero =>
      have hi : i = k + 1 := by omega
      subst hi
      have hpath := hhead k rfl
      cases path with
      | nil => simp at hpath
      | cons x xs =>
        simp only [List.head?_cons, Option.some.injEq] at hpath
        subst hpath
        simp [parentsFrom, hb]
    | succ j =>
      have hrest : j < rest.length := by simpa using hj
      unfold parentsFrom
      split
      · simp only [List.getElem?_cons_succ]
        exact parentsFrom_previous bonds rest (i + 1) _
          (by intro k' hk'; simp only [List.head?_cons, Option.some.injEq]; omega)
          j k (by omega) hrest hb
      · simp only [List.getElem?_cons_succ]
        exact parentsFrom_previous bonds rest (i + 1) [i]
          (by intro k' hk'; simp only [List.head?_cons, Option.some.injEq]; omega)
          j k (by omega) hrest hb

/-! ## The bond to the parent -/

/-- Which bonds are read once the bond to the parent is read. -/
theorem parent_bond_pred {l : List Bond} (hl : l.Pairwise Bond.before) {bond : Bond} {i p : Nat}
    (hmem : bond ∈ l) (hbond : bond.a = p ∧ bond.b = i) :
    ∀ e ∈ l, (decide (e.b < i) || e == bond)
      = (decide (e.b < i) || decide (e.b = i ∧ some p = some e.a)) := by
  intro e he
  by_cases h : e = bond
  · subst h
    simp [hbond.1, hbond.2]
  · have hb : (e == bond) = false := by simpa using h
    have hno : ¬ (e.b = i ∧ p = e.a) := by
      intro ⟨h1, h2⟩
      exact h (key_unique hl he hmem (by omega) (by omega))
    simp [hb, hno]

/-- The bond to the parent, put among the bonds between earlier atoms. -/
theorem insert_parent_bond {l : List Bond} (hl : l.Pairwise Bond.before) {bond : Bond}
    {i p : Nat} (hmem : bond ∈ l) (hbond : bond.a = p ∧ bond.b = i) :
    insertBond bond (l.filter (fun e => decide (e.b < i)))
      = l.filter (fun e => decide (e.b < i) || decide (e.b = i ∧ some p = some e.a)) := by
  rw [insertBond_filter hl _ hmem (by simp [hbond.2])]
  exact List.filter_congr (parent_bond_pred hl hmem hbond)

end VeriMol
