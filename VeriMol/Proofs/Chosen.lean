import VeriMol.Core.Chosen
import VeriMol.Core.Run
import VeriMol.Proofs.Read
import VeriMol.Proofs.Refusal
import VeriMol.Proofs.Same
import VeriMol.Proofs.Search
import VeriMol.Proofs.Write

/-!
# The chosen form is the same molecule, and the same for every numbering

Theorems 23 to 35 and 44 of CLAIMS.md, and the fourth statement of theorem 20.
The helper lemmas are about well formed `Mol`s, and about orders that name
every atom once (`IsOrderOf`). Their statements say so, also where a
docstring does not repeat it.

1. Putting the atoms of a well formed `Mol` in a new order gives the same
   molecule, numbered differently (`Mol.renumbered_arrange`). So the chosen
   form is the same molecule (`Mol.renumbered_chosenForm`, theorem 23), and it
   is well formed (theorem 24).
2. Every numbering of a molecule is reached by putting the atoms in a new
   order (`Mol.eq_arrange_of_renumbered`; with point 1 this is the fourth
   statement of theorem 20, `Mol.renumbered_iff_arrange`), and two well formed
   `Mol`s with the same key are equal (`Mol.eq_of_key_eq`, the second
   statement of theorem 25). So among all numberings of a molecule exactly
   one `Mol` has the least key, and the chosen form is that one
   (`Mol.chosenForm_least`, theorem 25).
3. The search finds a numbering with the least key
   (`VeriMol/Proofs/Search.lean`). Atoms that can be exchanged are placed in
   the order of their numbers, which loses no chosen form, because exchanging
   two such atoms gives the same `Mol` (`Mol.renumberedBy_swapOf`). And for a
   `Mol` without stereo facts, of the beginnings that are alike the search
   holds one, which loses no chosen form either: beginnings with the same
   outline have the same futures (`Mol.merges`). If the atoms are numbered
   differently, they can be renamed so that the two searches are the same
   search under other names, outlines included
   (`Mol.same_outline_of_renames`); then the search holds equally many
   beginnings in every round, so it gives up for both numberings or for
   neither. So two well formed `Mol`s that are the same molecule, numbered
   differently, get the same chosen form, or none for both
   (`Mol.chosenForm_eq_of_renumbered`, theorem 26).
4. So a well formed `Mol` is the same molecule as one that has a chosen form,
   numbered differently, exactly when it has that chosen form (theorem 27),
   and the chosen form of a well formed `Mol` is its own chosen form (theorem
   28).
5. The command `canonical`: theorems 29 to 35, in the order of CLAIMS.md,
   except that theorem 32 stands in front of theorem 31, which uses it. They
   say what points 1 to 4 mean for the texts that `canonical` prints; theorem
   35 also uses `VeriMol/Proofs/Refusal.lean`.
6. An example in which the search finds the chosen form (theorem 44). Without
   one, everything above could hold for a search that always gives up.
-/

namespace VeriMol

open Search

/-! ## Putting the atoms in a new order -/

/-- `order` names every atom number below `n` once. -/
structure IsOrderOf (n : Nat) (order : List Nat) : Prop where
  nodup : order.Nodup
  below : ∀ a ∈ order, a < n
  length : order.length = n

theorem IsOrderOf.mem {n : Nat} {order : List Nat} (h : IsOrderOf n order) {i : Nat} (hi : i < n) :
    i ∈ order :=
  mem_of_nodup_below h.nodup (fun a ha => List.mem_range.2 (h.below a ha)) h.length hi

/-! ## Lists -/

theorem getElem?_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome) → ∀ (j : Nat), (l.filterMap f)[j]? = l[j]?.bind f
  | [], _, j => by simp
  | a :: l, h, j => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a (List.mem_cons_self ..))
    have ih := getElem?_filterMap_of_isSome f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases j with
    | zero => simp [hb]
    | succ j => simp [hb, ih j]

theorem length_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a (List.mem_cons_self ..))
    simp [hb, length_filterMap_of_isSome f l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem mem_pairsBelow {n x y : Nat} : (x, y) ∈ pairsBelow n ↔ x < y ∧ y < n := by
  simp only [pairsBelow, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨x', _, y', ⟨hy', hxy⟩, heq⟩
    cases heq
    exact ⟨hxy, hy'⟩
  · rintro ⟨hxy, hy⟩
    exact ⟨x, by omega, y, ⟨hy, hxy⟩, rfl⟩

theorem pairsBelow_ordered (n : Nat) :
    (pairsBelow n).Pairwise fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  unfold pairsBelow
  rw [List.pairwise_flatMap]
  constructor
  · intro x _
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range.sublist List.filter_sublist).imp fun h => Or.inr ⟨rfl, h⟩
  · exact List.pairwise_lt_range.imp fun {a b} hab p hp q hq => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hp
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hq
      exact Or.inl hab

/-! ## The bond between two atoms -/

theorem Mol.joined_of_orderBetween {m : Mol} {i j : Nat} {order : BondOrder}
    (h : m.orderBetween i j = some order) : m.Joined i j order := by
  unfold Mol.orderBetween at h
  cases hfind : m.bonds.find? (fun b => (b.a == i && b.b == j) || (b.a == j && b.b == i)) with
  | none => simp [hfind] at h
  | some b =>
    rw [hfind] at h
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    have ho : b.order = order := by simpa using h
    obtain ⟨a, b', o⟩ := b
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    simp only at ho
    subst ho
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hmem
    · exact Or.inr hmem

theorem Mol.orderBetween_of_joined {m : Mol} (w : m.WellFormed) {i j : Nat} {order : BondOrder}
    (h : m.Joined i j order) : m.orderBetween i j = some order := by
  unfold Mol.orderBetween
  -- some bond between the two atoms is found
  have hex : ∃ c ∈ m.bonds,
      ((c.a == i && c.b == j) || (c.a == j && c.b == i)) = true ∧ c.order = order := by
    rcases h with h | h
    · exact ⟨_, h, by simp, rfl⟩
    · exact ⟨_, h, by simp, rfl⟩
  obtain ⟨c, hc, hpc, hoc⟩ := hex
  cases hfind : m.bonds.find? (fun b => (b.a == i && b.b == j) || (b.a == j && b.b == i)) with
  | none => exact absurd hpc (List.find?_eq_none.1 hfind c hc)
  | some b =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    -- it is the same bond, because a well formed `Mol` has one bond for a pair of atoms at most
    have hbc : b = c := by
      have wb := (w.1 b hmem).1
      have wc := (w.1 c hc).1
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp hpc
      apply key_unique w.2.1 hmem hc <;> omega
    simp [hbc, hoc]

/-! ## What the new `Mol` holds -/

theorem Mol.arrange_atoms (m : Mol) (order : List Nat) :
    (m.arrange order).atoms = (m.arrangedGraph order).atoms := by
  unfold Mol.arrange
  simp only
  split <;> rfl

theorem Mol.arrange_bonds (m : Mol) (order : List Nat) :
    (m.arrange order).bonds = (m.arrangedGraph order).bonds := by
  unfold Mol.arrange
  simp only
  split <;> rfl

theorem Mol.arrange_places (m : Mol) (order : List Nat) (j : Nat) :
    (m.arrangedGraph order).places j = (m.arrange order).places j := by
  unfold Mol.places Mol.neighbours
  rw [Mol.arrange_bonds]

theorem Mol.arrange_otherNeighbours (m : Mol) (order : List Nat) (a b : Nat) :
    (m.arrangedGraph order).otherNeighbours a b = (m.arrange order).otherNeighbours a b := by
  unfold Mol.otherNeighbours Mol.neighbours
  rw [Mol.arrange_bonds]

theorem Mol.arrange_isSome {m : Mol} {order : List Nat} (ho : IsOrderOf m.atoms.length order) :
    ∀ a ∈ order, (m.atoms[a]?).isSome := by
  intro a ha
  simp [List.getElem?_eq_getElem (ho.below a ha)]

theorem Mol.arrange_length {m : Mol} {order : List Nat} (ho : IsOrderOf m.atoms.length order) :
    (m.arrange order).atoms.length = m.atoms.length := by
  rw [Mol.arrange_atoms]
  simp only [Mol.arrangedGraph]
  rw [length_filterMap_of_isSome _ _ (Mol.arrange_isSome ho), ho.length]

theorem Mol.arrange_atom {m : Mol} {order : List Nat} (ho : IsOrderOf m.atoms.length order)
    (j : Nat) : (m.arrange order).atoms[j]? = order[j]?.bind fun i => m.atoms[i]? := by
  rw [Mol.arrange_atoms]
  simp only [Mol.arrangedGraph]
  rw [getElem?_filterMap_of_isSome _ _ (Mol.arrange_isSome ho)]

theorem Mol.mem_arrange_bonds {m : Mol} {order : List Nat} (ho : IsOrderOf m.atoms.length order)
    (x y : Nat) (o : BondOrder) :
    (⟨x, y, o⟩ : Bond) ∈ (m.arrange order).bonds ↔
      x < y ∧ y < m.atoms.length ∧
        ∃ i j, order[x]? = some i ∧ order[y]? = some j ∧ m.orderBetween i j = some o := by
  rw [Mol.arrange_bonds]
  simp only [Mol.arrangedGraph, List.mem_filterMap]
  constructor
  · rintro ⟨⟨x', y'⟩, hpair, hbond⟩
    rw [mem_pairsBelow, ho.length] at hpair
    simp only [Mol.arrangedBond] at hbond
    split at hbond
    · rename_i i j hi hj
      cases hob : m.orderBetween i j with
      | none => simp [hob] at hbond
      | some o' =>
        simp only [hob, Option.map_some, Option.some.injEq, Bond.mk.injEq] at hbond
        obtain ⟨rfl, rfl, rfl⟩ := hbond
        exact ⟨hpair.1, hpair.2, i, j, hi, hj, hob⟩
    · cases hbond
  · rintro ⟨hxy, hy, i, j, hi, hj, hob⟩
    refine ⟨(x, y), ?_, ?_⟩
    · rw [mem_pairsBelow, ho.length]
      exact ⟨hxy, hy⟩
    · simp [Mol.arrangedBond, hi, hj, hob]

/-- The atoms with an orientation in the new `Mol`: those for which the old
`Mol` gives an answer, for the places in their new fixed order. -/
theorem Mol.mem_arrange_orientations {m : Mol} {order : List Nat} {x : AtomOrientation} :
    x ∈ (m.arrange order).orientations ↔ x.atom < order.length ∧
      m.orientationOf ((order[x.atom]?).getD 0)
        (((m.arrange order).places x.atom).map (Option.map fun place => (order[place]?).getD 0))
        = some x.orientation := by
  rw [← Mol.arrange_places]
  unfold Mol.arrange
  simp only
  split
  · simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
    constructor
    · rintro ⟨place, hplace, o, ho, rfl⟩
      exact ⟨hplace, ho⟩
    · rintro ⟨hplace, ho⟩
      exact ⟨x.atom, hplace, x.orientation, ho, rfl⟩
  · rename_i hstereo
    have hnone : m.orientations = [] := by
      have : ¬ (m.orientations ≠ [] ∨ m.geometries ≠ []) := fun h => hstereo (Mol.hasStereo_iff.2 h)
      apply Classical.byContradiction
      intro hne
      exact this (Or.inl hne)
    rw [Mol.orientationOf_of_nil hnone]
    constructor
    · intro hx
      cases hx
    · rintro ⟨_, hx⟩
      cases hx

/-- The double bonds with a geometry in the new `Mol`: those for which the
old `Mol` gives an answer, for their new lowest-numbered neighbours. -/
theorem Mol.mem_arrange_geometries {m : Mol} {order : List Nat} {x : BondGeometry} :
    x ∈ (m.arrange order).geometries ↔ ∃ bond ∈ (m.arrange order).bonds,
      bond.a = x.a ∧ bond.b = x.b ∧ ∃ p q,
        ((m.arrange order).otherNeighbours bond.a bond.b).head? = some p ∧
        ((m.arrange order).otherNeighbours bond.b bond.a).head? = some q ∧
        m.geometryOf ((order[bond.a]?).getD 0) ((order[bond.b]?).getD 0)
            ((order[p]?).getD 0) ((order[q]?).getD 0)
          = some x.geometry := by
  rw [Mol.arrange_bonds]
  simp only [← Mol.arrange_otherNeighbours]
  unfold Mol.arrange
  simp only
  split
  · simp only [List.mem_filterMap]
    constructor
    · rintro ⟨bond, hbond, hx⟩
      split at hx
      · rename_i p q hp hq
        obtain ⟨geometry, hg, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact ⟨bond, hbond, rfl, rfl, p, q, hp, hq, hg⟩
      · cases hx
    · rintro ⟨bond, hbond, ha, hb, p, q, hp, hq, hg⟩
      obtain ⟨xa, xb, xg⟩ := x
      simp only at ha hb hg
      subst ha hb
      refine ⟨bond, hbond, ?_⟩
      rw [hp, hq]
      simp only
      rw [hg]
      rfl
  · rename_i hstereo
    have hnone : m.geometries = [] := by
      have : ¬ (m.orientations ≠ [] ∨ m.geometries ≠ []) := fun h => hstereo (Mol.hasStereo_iff.2 h)
      apply Classical.byContradiction
      intro hne
      exact this (Or.inr hne)
    constructor
    · intro hx
      cases hx
    · rintro ⟨bond, _, _, _, p, q, _, _, hg⟩
      rw [Mol.geometryOf_of_nil hnone] at hg
      cases hg

/-! ## A new order gives the same molecule -/

/-- For a well formed `Mol` and an order that names every atom once: the atoms
and the bonds of the `Mol` in that order are as a well formed `Mol` wants
them, and they are those of the `Mol` under new numbers: the new number of
atom `i` is its place in `order`. -/
theorem Mol.sameGraph_arrange {m : Mol} (w : m.WellFormed) {order : List Nat}
    (ho : IsOrderOf m.atoms.length order) :
    (m.arrange order).GraphWellFormed ∧
      Mol.SameGraphBy (fun i => order.idxOf i) (fun j => (order[j]?).getD 0) m
        (m.arrange order) := by
  have hsome := Mol.arrange_isSome ho
  have hlen := Mol.arrange_length ho
  have hmemBond := Mol.mem_arrange_bonds ho
  constructor
  · -- well formed
    constructor
    · rintro ⟨x, y, o⟩ hb
      obtain ⟨hxy, hy, _⟩ := (hmemBond x y o).1 hb
      exact ⟨hxy, by rw [hlen]; exact hy⟩
    · rw [Mol.arrange_bonds]
      simp only [Mol.arrangedGraph]
      refine List.Pairwise.filterMap _ ?_ (pairsBelow_ordered order.length)
      intro p q hpq b hb b' hb'
      have e1 : b.a = p.1 ∧ b.b = p.2 := by
        simp only [Mol.arrangedBond] at hb
        split at hb
        · obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hb
          exact ⟨rfl, rfl⟩
        · cases hb
      have e2 : b'.a = q.1 ∧ b'.b = q.2 := by
        simp only [Mol.arrangedBond] at hb'
        split at hb'
        · obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hb'
          exact ⟨rfl, rfl⟩
        · cases hb'
      unfold Bond.before
      rw [e1.1, e1.2, e2.1, e2.2]
      exact hpq
  · -- the same atoms and bonds: the new number of atom `i` is its place in `order`
    have hplace : ∀ i, i < m.atoms.length →
        ∃ h : order.idxOf i < order.length, order[order.idxOf i] = i := by
      intro i hi
      have h := List.idxOf_lt_length_of_mem (ho.mem hi)
      exact ⟨h, List.getElem_idxOf h⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨h, hget⟩ := hplace i hi
      refine ⟨by rw [hlen, ← ho.length]; exact h, ?_⟩
      simp [List.getElem?_eq_getElem h, hget]
    · intro j hj
      rw [hlen, ← ho.length] at hj
      simp only [List.getElem?_eq_getElem hj, Option.getD_some]
      exact ⟨ho.below _ (List.getElem_mem hj), ho.nodup.idxOf_getElem j hj⟩
    · intro i hi
      obtain ⟨h, hget⟩ := hplace i hi
      rw [Mol.arrange_atom ho, List.getElem?_eq_getElem h, hget]
      rfl
    · intro i j o hi hj
      obtain ⟨hx, hgx⟩ := hplace i hi
      obtain ⟨hy, hgy⟩ := hplace j hj
      have hx' : order[order.idxOf i]? = some i := by rw [List.getElem?_eq_getElem hx, hgx]
      have hy' : order[order.idxOf j]? = some j := by rw [List.getElem?_eq_getElem hy, hgy]
      rw [ho.length] at hx hy
      constructor
      · intro hjoined
        have hij : i ≠ j := by
          rcases hjoined with h | h <;> have := (w.1 _ h).1 <;> simp only at this <;> omega
        have hne : order.idxOf i ≠ order.idxOf j := by
          intro e
          apply hij
          rw [← hgx, ← hgy]
          simp [e]
        have hob := Mol.orderBetween_of_joined w hjoined
        have hob' : m.orderBetween j i = some o :=
          Mol.orderBetween_of_joined w (hjoined.symm)
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ((hmemBond _ _ o).2 ⟨hlt, hy, i, j, hx', hy', hob⟩)
        · exact Or.inr ((hmemBond _ _ o).2 ⟨hgt, hx, j, i, hy', hx', hob'⟩)
      · rintro (h | h)
        · obtain ⟨_, _, i', j', hi', hj', hob⟩ := (hmemBond _ _ o).1 h
          rw [hx'] at hi'
          rw [hy'] at hj'
          cases hi'; cases hj'
          exact Mol.joined_of_orderBetween hob
        · obtain ⟨_, _, j', i', hj', hi', hob⟩ := (hmemBond _ _ o).1 h
          rw [hx'] at hi'
          rw [hy'] at hj'
          cases hi'; cases hj'
          exact (Mol.joined_of_orderBetween hob).symm

/-- A well formed `Mol` with its atoms in a new order, one that names every
atom once, is well formed, and it is the same molecule: the new number of
atom `i` is its place in `order`, and the atom at the new number `j` is atom
`order[j]`. -/
theorem Mol.renumberedBy_arrange {m : Mol} (w : m.WellFormed) {order : List Nat}
    (ho : IsOrderOf m.atoms.length order) :
    (m.arrange order).WellFormed ∧
      Mol.RenumberedBy (fun i => order.idxOf i) (fun j => (order[j]?).getD 0) m
        (m.arrange order) := by
  obtain ⟨wg, hs⟩ := Mol.sameGraph_arrange w ho
  have hlen := Mol.arrange_length ho
  -- the stereo facts of the new `Mol` are as a well formed `Mol` wants them
  have wa : (m.arrange order).WellFormed := by
    refine ⟨wg.1, wg.2, ?_, ?_, ?_, ?_⟩
    · unfold Mol.arrange
      simp only
      split
      · refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
        intro a a' haa o ho o' ho'
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 ho
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 ho'
        exact haa
      · exact List.Pairwise.nil
    · intro x hx
      obtain ⟨hplace, hof⟩ := Mol.mem_arrange_orientations.1 hx
      obtain ⟨s, hs'⟩ := Mol.orientationAt_of_orientationOf hof
      have hj : x.atom < (m.arrange order).atoms.length := by rw [hlen, ← ho.length]; exact hplace
      obtain ⟨hg, hfg⟩ := hs.back x.atom hj
      have hfour := hs.hasFourPlaces w.graph wg hg
      rw [hfg] at hfour
      rw [hfour]
      exact (Mol.fourPlaces_of_orientationAt w hs').1
    · unfold Mol.arrange
      simp only
      split
      · have hord : (m.arrangedGraph order).bonds.Pairwise Bond.before := by
          rw [← Mol.arrange_bonds]
          exact wg.2
        refine List.Pairwise.filterMap _ ?_ hord
        intro bond bond' hbb g hg g' hg'
        have e1 : g.a = bond.a ∧ g.b = bond.b := by
          split at hg
          · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hg
            exact ⟨rfl, rfl⟩
          · cases hg
        have e2 : g'.a = bond'.a ∧ g'.b = bond'.b := by
          split at hg'
          · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hg'
            exact ⟨rfl, rfl⟩
          · cases hg'
        rw [e1.1, e1.2, e2.1, e2.2]
        exact hbb
      · exact List.Pairwise.nil
    · intro x hx
      obtain ⟨bond, hbond, hxa, hxb, p, q, _, _, hg⟩ := Mol.mem_arrange_geometries.1 hx
      obtain ⟨t, ht⟩ := Mol.geometryAt_of_geometryOf hg
      obtain ⟨hab, hblt⟩ := wg.1 bond hbond
      have halt : bond.a < (m.arrange order).atoms.length := by omega
      obtain ⟨hga, hfga⟩ := hs.back bond.a halt
      obtain ⟨hgb, hfgb⟩ := hs.back bond.b hblt
      have hcan := hs.canHaveGeometry w.graph wg hga hgb (by rw [hfga, hfgb]; exact hab)
        (Mol.canHave_of_geometryAt w ht).1
      rw [hfga, hfgb, hxa, hxb] at hcan
      exact hcan
  refine ⟨wa, Mol.RenumberedBy.of_stored hs w wa ?_ ?_⟩
  · -- the mark that the new `Mol` stores for an atom
    intro j hj
    have hjo : j < order.length := by rw [ho.length, ← hlen]; exact hj
    apply Option.ext
    intro o
    rw [Mol.orientationAt_eq_some wa, Mol.mem_arrange_orientations]
    exact ⟨fun h => h.2, fun h => ⟨hjo, h⟩⟩
  · -- the mark that the new `Mol` stores for a double bond
    intro bond hbond x y hx hy
    apply Option.ext
    intro s
    rw [Mol.geometryAt_eq_some wa, Mol.mem_arrange_geometries]
    constructor
    · rintro ⟨bond', _, ha, hb, p, q, hp, hq, hg⟩
      simp only at ha hb
      rw [ha, hb] at hp hq hg
      rw [hx] at hp
      rw [hy] at hq
      cases hp
      cases hq
      exact hg
    · intro hg
      exact ⟨bond, hbond, rfl, rfl, x, y, hx, hy, hg⟩

/-- A well formed `Mol` with its atoms in a new order, one that names every
atom once, is well formed, and it is the same molecule, numbered differently. -/
theorem Mol.renumbered_arrange {m : Mol} (w : m.WellFormed) {order : List Nat}
    (ho : IsOrderOf m.atoms.length order) :
    (m.arrange order).WellFormed ∧ m.Renumbered (m.arrange order) :=
  ⟨(Mol.renumberedBy_arrange w ho).1, _, _, (Mol.renumberedBy_arrange w ho).2⟩

/-! ## What a chosen form is

`before a b` says that the `Mol` `a` comes no later than `b` in some fixed way
of comparing `Mol`s. Further down it is the comparison of their keys
(`Mol.noLaterThan`). All that is asked of it here is that two well formed
`Mol`s which come no later than each other are equal. -/

/-- `c` is the chosen form of `m`: it is the same molecule, it is well formed,
and among all well formed `Mol`s that are the same molecule it comes first. -/
structure Mol.IsChosenForm (before : Mol → Mol → Prop) (m c : Mol) : Prop where
  wellFormed : c.WellFormed
  same : m.Renumbered c
  first : ∀ c' : Mol, c'.WellFormed → m.Renumbered c' → before c c'

/-- A molecule has at most one chosen form, and two `Mol`s that are the same
molecule have the same one. -/
theorem Mol.IsChosenForm.unique {before : Mol → Mol → Prop}
    (antisymm : ∀ a b : Mol, a.WellFormed → b.WellFormed → before a b → before b a → a = b)
    {m₁ m₂ c₁ c₂ : Mol} (h : m₁.Renumbered m₂)
    (h₁ : Mol.IsChosenForm before m₁ c₁) (h₂ : Mol.IsChosenForm before m₂ c₂) : c₁ = c₂ :=
  antisymm c₁ c₂ h₁.wellFormed h₂.wellFormed
    (h₁.first c₂ h₂.wellFormed (h.trans h₂.same))
    (h₂.first c₁ h₁.wellFormed (h.symm.trans h₁.same))

/-! ## Every numbering is reached by putting the atoms in a new order -/

theorem Mol.RenumberedBy.length_le {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) : m₁.atoms.length ≤ m₂.atoms.length := by
  have hnd : ((List.range m₁.atoms.length).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro a b ha hb hab hfab
    have := congrArg g hfab
    rw [(h.forth a (List.mem_range.1 ha)).2, (h.forth b (List.mem_range.1 hb)).2] at this
    omega
  have hsub : (List.range m₁.atoms.length).map f ⊆ List.range m₂.atoms.length := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (h.forth a (List.mem_range.1 ha)).1
  simpa using hnd.length_le_of_subset hsub

/-- Whatever well formed `Mol` is the same molecule as `m`: it is `m` with its
atoms put in some order. -/
theorem Mol.eq_arrange_of_renumbered {m c : Mol} (w : m.WellFormed) (wc : c.WellFormed)
    (h : m.Renumbered c) : ∃ order, IsOrderOf m.atoms.length order ∧ c = m.arrange order := by
  obtain ⟨f, g, hf⟩ := h
  have hlen : m.atoms.length = c.atoms.length := Nat.le_antisymm hf.length_le hf.symm.length_le
  obtain ⟨order, hdef⟩ : ∃ order, order = (List.range c.atoms.length).map g := ⟨_, rfl⟩
  have ho : IsOrderOf m.atoms.length order := by
    refine ⟨?_, ?_, by simp [hdef, hlen]⟩
    · rw [hdef, List.Nodup, List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
      intro a b ha hb hab hgab
      have := congrArg f hgab
      rw [(hf.back a (List.mem_range.1 ha)).2, (hf.back b (List.mem_range.1 hb)).2] at this
      omega
    · intro a ha
      rw [hdef] at ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      exact (hf.back j (List.mem_range.1 hj)).1
  refine ⟨order, ho, ?_⟩
  have horder : ∀ j, j < c.atoms.length → order[j]? = some (g j) := by
    intro j hj
    simp [hdef, List.getElem?_map, List.getElem?_range hj]
  obtain ⟨wa, ha⟩ := Mol.renumberedBy_arrange w ho
  -- from the `Mol` in the new order back to `m`, and on to `c`: no atom gets another number
  have hid : Mol.RenumberedBy id id (m.arrange order) c := by
    refine (ha.symm.trans hf).congr ?_ ?_
    · intro i hi
      rw [Mol.arrange_length ho, hlen] at hi
      simp only [Function.comp, horder i hi, Option.getD_some, (hf.back i hi).2, id]
    · intro j hj
      have hjo : j < order.length := by rw [ho.length, hlen]; exact hj
      have hget : order[j] = g j := by
        have := horder j hj
        rw [List.getElem?_eq_getElem hjo] at this
        exact Option.some.inj this
      have := ho.nodup.idxOf_getElem j hjo
      rw [hget] at this
      simp only [Function.comp, id, this]
  exact (Mol.eq_of_renumberedBy_id wa wc hid).symm

/-- Putting the atoms of a well formed `Mol` in the order that they have gives
the `Mol` itself. -/
theorem Mol.arrange_range {m : Mol} (w : m.WellFormed) :
    m.arrange (List.range m.atoms.length) = m := by
  have ho : IsOrderOf m.atoms.length (List.range m.atoms.length) :=
    ⟨List.nodup_range, fun a ha => List.mem_range.1 ha, List.length_range⟩
  obtain ⟨wa, ha⟩ := Mol.renumberedBy_arrange w ho
  have hid : Mol.RenumberedBy id id m (m.arrange (List.range m.atoms.length)) := by
    refine ha.congr ?_ ?_
    · intro i hi
      have hir : i < (List.range m.atoms.length).length := by simpa using hi
      have := ho.nodup.idxOf_getElem i hir
      simp only [List.getElem_range] at this
      simp only [id, this]
    · intro j hj
      rw [Mol.arrange_length ho] at hj
      simp [List.getElem?_range hj]
  exact (Mol.eq_of_renumberedBy_id w wa hid).symm

/-- If the atoms of two `Mol`s that are the same molecule are put in the same
order, each with its own numbers, the same `Mol` comes out. -/
theorem Mol.RenumberedBy.arrange_map {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) {order : List Nat}
    (ho : IsOrderOf m₁.atoms.length order) : m₂.arrange (order.map f) = m₁.arrange order := by
  have hlen : m₁.atoms.length = m₂.atoms.length := Nat.le_antisymm h.length_le h.symm.length_le
  have ho₂ : IsOrderOf m₂.atoms.length (order.map f) := by
    refine ⟨?_, ?_, by simp [ho.length, hlen]⟩
    · rw [List.Nodup, List.pairwise_map]
      refine ho.nodup.imp_of_mem ?_
      intro a b ha hb hab e
      exact hab (h.sameGraph.injective (ho.below a ha) (ho.below b hb) e)
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      exact (h.forth i (ho.below i hi)).1
  obtain ⟨wa₁, r₁⟩ := Mol.renumberedBy_arrange w₁ ho
  obtain ⟨wa₂, r₂⟩ := Mol.renumberedBy_arrange w₂ ho₂
  have hid : Mol.RenumberedBy id id (m₁.arrange order) (m₂.arrange (order.map f)) := by
    refine ((r₁.symm.trans h).trans r₂).congr ?_ ?_
    · intro i hi
      rw [Mol.arrange_length ho] at hi
      have hio : i < order.length := by rw [ho.length]; exact hi
      have hio₂ : i < (order.map f).length := by simpa using hio
      have := ho₂.nodup.idxOf_getElem i hio₂
      simp only [List.getElem_map] at this
      simp only [Function.comp, id, List.getElem?_eq_getElem hio, Option.getD_some, this]
    · intro j hj
      rw [Mol.arrange_length ho₂, ← hlen] at hj
      have hjo : j < order.length := by rw [ho.length]; exact hj
      have hjo₂ : j < (order.map f).length := by simpa using hjo
      have hback := (h.forth order[j] (ho.below _ (List.getElem_mem hjo))).2
      have := ho.nodup.idxOf_getElem j hjo
      simp only [Function.comp, id, List.getElem?_eq_getElem hjo₂, Option.getD_some,
        List.getElem_map, hback, this]
  exact (Mol.eq_of_renumberedBy_id wa₁ wa₂ hid).symm

/-- An order that names every atom number below `n` once is a permutation of
those numbers, in the words of Lean's own library. -/
theorem IsOrderOf.perm {n : Nat} {order : List Nat} (h : IsOrderOf n order) :
    order.Perm (List.range n) :=
  (List.perm_ext_iff_of_nodup h.nodup List.nodup_range).2 fun a =>
    ⟨fun ha => List.mem_range.2 (h.below a ha), fun ha => h.mem (List.mem_range.1 ha)⟩

theorem IsOrderOf.of_perm {n : Nat} {order : List Nat} (h : order.Perm (List.range n)) :
    IsOrderOf n order :=
  ⟨h.nodup_iff.2 List.nodup_range, fun a ha => List.mem_range.1 (h.mem_iff.1 ha),
    by simpa using h.length_eq⟩

/-- Theorem 20 of CLAIMS.md, fourth statement. "The same molecule, numbered
differently" (SPEC.md, section 3.1), said with the program's own function for
a new order: a well formed `Mol` is another well formed `Mol` numbered
differently exactly when it is that one with its atoms put in a new order
(`Mol.arrange`, SPEC.md, section 3.2), for an order that is a permutation of
the atom numbers. -/
theorem Mol.renumbered_iff_arrange (m c : Mol) (w : m.WellFormed) (wc : c.WellFormed) :
    m.Renumbered c ↔ ∃ order, order.Perm (List.range m.atoms.length) ∧ c = m.arrange order := by
  constructor
  · intro h
    obtain ⟨order, ho, hc⟩ := Mol.eq_arrange_of_renumbered w wc h
    exact ⟨order, ho.perm, hc⟩
  · rintro ⟨order, ho, rfl⟩
    exact (Mol.renumbered_arrange w (IsOrderOf.of_perm ho)).2

/-! ## Comparing `Mol`s: the key

Every `Mol` has a key (`Mol.key` in `VeriMol/Core/Chosen.lean`; SPEC.md,
section 3.2): one entry for every atom, in the order of the atom numbers. Two
`Mol`s are compared by their keys, from the front. -/

/-- How the atoms `i` and `a` are bonded, as a number: the order of their
bond, or 5 if there is none. 5 is the largest, so a bond comes before no
bond. -/
def Mol.bondCode (m : Mol) (i a : Nat) : Nat :=
  match m.orderBetween i a with
  | some o => o.code
  | none => 5

/-- Looking among the bonds at `a` alone finds the same as looking among all
bonds. -/
theorem Mol.bondCodeAmong_bondsAt (m : Mol) (i a : Nat) :
    bondCodeAmong (m.bondsAt a) i a = m.bondCode i a := by
  have hbool : ∀ x y u v : Bool,
      decide ((x || y) = true ∧ ((u && y) || (x && v)) = true) = ((u && y) || (x && v)) := by
    decide
  unfold bondCodeAmong Mol.bondsAt Mol.bondCode Mol.orderBetween
  rw [List.find?_filter]
  have hfun : (fun b : Bond => decide ((b.a == a || b.b == a) = true ∧
        ((b.a == i && b.b == a) || (b.a == a && b.b == i)) = true))
      = fun b : Bond => (b.a == i && b.b == a) || (b.a == a && b.b == i) := by
    funext b
    exact hbool _ _ _ _
  rw [hfun]
  rfl

/-- The row, said with all bonds of the `Mol`. -/
theorem Mol.row_eq (m : Mol) (done : List Nat) (a : Nat) :
    m.row done a = done.reverse.map fun i => m.bondCode i a := by
  simp only [Mol.row, Mol.bondCodeAmong_bondsAt]

/-- `c` comes no later than `c'`: the key of `c` is not greater than the key
of `c'`, in Lean's own order of lists, which compares two keys entry by entry
from the front, and two entries number by number. -/
def Mol.noLaterThan (c c' : Mol) : Prop :=
  c.key ≤ c'.key

theorem leEntry_isOrder : IsOrder leEntry where
  total x y := by
    rcases List.le_total x y with h | h
    · exact Or.inl (by simp [leEntry, h])
    · exact Or.inr (by simp [leEntry, h])
  trans x y z hxy hyz := by
    simp only [leEntry, decide_eq_true_eq] at *
    exact List.le_trans hxy hyz
  antisymm x y hxy hyx := by
    simp only [leEntry, decide_eq_true_eq] at *
    exact List.le_antisymm hxy hyx

/-- Two keys that the search finds in order (`NoLater`, with its own
comparison of entries) are in Lean's own order of lists. -/
theorem le_of_noLater {xs ys : List (List Nat)} (h : NoLater (Lt leEntry) xs ys) : xs ≤ ys := by
  rcases h with rfl | ⟨common, x, y, r₁, r₂, rfl, rfl, hlt⟩
  · exact List.le_refl _
  · have hxy : x < y := by simpa [Lt, leEntry, List.not_le] using hlt
    apply List.le_of_lt
    induction common with
    | nil => exact List.cons_lt_cons_iff.2 (Or.inl hxy)
    | cons c common ih => exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, ih⟩)

/-! ## The key of a `Mol` whose atoms were put in a new order -/

/-- Whether two atoms at the new places `x < y` are bonded is what it was at
their old numbers. -/
theorem Mol.orderBetween_arrange {m : Mol} (w : m.WellFormed) {order : List Nat}
    (ho : IsOrderOf m.atoms.length order) {x y i j : Nat} (hxy : x < y) (hy : y < m.atoms.length)
    (hi : order[x]? = some i) (hj : order[y]? = some j) :
    (m.arrange order).orderBetween x y = m.orderBetween i j := by
  obtain ⟨wa, _⟩ := Mol.renumbered_arrange w ho
  apply Option.ext
  intro o
  constructor
  · intro h
    rcases Mol.joined_of_orderBetween h with h' | h'
    · obtain ⟨_, _, i', j', hi', hj', hob⟩ := (Mol.mem_arrange_bonds ho x y o).1 h'
      rw [hi] at hi'; rw [hj] at hj'
      cases hi'; cases hj'
      exact hob
    · have := (wa.1 _ h').1
      simp only at this
      omega
  · intro h
    exact Mol.orderBetween_of_joined wa
      (Or.inl ((Mol.mem_arrange_bonds ho x y o).2 ⟨hxy, hy, i, j, hi, hj, h⟩))

/-- The key of the new `Mol` is the key of the order, worked out on the old
`Mol`. This is what lets the search work on the old `Mol` alone. -/
theorem Mol.key_arrange {m : Mol} (w : m.WellFormed) {order : List Nat}
    (ho : IsOrderOf m.atoms.length order) :
    (m.arrange order).key = keys m.entry order := by
  have hlen := Mol.arrange_length ho
  apply List.ext_getElem?
  intro j
  simp only [Mol.key, getElem?_keys, hlen]
  by_cases hj : j < m.atoms.length
  · have hjo : j < order.length := by rw [ho.length]; exact hj
    rw [List.getElem?_range hj, List.getElem?_eq_getElem hjo]
    simp only [Option.map_some, Option.some.injEq]
    -- the two entries: the rows agree, and the atoms agree
    have hrow : (m.arrange order).row (List.take j (List.range m.atoms.length)) j
        = m.row (List.take j order) order[j] := by
      rw [Mol.row_eq, Mol.row_eq]
      simp only [List.map_reverse]
      congr 1
      apply List.ext_getElem?
      intro x
      by_cases hxj : x < j
      · have hx' : x < m.atoms.length := by omega
        have hxo : x < order.length := by omega
        simp only [List.getElem?_map, List.getElem?_take_of_lt hxj, List.getElem?_range hx',
          List.getElem?_eq_getElem hxo, Option.map_some, Option.some.injEq]
        simp only [Mol.bondCode]
        rw [Mol.orderBetween_arrange w ho hxj hj (List.getElem?_eq_getElem hxo)
          (List.getElem?_eq_getElem hjo)]
      · simp only [List.getElem?_map, List.getElem?_take]
        simp [hxj]
    have hatom : (m.arrange order).atoms[j]? = m.atoms[order[j]]? := by
      rw [Mol.arrange_atom ho, List.getElem?_eq_getElem hjo]
      rfl
    -- and at the last place, the stereo facts are those of the new `Mol`
    have hstereo : (if ((m.arrange order).hasStereo &&
          (List.take j (List.range m.atoms.length)).length + 1
            == (m.arrange order).atoms.length) = true
        then ((m.arrange order).arrange (List.take j (List.range m.atoms.length) ++ [j])).stereoCode
        else [])
        = (if (m.hasStereo && (List.take j order).length + 1 == m.atoms.length) = true
          then (m.arrange (List.take j order ++ [order[j]])).stereoCode else []) := by
      obtain ⟨wa, ha⟩ := Mol.renumberedBy_arrange w ho
      have hl1 : (List.take j (List.range m.atoms.length)).length = j := by
        rw [List.length_take, List.length_range]
        omega
      have hl2 : (List.take j order).length = j := by
        rw [List.length_take]
        omega
      rw [ha.hasStereo_eq w wa, hlen, hl1, hl2]
      by_cases hlast : j + 1 = m.atoms.length
      · have e1 : List.take j (List.range m.atoms.length) ++ [j]
            = List.range (m.arrange order).atoms.length := by
          rw [hlen, ← hlast, List.take_range, Nat.min_eq_left (Nat.le_succ j), List.range_succ]
        have e2 : List.take j order ++ [order[j]] = order := by
          rw [List.take_append_getElem hjo, List.take_of_length_le (by rw [ho.length]; omega)]
        rw [e1, e2, Mol.arrange_range wa]
      · have hfalse : (j + 1 == m.atoms.length) = false := by simpa using hlast
        simp only [hfalse, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    simp only [Mol.entry, hrow, hatom, hstereo]
  · have hjo : ¬ j < order.length := by rw [ho.length]; exact hj
    rw [List.getElem?_eq_none (by simpa using hj), List.getElem?_eq_none (by omega)]
    rfl

/-! ## Two well formed `Mol`s with the same key are equal -/

theorem BondOrder.code_inj {o o' : BondOrder} (h : o.code = o'.code) : o = o' := by
  cases o <;> cases o' <;> first | rfl | (simp [BondOrder.code] at h)

theorem BondOrder.code_lt (o : BondOrder) : o.code < 5 := by
  cases o <;> decide

/-- Two bond codes are equal only if the bonds are. -/
theorem Mol.orderBetween_of_bondCode {c c' : Mol} {x y x' y' : Nat}
    (h : c.bondCode x y = c'.bondCode x' y') : c.orderBetween x y = c'.orderBetween x' y' := by
  unfold Mol.bondCode at h
  cases h1 : c.orderBetween x y with
  | none =>
    cases h2 : c'.orderBetween x' y' with
    | none => rfl
    | some o' =>
      rw [h1, h2] at h
      have := BondOrder.code_lt o'
      simp only at h
      omega
  | some o =>
    cases h2 : c'.orderBetween x' y' with
    | none =>
      rw [h1, h2] at h
      have := BondOrder.code_lt o
      simp only at h
      omega
    | some o' =>
      rw [h1, h2] at h
      rw [BondOrder.code_inj h]

theorem Element.eq_of_idxOf_eq {e e' : Element}
    (h : Element.all.idxOf e = Element.all.idxOf e') : e = e' := by
  have he : e ∈ Element.all := by cases e <;> decide
  have he' : e' ∈ Element.all := by cases e' <;> decide
  have h1 : Element.all[Element.all.idxOf e]? = some e := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem he), List.getElem_idxOf]
  have h2 : Element.all[Element.all.idxOf e']? = some e' := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem he'), List.getElem_idxOf]
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

theorem Atom.code_inj {a a' : Atom} (h : a.code = a'.code) : a = a' := by
  obtain ⟨e, iso, ch, hy⟩ := a
  obtain ⟨e', iso', ch', hy'⟩ := a'
  simp only [Atom.code, List.cons.injEq, and_true] at h
  obtain ⟨h1, h5, h3, h4⟩ := h
  have e1 : e = e' := Element.eq_of_idxOf_eq h1
  have e5 : hy = hy' := by
    split at h5 <;> split at h5 <;> omega
  have e3 : iso = iso' := by
    cases iso with
    | none =>
      cases iso' with
      | none => rfl
      | some k' => simp at h3
    | some k =>
      cases iso' with
      | none => simp at h3
      | some k' => simp at h3; rw [h3]
  have e4 : ch = ch' := by
    split at h4 <;> split at h4 <;> omega
  subst e1 e3 e4 e5
  rfl

/-- Theorem 25 of CLAIMS.md, second statement. The key of a well formed
`Mol` says the whole `Mol`: two well formed `Mol`s with the same key are
equal. So among the numberings of a molecule the least key belongs to one
`Mol` only, and "the `Mol` with the least key" names one `Mol`. -/
theorem Mol.eq_of_key_eq {c c' : Mol} (w : c.WellFormed) (w' : c'.WellFormed)
    (h : c.key = c'.key) : c = c' := by
  have hlen : c.atoms.length = c'.atoms.length := by
    have := congrArg List.length h
    simpa [Mol.key, length_keys] using this
  -- the keys agree entry by entry
  have hentry : ∀ j, j < c.atoms.length →
      c.entry (List.take j (List.range c.atoms.length)) j
        = c'.entry (List.take j (List.range c.atoms.length)) j := by
    intro j hj
    have := congrArg (fun l => l[j]?) h
    simp only [Mol.key, getElem?_keys, ← hlen, List.getElem?_range hj, Option.map_some,
      Option.some.injEq] at this
    exact this
  -- so the rows agree, the atoms agree, and what the entries say about stereo facts agrees
  have hsplit : ∀ j, j < c.atoms.length →
      c.row (List.take j (List.range c.atoms.length)) j
          = c'.row (List.take j (List.range c.atoms.length)) j
        ∧ c.atoms[j]? = c'.atoms[j]?
        ∧ (if (c.hasStereo
              && (List.take j (List.range c.atoms.length)).length + 1 == c.atoms.length) = true
            then (c.arrange (List.take j (List.range c.atoms.length) ++ [j])).stereoCode else [])
          = (if (c'.hasStereo
              && (List.take j (List.range c.atoms.length)).length + 1 == c'.atoms.length) = true
            then (c'.arrange (List.take j (List.range c.atoms.length) ++ [j])).stereoCode
            else []) := by
    intro j hj
    have hj' : j < c'.atoms.length := by omega
    have h1 := hentry j hj
    simp only [Mol.entry, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
      List.append_assoc] at h1
    obtain ⟨hr, hrest⟩ := List.append_inj h1 (by simp [Mol.row_eq])
    obtain ⟨hc, hthird⟩ := List.append_inj hrest (by simp [Atom.code])
    refine ⟨hr, ?_, hthird⟩
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Atom.code_inj hc]
  have hatoms : c.atoms = c'.atoms := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < c.atoms.length
    · exact (hsplit j hj).2.1
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hob : ∀ x y, x < y → y < c.atoms.length → c.orderBetween x y = c'.orderBetween x y := by
    intro x y hxy hy
    have hr := (hsplit y hy).1
    rw [Mol.row_eq, Mol.row_eq] at hr
    have hx : x ∈ (List.take y (List.range c.atoms.length)).reverse := by
      rw [List.mem_reverse, List.mem_take_iff_getElem]
      exact ⟨x, by simp; omega, by simp⟩
    exact Mol.orderBetween_of_bondCode (List.map_inj_left.1 hr x hx)
  have hbonds : c.bonds = c'.bonds := by
    apply eq_of_ordered_of_mem_iff w.2.1 w'.2.1
    rintro ⟨x, y, o⟩
    constructor
    · intro hb
      obtain ⟨hxy, hy⟩ := w.1 _ hb
      simp only at hxy hy
      have h1 := Mol.orderBetween_of_joined w (Or.inl hb)
      rw [hob x y hxy hy] at h1
      rcases Mol.joined_of_orderBetween h1 with h' | h'
      · exact h'
      · have := (w'.1 _ h').1
        simp only at this
        omega
    · intro hb
      obtain ⟨hxy, hy⟩ := w'.1 _ hb
      simp only at hxy hy
      have h1 := Mol.orderBetween_of_joined w' (Or.inl hb)
      rw [← hob x y hxy (by omega)] at h1
      rcases Mol.joined_of_orderBetween h1 with h' | h'
      · exact h'
      · have := (w.1 _ h').1
        simp only at this
        omega
  -- the stereo facts: the entry of the last place holds them
  have hstereo : c.orientations = c'.orientations ∧ c.geometries = c'.geometries := by
    by_cases hn : c.atoms.length = 0
    · obtain ⟨h1, h2⟩ := Mol.noStereo_of_noAtoms w hn
      obtain ⟨h1', h2'⟩ := Mol.noStereo_of_noAtoms w' (by omega)
      rw [h1, h2, h1', h2']
      exact ⟨rfl, rfl⟩
    · have hj : c.atoms.length - 1 < c.atoms.length := by omega
      have hthird := (hsplit _ hj).2.2
      have hl : (List.take (c.atoms.length - 1) (List.range c.atoms.length)).length + 1
          = c.atoms.length := by
        rw [List.length_take, List.length_range]
        omega
      have e1 : List.take (c.atoms.length - 1) (List.range c.atoms.length) ++ [c.atoms.length - 1]
          = List.range c.atoms.length := by
        have e : c.atoms.length = (c.atoms.length - 1) + 1 := by omega
        rw [List.take_range, Nat.min_eq_left (Nat.sub_le _ _)]
        conv => rhs; rw [e, List.range_succ]
      rw [hl, e1, Mol.arrange_range w] at hthird
      rw [hlen, Mol.arrange_range w'] at hthird
      simp only [beq_self_eq_true, Bool.and_true] at hthird
      have hcode : ∀ m : Mol, m.stereoCode.length = m.atoms.length + m.bonds.length := by
        intro m
        simp [Mol.stereoCode]
      cases hs : c.hasStereo with
      | false =>
        cases hs' : c'.hasStereo with
        | false =>
          obtain ⟨h1, h2⟩ := Mol.noStereo_of_not_hasStereo hs
          obtain ⟨h1', h2'⟩ := Mol.noStereo_of_not_hasStereo hs'
          rw [h1, h2, h1', h2']
          exact ⟨rfl, rfl⟩
        | true =>
          rw [hs, hs'] at hthird
          have := congrArg List.length hthird
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil, hcode] at this
          omega
      | true =>
        cases hs' : c'.hasStereo with
        | false =>
          rw [hs, hs'] at hthird
          have := congrArg List.length hthird
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil, hcode] at this
          omega
        | true =>
          rw [hs, hs'] at hthird
          simp only [↓reduceIte] at hthird
          unfold Mol.stereoCode at hthird
          rw [← hlen, ← hbonds] at hthird
          obtain ⟨hfirst, hsecond⟩ := List.append_inj hthird (by simp)
          constructor
          · apply Mol.orientations_ext w w'
            intro atom
            by_cases hatom : atom < c.atoms.length
            · have := List.map_inj_left.1 hfirst atom (List.mem_range.2 hatom)
              revert this
              generalize c.orientationAt atom = x
              generalize c'.orientationAt atom = y
              intro this
              rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
                first | rfl | (simp at this)
            · rw [Mol.orientationAt_of_ge w (by omega), Mol.orientationAt_of_ge w' (by omega)]
          · apply Mol.geometries_ext w w'
            intro a b
            by_cases hbond : (⟨a, b, .double⟩ : Bond) ∈ c.bonds
            · have := List.map_inj_left.1 hsecond _ hbond
              simp only at this
              revert this
              generalize c.geometryAt a b = x
              generalize c'.geometryAt a b = y
              intro this
              rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
                first | rfl | (simp at this)
            · have h1 : c.geometryAt a b = none := by
                cases hg : c.geometryAt a b with
                | none => rfl
                | some s => exact absurd (Mol.canHave_of_geometryAt w hg).2 hbond
              have h2 : c'.geometryAt a b = none := by
                cases hg : c'.geometryAt a b with
                | none => rfl
                | some s => exact absurd (hbonds ▸ (Mol.canHave_of_geometryAt w' hg).2) hbond
              rw [h1, h2]
  obtain ⟨ho, hg⟩ := hstereo
  cases c
  cases c'
  simp only at hatoms hbonds ho hg
  subst hatoms hbonds ho hg
  rfl

theorem Mol.noLaterThan_antisymm (a b : Mol) (wa : a.WellFormed) (wb : b.WellFormed)
    (h₁ : a.noLaterThan b) (h₂ : b.noLaterThan a) : a = b :=
  Mol.eq_of_key_eq wa wb (List.le_antisymm h₁ h₂)

/-! ## The entries of a renumbered `Mol` -/

/-- How two atoms are bonded is the same after renumbering. -/
theorem Mol.RenumberedBy.orderBetween {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) {i a : Nat}
    (hi : i < m₁.atoms.length) (ha : a < m₁.atoms.length) :
    m₂.orderBetween (f i) (f a) = m₁.orderBetween i a := by
  apply Option.ext
  intro o
  constructor
  · intro h2
    exact Mol.orderBetween_of_joined w₁ ((h.bonds i a o hi ha).2 (Mol.joined_of_orderBetween h2))
  · intro h1
    exact Mol.orderBetween_of_joined w₂ ((h.bonds i a o hi ha).1 (Mol.joined_of_orderBetween h1))

/-- So the searches of the two `Mol`s are the same search under other names. -/
theorem Mol.RenumberedBy.renames {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) :
    Renames f g (List.range m₁.atoms.length) (List.range m₂.atoms.length) m₁.entry m₂.entry := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have := h.forth a (List.mem_range.1 ha)
    exact ⟨List.mem_range.2 this.1, this.2⟩
  · intro b hb
    have := h.back b (List.mem_range.1 hb)
    exact ⟨List.mem_range.2 this.1, this.2⟩
  · intro p a hp ha hnot
    have ha' := List.mem_range.1 ha
    simp only [Mol.entry, Mol.row_eq]
    congr 1
    · congr 1
      · rw [← List.map_reverse, List.map_map]
        apply List.map_inj_left.2
        intro i hi
        have hi' : i < m₁.atoms.length := List.mem_range.1 (hp.2 i (List.mem_reverse.1 hi))
        simp only [Function.comp, Mol.bondCode]
        rw [h.orderBetween w₁ w₂ hi' ha']
      · rw [h.atoms a ha']
    · -- at the last place: the stereo facts of the same `Mol`
      have hlen : m₁.atoms.length = m₂.atoms.length := Nat.le_antisymm h.length_le h.symm.length_le
      rw [h.hasStereo_eq w₁ w₂, ← hlen, List.length_map]
      by_cases hlast : p.length + 1 = m₁.atoms.length
      · have ho : IsOrderOf m₁.atoms.length (p ++ [a]) := by
          refine ⟨?_, ?_, by simp [hlast]⟩
          · exact List.pairwise_append.2 ⟨hp.1, List.pairwise_singleton _ _, fun x hx y hy => by
              simp only [List.mem_singleton] at hy
              subst hy
              exact fun e => hnot (e ▸ hx)⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact List.mem_range.1 (hp.2 x hx)
            · simp only [List.mem_singleton] at hx
              subst hx
              exact ha'
        have hmap : p.map f ++ [f a] = (p ++ [a]).map f := by simp
        rw [hmap, h.arrange_map w₁ w₂ ho]
      · have hfalse : (p.length + 1 == m₁.atoms.length) = false := by simpa using hlast
        simp only [hfalse, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-! ## Atoms that can be exchanged -/

theorem Mol.orderBetween_comm (m : Mol) (i j : Nat) : m.orderBetween i j = m.orderBetween j i := by
  unfold Mol.orderBetween
  congr 2
  funext b
  exact Bool.or_comm _ _

theorem Mol.orderBetween_self {m : Mol} (w : m.WellFormed) (i : Nat) :
    m.orderBetween i i = none := by
  unfold Mol.orderBetween
  have : m.bonds.find? (fun b => (b.a == i && b.b == i) || (b.a == i && b.b == i)) = none := by
    rw [List.find?_eq_none]
    intro b hb hp
    have := (w.1 b hb).1
    simp only [Bool.or_self, Bool.and_eq_true, beq_iff_eq] at hp
    omega
  rw [this]
  rfl

/-- A bond between `x` and `a` is one of the bonds at `a`, and `x` is its other
end. -/
theorem Mol.exists_bondsAt {m : Mol} {x a : Nat} {o : BondOrder} (h : m.orderBetween x a = some o)
    (hne : x ≠ a) : ∃ bond ∈ m.bondsAt a, bond.other a = x := by
  unfold Mol.orderBetween at h
  cases hfind : m.bonds.find? (fun b => (b.a == x && b.b == a) || (b.a == a && b.b == x)) with
  | none => simp [hfind] at h
  | some bond =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨bond, ?_, ?_⟩
    · unfold Mol.bondsAt
      rw [List.mem_filter]
      refine ⟨hmem, ?_⟩
      rcases hp with ⟨_, h2⟩ | ⟨h1, _⟩
      · simp [h2]
      · simp [h1]
    · unfold Bond.other
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hfalse : (bond.a == a) = false := by
          rw [h1]
          simpa using hne
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
        exact h1
      · have htrue : (bond.a == a) = true := by simpa using h1
        simp only [htrue, ↓reduceIte]
        exact h2

/-- The other end of a bond at `a` in a well formed `Mol` is another atom of
the `Mol`. -/
theorem Mol.other_of_bondsAt {m : Mol} (w : m.WellFormed) {a : Nat} {bond : Bond}
    (h : bond ∈ m.bondsAt a) : bond.other a ≠ a ∧ bond.other a < m.atoms.length := by
  unfold Mol.bondsAt at h
  rw [List.mem_filter] at h
  obtain ⟨hmem, hat⟩ := h
  obtain ⟨hlt, hb⟩ := w.1 bond hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at hat
  unfold Bond.other
  by_cases h1 : bond.a = a
  · simp only [h1, beq_self_eq_true, ↓reduceIte]
    constructor
    · omega
    · exact hb
  · have h2 : bond.b = a := by
      rcases hat with h | h
      · exact absurd h h1
      · exact h
    have h1' : (bond.a == a) = false := by simpa using h1
    simp only [h1', Bool.false_eq_true, ↓reduceIte]
    constructor
    · exact h1
    · omega

/-- What `twinsFrom` says, for a well formed `Mol`: they are two atoms of the
`Mol` with the same element, isotope, charge and hydrogens, and each is bonded
to every third atom exactly as the other is. -/
theorem Mol.twinsFrom_iff {m : Mol} (w : m.WellFormed) (a b : Nat) :
    twinsFrom a m.atoms[a]? (m.bondsAt a) b m.atoms[b]? (m.bondsAt b) = true ↔
      a ≠ b ∧ a < m.atoms.length ∧ m.atoms[a]? = m.atoms[b]? ∧
      ∀ x, x < m.atoms.length → x ≠ a → x ≠ b → m.orderBetween a x = m.orderBetween b x := by
  have hcode : ∀ x, (bondCodeAmong (m.bondsAt a) x a == bondCodeAmong (m.bondsAt b) x b) = true ↔
      m.orderBetween x a = m.orderBetween x b := by
    intro x
    rw [beq_iff_eq, Mol.bondCodeAmong_bondsAt, Mol.bondCodeAmong_bondsAt]
    constructor
    · exact Mol.orderBetween_of_bondCode
    · intro h
      unfold Mol.bondCode
      rw [h]
  unfold twinsFrom
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hne, hsome⟩, hatoms⟩, hall₁⟩, hall₂⟩
    have hne' : a ≠ b := by simpa using hne
    have ha : a < m.atoms.length := by
      rcases Nat.lt_or_ge a m.atoms.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hsome
        cases hsome
    have hatoms' : m.atoms[a]? = m.atoms[b]? := by simpa using hatoms
    refine ⟨hne', ha, hatoms', ?_⟩
    intro x hx hxa hxb
    rw [m.orderBetween_comm a x, m.orderBetween_comm b x]
    cases h1 : m.orderBetween x a with
    | some o =>
      obtain ⟨bond, hbond, hother⟩ := Mol.exists_bondsAt h1 hxa
      have := hall₁ bond hbond
      rw [hother, Bool.or_eq_true] at this
      rcases this with e | e
      · exact absurd (by simpa using e) hxb
      · rw [← h1]
        exact (hcode x).1 e
    | none =>
      cases h2 : m.orderBetween x b with
      | none => rfl
      | some o =>
        obtain ⟨bond, hbond, hother⟩ := Mol.exists_bondsAt h2 hxb
        have := hall₂ bond hbond
        rw [hother, Bool.or_eq_true] at this
        rcases this with e | e
        · exact absurd (by simpa using e) hxa
        · rw [← h1, ← h2]
          exact (hcode x).1 e
  · rintro ⟨hne, ha, hatoms, hbonds⟩
    refine ⟨⟨⟨⟨by simpa using hne, by simp [List.getElem?_eq_getElem ha]⟩, by simpa using hatoms⟩,
      ?_⟩, ?_⟩
    · intro bond hbond
      obtain ⟨hxa, hx⟩ := Mol.other_of_bondsAt w hbond
      rw [Bool.or_eq_true]
      by_cases hxb : bond.other a = b
      · left
        simpa using hxb
      · right
        rw [hcode, m.orderBetween_comm _ a, m.orderBetween_comm _ b]
        exact hbonds _ hx hxa hxb
    · intro bond hbond
      obtain ⟨hxb, hx⟩ := Mol.other_of_bondsAt w hbond
      rw [Bool.or_eq_true]
      by_cases hxa : bond.other b = a
      · left
        simpa using hxa
      · right
        rw [hcode, m.orderBetween_comm _ a, m.orderBetween_comm _ b]
        exact hbonds _ hx hxa hxb

/-- When an atom takes part in a stereo fact. -/
theorem Mol.inStereoFact_iff {m : Mol} {atom : Nat} :
    m.inStereoFact atom = true ↔
      (∃ x ∈ m.orientations, x.atom = atom ∨ atom ∈ m.neighbours x.atom) ∨
      (∃ x ∈ m.geometries,
        x.a = atom ∨ x.b = atom ∨ atom ∈ m.neighbours x.a ∨ atom ∈ m.neighbours x.b) := by
  simp [Mol.inStereoFact, or_assoc]

/-- An atom that takes part in no stereo fact has no orientation, is no
neighbour of an atom with one, is no atom of a double bond with a geometry,
and is no neighbour of such an atom. -/
theorem Mol.not_inStereoFact {m : Mol} {atom : Nat} (h : m.inStereoFact atom = false) :
    (∀ x ∈ m.orientations, x.atom ≠ atom ∧ atom ∉ m.neighbours x.atom) ∧
    (∀ x ∈ m.geometries,
      x.a ≠ atom ∧ x.b ≠ atom ∧ atom ∉ m.neighbours x.a ∧ atom ∉ m.neighbours x.b) := by
  have hnot : ¬ m.inStereoFact atom = true := by
    rw [h]
    exact Bool.false_ne_true
  rw [Mol.inStereoFact_iff] at hnot
  constructor
  · intro x hx
    exact ⟨fun e => hnot (Or.inl ⟨x, hx, Or.inl e⟩), fun e => hnot (Or.inl ⟨x, hx, Or.inr e⟩)⟩
  · intro x hx
    exact ⟨fun e => hnot (Or.inr ⟨x, hx, Or.inl e⟩),
      fun e => hnot (Or.inr ⟨x, hx, Or.inr (Or.inl e)⟩),
      fun e => hnot (Or.inr ⟨x, hx, Or.inr (Or.inr (Or.inl e))⟩),
      fun e => hnot (Or.inr ⟨x, hx, Or.inr (Or.inr (Or.inr e))⟩)⟩

/-- What `Mol.twins` says, for a well formed `Mol`: neither atom takes part in
a stereo fact, they are two atoms of the `Mol` with the same element, isotope,
charge and hydrogens, and each is bonded to every third atom exactly as the
other is. -/
theorem Mol.twins_iff {m : Mol} (w : m.WellFormed) (a b : Nat) :
    m.twins a b = true ↔ m.inStereoFact a = false ∧ m.inStereoFact b = false ∧
      a ≠ b ∧ a < m.atoms.length ∧ m.atoms[a]? = m.atoms[b]? ∧
      ∀ x, x < m.atoms.length → x ≠ a → x ≠ b → m.orderBetween a x = m.orderBetween b x := by
  unfold Mol.twins
  rw [Bool.and_eq_true, Bool.and_eq_true, Mol.twinsFrom_iff w]
  simp only [Bool.not_eq_true', and_assoc]

theorem Mol.twins_lt {m : Mol} (w : m.WellFormed) {a b : Nat} (h : m.twins a b = true) :
    b < m.atoms.length := by
  obtain ⟨_, _, _, ha, hatoms, _⟩ := (Mol.twins_iff w a b).1 h
  apply Classical.byContradiction
  intro hb
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_none (by omega)] at hatoms
  cases hatoms

theorem Mol.twins_symm {m : Mol} (w : m.WellFormed) {a b : Nat} (h : m.twins a b = true) :
    m.twins b a = true := by
  have hb := Mol.twins_lt w h
  obtain ⟨hsa, hsb, hne, _, hatoms, hbonds⟩ := (Mol.twins_iff w a b).1 h
  exact (Mol.twins_iff w b a).2 ⟨hsb, hsa, fun e => hne e.symm, hb, hatoms.symm,
    fun x hx hxb hxa => (hbonds x hx hxa hxb).symm⟩

theorem Mol.twins_trans {m : Mol} (w : m.WellFormed) {a b c : Nat} (hab : m.twins a b = true)
    (hbc : m.twins b c = true) (hac : a ≠ c) : m.twins a c = true := by
  have hc := Mol.twins_lt w hbc
  obtain ⟨hsa, _, hneab, ha, hatoms₁, hbonds₁⟩ := (Mol.twins_iff w a b).1 hab
  obtain ⟨_, hsc, hnebc, hb, hatoms₂, hbonds₂⟩ := (Mol.twins_iff w b c).1 hbc
  refine (Mol.twins_iff w a c).2 ⟨hsa, hsc, hac, ha, hatoms₁.trans hatoms₂, fun x hx hxa hxc => ?_⟩
  by_cases hxb : x = b
  · subst hxb
    -- a to b is as b to a, as c to a, as a to c, as b to c, as c to b
    rw [m.orderBetween_comm a x, hbonds₂ a ha hneab hac, m.orderBetween_comm c a,
      hbonds₁ c hc (fun e => hac e.symm) (fun e => hnebc e.symm)]
    exact m.orderBetween_comm _ _
  · rw [hbonds₁ x hx hxa hxb, hbonds₂ x hx hxb hxc]

/-- Exchanging two twins changes no bond. -/
theorem Mol.orderBetween_swapOf {m : Mol} (w : m.WellFormed) {a b : Nat} (h : m.twins a b = true)
    {i j : Nat} (hi : i < m.atoms.length) (hj : j < m.atoms.length) :
    m.orderBetween (swapOf a b i) (swapOf a b j) = m.orderBetween i j := by
  obtain ⟨_, _, hne, _, _, hbonds⟩ := (Mol.twins_iff w a b).1 h
  have hbonds' := ((Mol.twins_iff w b a).1 (Mol.twins_symm w h)).2.2.2.2.2
  unfold swapOf
  by_cases hia : i = a
  · by_cases hja : j = a
    · subst hia hja
      simp [Mol.orderBetween_self w]
    · by_cases hjb : j = b
      · subst hia hjb
        simp only [↓reduceIte, hja]
        exact m.orderBetween_comm _ _
      · subst hia
        simp only [↓reduceIte, hja, hjb]
        exact hbonds' j hj hjb hja
  · by_cases hib : i = b
    · by_cases hja : j = a
      · subst hib hja
        simp only [hia, ↓reduceIte]
        exact m.orderBetween_comm _ _
      · by_cases hjb : j = b
        · subst hib hjb
          simp [Mol.orderBetween_self w, hia]
        · subst hib
          simp only [hia, ↓reduceIte, hja, hjb]
          exact hbonds j hj hja hjb
    · by_cases hja : j = a
      · subst hja
        simp only [hia, hib, ↓reduceIte]
        rw [m.orderBetween_comm i b, m.orderBetween_comm i j]
        exact hbonds' i hi hib hia
      · by_cases hjb : j = b
        · subst hjb
          simp only [hia, hib, ↓reduceIte, hja]
          rw [m.orderBetween_comm i a, m.orderBetween_comm i j]
          exact hbonds i hi hia hib
        · simp only [hia, hib, ↓reduceIte, hja, hjb]

/-- So exchanging two twins gives the same `Mol`. The two take part in no
stereo fact, so every stored mark stays what it is. -/
theorem Mol.renumberedBy_swapOf {m : Mol} (w : m.WellFormed) {a b : Nat} (h : m.twins a b = true) :
    Mol.RenumberedBy (swapOf a b) (swapOf a b) m m := by
  have hb := Mol.twins_lt w h
  obtain ⟨hsa, hsb, hne, ha, hatoms, _⟩ := (Mol.twins_iff w a b).1 h
  have hswap : ∀ i, i < m.atoms.length →
      swapOf a b i < m.atoms.length ∧ swapOf a b (swapOf a b i) = i := by
    intro i hi
    unfold swapOf
    by_cases hia : i = a
    · subst hia
      have : ¬ b = i := fun e => hne e.symm
      simp [this, hb]
    · by_cases hib : i = b
      · subst hib
        simp [hia, ha]
      · simp [hia, hib, hi]
  have hgraph : Mol.SameGraphBy (swapOf a b) (swapOf a b) m m := by
    refine ⟨hswap, hswap, ?_, ?_⟩
    · intro i _
      unfold swapOf
      by_cases hia : i = a
      · subst hia
        simp only [↓reduceIte]
        exact hatoms.symm
      · by_cases hib : i = b
        · subst hib
          simp only [hia, ↓reduceIte]
          exact hatoms
        · simp only [hia, hib, ↓reduceIte]
    · intro i j order hi hj
      constructor
      · intro hjoined
        apply Mol.joined_of_orderBetween
        rw [Mol.orderBetween_swapOf w h hi hj]
        exact Mol.orderBetween_of_joined w hjoined
      · intro hjoined
        apply Mol.joined_of_orderBetween
        rw [← Mol.orderBetween_swapOf w h hi hj]
        exact Mol.orderBetween_of_joined w hjoined
  obtain ⟨hoa, hga⟩ := Mol.not_inStereoFact hsa
  obtain ⟨hob, hgb⟩ := Mol.not_inStereoFact hsb
  -- an atom that is neither of the two keeps its number
  have hfix : ∀ i, i ≠ a → i ≠ b → swapOf a b i = i := by
    intro i hia hib
    simp [swapOf, hia, hib]
  -- and an atom whose new number is neither of the two is neither of the two
  have hfixed : ∀ i, swapOf a b i ≠ a → swapOf a b i ≠ b → swapOf a b i = i := by
    intro i hia hib
    by_cases e1 : i = a
    · subst e1
      simp [swapOf] at hib
    · by_cases e2 : i = b
      · subst e2
        simp [swapOf, e1] at hia
      · exact hfix i e1 e2
  refine Mol.RenumberedBy.of_stored hgraph w w ?_ ?_
  · intro j hj
    cases hs : m.orientationAt j with
    | some s =>
      have hx := (Mol.orientationAt_eq_some w).1 hs
      have hja : j ≠ a := (hoa _ hx).1
      have hjb : j ≠ b := (hob _ hx).1
      have hplaces : (m.places j).map (Option.map (swapOf a b)) = m.places j := by
        have hsame : ∀ p ∈ m.places j, Option.map (swapOf a b) p = id p := by
          intro p hp
          cases p with
          | none => rfl
          | some x =>
            have hxn := Mol.mem_places.1 hp
            have hxa : x ≠ a := fun e => (hoa _ hx).2 (e ▸ hxn)
            have hxb : x ≠ b := fun e => (hob _ hx).2 (e ▸ hxn)
            simp [hfix x hxa hxb]
        rw [List.map_congr_left hsame, List.map_id]
      rw [hfix j hja hjb, hplaces, Mol.orientationOf_places w.graph, hs]
    | none =>
      have hnone : m.orientationAt (swapOf a b j) = none := by
        cases hs' : m.orientationAt (swapOf a b j) with
        | none => rfl
        | some s' =>
          exfalso
          have hx := (Mol.orientationAt_eq_some w).1 hs'
          have h1 : swapOf a b j ≠ a := (hoa _ hx).1
          have h2 : swapOf a b j ≠ b := (hob _ hx).1
          rw [hfixed j h1 h2, hs] at hs'
          cases hs'
      unfold Mol.orientationOf
      rw [hnone]
  · intro bond hbond x y hx hy
    obtain ⟨hab, hblt⟩ := w.1 bond hbond
    cases hs : m.geometryAt bond.a bond.b with
    | some s =>
      have he := (Mol.geometryAt_eq_some w).1 hs
      obtain ⟨h1, h2, h3, h4⟩ := hga _ he
      obtain ⟨h1', h2', h3', h4'⟩ := hgb _ he
      simp only at h1 h2 h3 h4 h1' h2' h3' h4'
      have hxn := (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hx)).1
      have hyn := (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hy)).1
      rw [hfix _ h1 h1', hfix _ h2 h2', hfix x (fun e => h3 (e ▸ hxn)) (fun e => h3' (e ▸ hxn)),
        hfix y (fun e => h4 (e ▸ hyn)) (fun e => h4' (e ▸ hyn)), Mol.geometryOf_heads hab hx hy, hs]
    | none =>
      have hnone : m.geometryAt (min (swapOf a b bond.a) (swapOf a b bond.b))
          (max (swapOf a b bond.a) (swapOf a b bond.b)) = none := by
        cases hs' : m.geometryAt (min (swapOf a b bond.a) (swapOf a b bond.b))
            (max (swapOf a b bond.a) (swapOf a b bond.b)) with
        | none => rfl
        | some s' =>
          exfalso
          have he := (Mol.geometryAt_eq_some w).1 hs'
          obtain ⟨h1, h2, -, -⟩ := hga _ he
          obtain ⟨h1', h2', -, -⟩ := hgb _ he
          simp only at h1 h2 h1' h2'
          have hboth : swapOf a b bond.a ≠ a ∧ swapOf a b bond.a ≠ b ∧
              swapOf a b bond.b ≠ a ∧ swapOf a b bond.b ≠ b := by
            rcases Nat.le_total (swapOf a b bond.a) (swapOf a b bond.b) with hle | hle
            · rw [Nat.min_eq_left hle] at h1 h1'
              rw [Nat.max_eq_right hle] at h2 h2'
              exact ⟨h1, h1', h2, h2'⟩
            · rw [Nat.min_eq_right hle] at h1 h1'
              rw [Nat.max_eq_left hle] at h2 h2'
              exact ⟨h2, h2', h1, h1'⟩
          rw [hfixed _ hboth.1 hboth.2.1, hfixed _ hboth.2.2.1 hboth.2.2.2,
            Nat.min_eq_left (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt hab), hs] at hs'
          cases hs'
      unfold Mol.geometryOf
      rw [hnone]

/-- The twins of a well formed `Mol` are twins for its search. -/
theorem Mol.twins_isTwins {m : Mol} (w : m.WellFormed) :
    Twins (List.range m.atoms.length) m.entry m.twins where
  symm := fun _ _ h => Mol.twins_symm w h
  trans := fun _ _ _ h₁ h₂ hne => Mol.twins_trans w h₁ h₂ hne
  swap := fun _ _ _ h => (Mol.renumberedBy_swapOf w h).renames w w

/-- An atom that takes part in a stereo fact still does when the atoms are
numbered differently. -/
theorem Mol.RenumberedBy.inStereoFact {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) {a : Nat}
    (ha : a < m₁.atoms.length) (hs : m₁.inStereoFact a = true) : m₂.inStereoFact (f a) = true := by
  rw [Mol.inStereoFact_iff] at hs ⊢
  rcases hs with ⟨x, hx, hat⟩ | ⟨x, hx, hat⟩
  · left
    obtain ⟨atom, o⟩ := x
    simp only at hat
    have hlt := Mol.orientation_lt w₁ hx
    simp only at hlt
    obtain ⟨s, hs₂⟩ := h.orientationAt_some w₁ ((Mol.orientationAt_eq_some w₁).2 hx)
    refine ⟨⟨f atom, s⟩, (Mol.orientationAt_eq_some w₂).1 hs₂, ?_⟩
    rcases hat with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr ((h.sameGraph.mem_neighbours hlt ha).2 e)
  · right
    obtain ⟨p, q, s⟩ := x
    simp only at hat
    have hat' := (Mol.geometryAt_eq_some w₁).2 hx
    obtain ⟨t, ht⟩ := h.geometryAt_some w₁ hat'
    obtain ⟨hpq, hqlt⟩ := w₁.1 _ (Mol.canHave_of_geometryAt w₁ hat').2
    simp only at hpq hqlt
    have hplt : p < m₁.atoms.length := by omega
    refine ⟨⟨_, _, t⟩, (Mol.geometryAt_eq_some w₂).1 ht, ?_⟩
    simp only
    have hp := h.sameGraph.mem_neighbours (x := a) hplt ha
    have hq := h.sameGraph.mem_neighbours (x := a) hqlt ha
    rcases Nat.le_total (f p) (f q) with hle | hle
    · rw [Nat.min_eq_left hle, Nat.max_eq_right hle]
      rcases hat with e | e | e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (Or.inl (by rw [e]))
      · exact Or.inr (Or.inr (Or.inl (hp.2 e)))
      · exact Or.inr (Or.inr (Or.inr (hq.2 e)))
    · rw [Nat.min_eq_right hle, Nat.max_eq_left hle]
      rcases hat with e | e | e | e
      · exact Or.inr (Or.inl (by rw [e]))
      · exact Or.inl (by rw [e])
      · exact Or.inr (Or.inr (Or.inr (hp.2 e)))
      · exact Or.inr (Or.inr (Or.inl (hq.2 e)))

/-- Twins stay twins when the atoms are numbered differently. -/
theorem Mol.RenumberedBy.twins {f g : Nat → Nat} {m₁ m₂ : Mol} (h : Mol.RenumberedBy f g m₁ m₂)
    (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) {a b : Nat} (ha : a < m₁.atoms.length)
    (hb : b < m₁.atoms.length) (ht : m₁.twins a b = true) : m₂.twins (f a) (f b) = true := by
  obtain ⟨hsa, hsb, hne, _, hatoms, hbonds⟩ := (Mol.twins_iff w₁ a b).1 ht
  refine (Mol.twins_iff w₂ (f a) (f b)).2 ⟨?_, ?_, ?_, (h.forth a ha).1, ?_, ?_⟩
  · cases hs : m₂.inStereoFact (f a) with
    | false => rfl
    | true =>
      have := h.symm.inStereoFact w₂ w₁ (h.forth a ha).1 hs
      rw [(h.forth a ha).2, hsa] at this
      cases this
  · cases hs : m₂.inStereoFact (f b) with
    | false => rfl
    | true =>
      have := h.symm.inStereoFact w₂ w₁ (h.forth b hb).1 hs
      rw [(h.forth b hb).2, hsb] at this
      cases this
  · intro e
    apply hne
    rw [← (h.forth a ha).2, e, (h.forth b hb).2]
  · rw [h.atoms a ha, h.atoms b hb]
    exact hatoms
  · intro y hy hya hyb
    obtain ⟨hgy, hfgy⟩ := h.back y hy
    have hne_a : g y ≠ a := fun e => hya (by rw [← hfgy, e])
    have hne_b : g y ≠ b := fun e => hyb (by rw [← hfgy, e])
    rw [← hfgy, h.orderBetween w₁ w₂ ha hgy, h.orderBetween w₁ w₂ hb hgy]
    exact hbonds (g y) hgy hne_a hne_b

/-! ## Beginnings that are alike -/

/-- Every entry of `placedCodes` has a place from `place` on. -/
theorem placedCodes_ge : ∀ (l : List Nat) (place : Nat),
    ∀ e ∈ placedCodes place l, place ≤ e.headD 0
  | [], _, e, h => by simp [placedCodes] at h
  | code :: rest, place, e, h => by
    unfold placedCodes at h
    split at h
    · have := placedCodes_ge rest (place + 1) e h
      omega
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_refl _
      · have := placedCodes_ge rest (place + 1) e h
        omega

/-- Two rows of the same length with the same bonded entries at the same
places are the same row. -/
theorem placedCodes_inj : ∀ (l l' : List Nat) (place : Nat), l.length = l'.length →
    placedCodes place l = placedCodes place l' → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | c :: rest, c' :: rest', place, hlen, h => by
    have hlen' : rest.length = rest'.length := by simpa using hlen
    unfold placedCodes at h
    by_cases hc : c = 5
    · by_cases hc' : c' = 5
      · simp only [hc, hc', ↓reduceIte] at h
        rw [hc, hc', placedCodes_inj rest rest' (place + 1) hlen' h]
      · simp only [hc, hc', ↓reduceIte] at h
        have h1 : place + 1 ≤ place :=
          placedCodes_ge rest (place + 1) [place, c'] (by rw [h]; exact List.mem_cons_self ..)
        omega
    · by_cases hc' : c' = 5
      · simp only [hc, hc', ↓reduceIte] at h
        have h1 : place + 1 ≤ place :=
          placedCodes_ge rest' (place + 1) [place, c] (by rw [← h]; exact List.mem_cons_self ..)
        omega
      · simp only [hc, hc', ↓reduceIte, List.cons.injEq, true_and, and_true] at h
        rw [h.1, placedCodes_inj rest rest' (place + 1) hlen' h.2]

theorem Mol.length_row (m : Mol) (done : List Nat) (a : Nat) :
    (m.row done a).length = done.length := by
  simp [Mol.row]

/-- The row of an atom, when one atom more stands before it. -/
theorem Mol.row_append (m : Mol) (done : List Nat) (b a : Nat) :
    m.row (done ++ [b]) a = bondCodeAmong (m.bondsAt a) b a :: m.row done a := by
  simp [Mol.row]

theorem Mol.outline_of_stereo {m : Mol} (h : m.hasStereo = true) : m.outline = none := by
  simp [Mol.outline, h]

theorem Mol.outline_of_no_stereo {m : Mol} (h : m.hasStereo = false) :
    m.outline = some m.outlineOf := by
  simp [Mol.outline, h]

/-- Two beginnings of the same length have the same outline exactly when they
are alike (SPEC.md, section 3.2): they have placed the same atoms, and every
atom that is not placed has the same row for both. -/
theorem Mol.outlineOf_eq_iff (m : Mol) {p q : List Nat} (hlen : p.length = q.length) :
    m.outlineOf p = m.outlineOf q ↔
      ∀ u, u < m.atoms.length → (u ∈ p ↔ u ∈ q) ∧ (u ∉ p → m.row p u = m.row q u) := by
  unfold Mol.outlineOf
  rw [List.map_inj_left]
  constructor
  · intro h u hu
    have hu' := h u (List.mem_range.2 hu)
    by_cases hp : u ∈ p
    · by_cases hq : u ∈ q
      · exact ⟨⟨fun _ => hq, fun _ => hp⟩, fun hn => absurd hp hn⟩
      · simp [hp, hq] at hu'
    · by_cases hq : u ∈ q
      · simp [hp, hq] at hu'
      · simp only [List.contains_eq_mem, hp, hq, decide_false, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at hu'
        refine ⟨⟨fun h => absurd h hp, fun h => absurd h hq⟩, fun _ => ?_⟩
        exact placedCodes_inj _ _ 0 (by rw [m.length_row, m.length_row, hlen]) hu'
  · intro h u hu
    obtain ⟨hmem, hrow⟩ := h u (List.mem_range.1 hu)
    by_cases hp : u ∈ p
    · have hq := hmem.1 hp
      simp [hp, hq]
    · have hq : u ∉ q := fun hq => hp (hmem.2 hq)
      simp [hp, hq, hrow hp]

/-- The outlines of a `Mol` do what the search needs of outlines (`Merges` in
`VeriMol/Proofs/Search.lean`). For a `Mol` with stereo facts the search takes no
outlines, and nothing is asked. -/
theorem Mol.merges (m : Mol) :
    Merges (List.range m.atoms.length) (tieBreak m.entry m.twins) m.outline := by
  cases hs : m.hasStereo with
  | true =>
    rw [Mol.outline_of_stereo hs]
    exact Merges.none _ _
  | false =>
    rw [Mol.outline_of_no_stereo hs]
    refine ⟨?_⟩
    intro p q a hp hq hlen hsame ha hnot
    have hsame' : m.outlineOf p = m.outlineOf q := hsame
    have hchar := (m.outlineOf_eq_iff hlen).1 hsame'
    have ha' := List.mem_range.1 ha
    obtain ⟨hmem_a, hrow_a⟩ := hchar a ha'
    have hnotq : a ∉ q := fun h => hnot (hmem_a.2 h)
    refine ⟨hnotq, ?_, ?_⟩
    · show (m.entry q a, waiting m.twins q a) = (m.entry p a, waiting m.twins p a)
      congr 1
      · simp only [Mol.entry, hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrow_a hnot]
      · apply waiting_congr
        rw [waiting_eq_zero_iff, waiting_eq_zero_iff]
        constructor
        · intro H b hb ht
          exact (hchar b (by omega)).1.2 (H b hb ht)
        · intro H b hb ht
          exact (hchar b (by omega)).1.1 (H b hb ht)
    · show m.outlineOf (p ++ [a]) = m.outlineOf (q ++ [a])
      rw [m.outlineOf_eq_iff (by simp [hlen])]
      intro u hu
      obtain ⟨hmem, hrow⟩ := hchar u hu
      refine ⟨by simp [hmem], ?_⟩
      intro hnu
      have hnu' : u ∉ p := fun h => hnu (List.mem_append_left _ h)
      rw [Mol.row_append, Mol.row_append, hrow hnu']

/-- The atoms of one `Mol` are renamed into those of another so that the
entries agree, and both `Mol`s have stereo facts or neither has. Then two
beginnings of the same length whose renamed forms count as the same for the
search of the second `Mol` (`Same`) count as the same for the search of the
first. -/
theorem Mol.same_outline_of_renames {m₁ m₂ : Mol} {F G : Nat → Nat} {n : Nat}
    (hn₁ : m₁.atoms.length = n) (hn₂ : m₂.atoms.length = n) (hs : m₁.hasStereo = m₂.hasStereo)
    (hR : Renames F G (List.range n) (List.range n) m₁.entry m₂.entry) {p p' : List Nat}
    (hp : IsBeginning (List.range n) p) (hp' : IsBeginning (List.range n) p')
    (hlen : p.length = p'.length) (h : Same m₂.outline (p.map F) (p'.map F)) :
    Same m₁.outline p p' := by
  cases hst : m₁.hasStereo with
  | true =>
    rw [Mol.outline_of_stereo (hs ▸ hst)] at h
    rw [Mol.outline_of_stereo hst]
    have h' : p.map F = p'.map F := h
    have := congrArg (List.map G) h'
    rw [hR.map_map hp, hR.map_map hp'] at this
    exact this
  | false =>
    rw [Mol.outline_of_no_stereo (hs ▸ hst)] at h
    rw [Mol.outline_of_no_stereo hst]
    have h' : m₂.outlineOf (p.map F) = m₂.outlineOf (p'.map F) := h
    show m₁.outlineOf p = m₁.outlineOf p'
    rw [m₁.outlineOf_eq_iff hlen]
    have hchar := (m₂.outlineOf_eq_iff (by simp [hlen])).1 h'
    intro u hu
    have hu' : u ∈ List.range n := List.mem_range.2 (hn₁ ▸ hu)
    obtain ⟨hFu, hGF⟩ := hR.forth u hu'
    obtain ⟨hmem, hrow⟩ := hchar (F u) (by rw [hn₂]; exact List.mem_range.1 hFu)
    have hin : ∀ {l : List Nat}, IsBeginning (List.range n) l → (F u ∈ l.map F ↔ u ∈ l) := by
      intro l hl
      constructor
      · intro hm
        obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
        have : x = u := by rw [← (hR.forth x (hl.2 x hx)).2, hxe, hGF]
        exact this ▸ hx
      · exact fun hm => List.mem_map.2 ⟨u, hm, rfl⟩
    refine ⟨⟨fun hm => (hin hp').1 (hmem.1 ((hin hp).2 hm)),
      fun hm => (hin hp).1 (hmem.2 ((hin hp').2 hm))⟩, ?_⟩
    intro hnu
    have hnu' : u ∉ p' := fun hm => hnu ((hin hp).1 (hmem.2 ((hin hp').2 hm)))
    have hrow' := hrow (fun hm => hnu ((hin hp).1 hm))
    -- the row of a renamed atom behind a renamed beginning is the row of the atom
    have hrows : ∀ {l : List Nat}, IsBeginning (List.range n) l → u ∉ l →
        m₂.row (l.map F) (F u) = m₁.row l u := by
      intro l hl hnl
      have he := hR.entry l u hl hu' hnl
      unfold Mol.entry at he
      rw [List.append_assoc, List.append_assoc] at he
      exact List.append_inj_left he (by simp [Mol.length_row])
    rw [← hrows hp hnu, ← hrows hp' hnu', hrow']

/-! ## The chosen form -/

/-- The table holds, for every atom, its twins with a smaller number. -/
theorem Mol.smallerTwins_getElem? (m : Mol) {a : Nat} (ha : a < m.atoms.length) :
    m.smallerTwins[a]? = some ((List.range a).filter (m.twins a)) := by
  unfold Mol.smallerTwins
  simp only [List.getElem?_map, List.getElem?_range ha, Option.map_some, Option.some.injEq]
  rw [← List.map_take, List.take_range, Nat.min_eq_left (Nat.le_of_lt ha), List.filter_map,
    List.map_map]
  have hid : ((fun x : Nat × Option Atom × List Bond × Bool => x.1) ∘
      fun a => (a, m.atoms[a]?, m.bondsAt a, m.inStereoFact a)) = id := rfl
  rw [hid, List.map_id]
  rfl

/-- The program looks the twins up in a table that it makes once. That gives
the entry with the tie-break. -/
theorem Mol.searchEntry_eq (m : Mol) {a : Nat} (ha : a < m.atoms.length) (done : List Nat) :
    m.searchEntry m.smallerTwins done a = tieBreak m.entry m.twins done a := by
  unfold Mol.searchEntry tieBreak
  congr 1
  unfold stillWaiting waiting
  rw [m.smallerTwins_getElem? ha]
  simp only [Option.getD_some, List.any_filter]

/-- The chosen order, said with the tie-break of `VeriMol/Proofs/Search.lean`
in the place of the table. -/
theorem Mol.chosenOrder_eq (m : Mol) :
    m.chosenOrder =
      (match searchWithin searchLimit (tieBreak m.entry m.twins) (lePair leEntry) m.outline
          (List.range m.atoms.length) m.atoms.length with
        | some (order :: _) => some order
        | _ => none) := by
  unfold Mol.chosenOrder
  rw [searchWithin_congr (lePair leEntry) m.outline (List.range m.atoms.length)
    (fun p a ha => m.searchEntry_eq (List.mem_range.1 ha) p) searchLimit m.atoms.length]
  rfl

/-- The chosen order is one of the orders that the search with the tie-break,
without a limit, ends with. -/
theorem Mol.chosenOrder_mem {m : Mol} {order : List Nat} (h : m.chosenOrder = some order) :
    order ∈ search (tieBreak m.entry m.twins) (lePair leEntry) m.outline
      (List.range m.atoms.length) m.atoms.length := by
  rw [Mol.chosenOrder_eq] at h
  split at h
  · rename_i first rest hs
    cases h
    rw [← searchWithin_eq _ _ _ _ _ _ _ hs]
    exact List.mem_cons_self ..
  · cases h

/-- There is a chosen order exactly when the search does not give up. -/
theorem Mol.chosenOrder_isSome (m : Mol) :
    m.chosenOrder.isSome =
      (searchWithin searchLimit (tieBreak m.entry m.twins) (lePair leEntry) m.outline
        (List.range m.atoms.length) m.atoms.length).isSome := by
  rw [Mol.chosenOrder_eq]
  cases hs : searchWithin searchLimit (tieBreak m.entry m.twins) (lePair leEntry) m.outline
      (List.range m.atoms.length) m.atoms.length with
  | none => rfl
  | some held =>
    have heq := searchWithin_eq _ _ _ _ _ _ _ hs
    have hne := (search_least (tieBreak m.entry m.twins) (lePair_isOrder leEntry_isOrder)
      m.merges List.nodup_range).1
    simp only [List.length_range] at hne
    rw [← heq] at hne
    cases held with
    | nil => exact absurd rfl hne
    | cons order rest => rfl

/-- What the search finds is the chosen form: well formed, the same molecule,
and first among all well formed `Mol`s that are the same molecule. The
tie-break does not change that (`Holds.least_of_tieBreak`). -/
theorem Mol.chosenForm_isChosenForm {m c : Mol} (w : m.WellFormed) (h : m.chosenForm = some c) :
    Mol.IsChosenForm Mol.noLaterThan m c := by
  unfold Mol.chosenForm at h
  cases ho : m.chosenOrder with
  | none => simp [ho] at h
  | some p =>
    rw [ho] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have ho' := lePair_isOrder leEntry_isOrder
    obtain ⟨_, hall⟩ := search_least (tieBreak m.entry m.twins) ho' m.merges List.nodup_range
    simp only [List.length_range] at hall
    obtain ⟨⟨⟨hnd, hsub⟩, hplen⟩, _⟩ := hall p (Mol.chosenOrder_mem ho)
    have hholds := search_holds (tieBreak m.entry m.twins) ho' m.merges List.nodup_range
      m.atoms.length (by simp)
    have hleast := hholds.least_of_tieBreak leEntry_isOrder (Mol.twins_isTwins w) p
      (Mol.chosenOrder_mem ho)
    have hp : IsOrderOf m.atoms.length p :=
      ⟨hnd, fun a ha => List.mem_range.1 (hsub a ha), hplen⟩
    obtain ⟨wa, hsame⟩ := Mol.renumbered_arrange w hp
    refine ⟨wa, hsame, ?_⟩
    intro c' wc' hc'
    obtain ⟨q, hq, rfl⟩ := Mol.eq_arrange_of_renumbered w wc' hc'
    apply le_of_noLater
    rw [Mol.key_arrange w hp, Mol.key_arrange w hq]
    exact hleast q ⟨hq.nodup, fun a ha => List.mem_range.2 (hq.below a ha)⟩ hq.length

/-- Theorem 23 of CLAIMS.md. The chosen form of a well formed `Mol` is the same
molecule as what went in, numbered differently. -/
theorem Mol.renumbered_chosenForm (m c : Mol) (w : m.WellFormed) (h : m.chosenForm = some c) :
    m.Renumbered c :=
  (Mol.chosenForm_isChosenForm w h).same

/-- Theorem 24 of CLAIMS.md. The chosen form of a well formed `Mol` is well
formed. -/
theorem Mol.chosenForm_wellFormed (m c : Mol) (w : m.WellFormed) (h : m.chosenForm = some c) :
    c.WellFormed :=
  (Mol.chosenForm_isChosenForm w h).wellFormed

/-- Theorem 25 of CLAIMS.md. The chosen form of a well formed `Mol` has the
least key. Take any well formed `Mol` that is the same molecule, numbered
differently: the key of the chosen form is not greater than the key of that
`Mol` (`Mol.noLaterThan`). The two keys have as many entries, so this says
that they are equal, or that at the first place where they differ, the entry
of the chosen form is the smaller one. -/
theorem Mol.chosenForm_least (m c : Mol) (w : m.WellFormed) (h : m.chosenForm = some c)
    (other : Mol) (wother : other.WellFormed) (hother : m.Renumbered other) :
    c.noLaterThan other :=
  (Mol.chosenForm_isChosenForm w h).first other wother hother

/-- Theorem 26 of CLAIMS.md. Two well formed `Mol`s that are the same molecule,
numbered differently, get the same chosen form, or the search gives up for
both. -/
theorem Mol.chosenForm_eq_of_renumbered (m₁ m₂ : Mol) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (h : m₁.Renumbered m₂) : m₁.chosenForm = m₂.chosenForm := by
  obtain ⟨f, g, hf⟩ := h
  have hlen : m₁.atoms.length = m₂.atoms.length := Nat.le_antisymm hf.length_le hf.symm.length_le
  have hTf : ∀ a b, a ∈ List.range m₁.atoms.length → b ∈ List.range m₁.atoms.length →
      m₂.twins (f a) (f b) = m₁.twins a b := by
    intro a b ha hb
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    apply Bool.eq_iff_iff.2
    constructor
    · intro ht
      have := hf.symm.twins w₂ w₁ (hf.forth a ha').1 (hf.forth b hb').1 ht
      rw [(hf.forth a ha').2, (hf.forth b hb').2] at this
      exact this
    · exact hf.twins w₁ w₂ ha' hb'
  have hsome : m₁.chosenForm.isSome = m₂.chosenForm.isSome := by
    simp only [Mol.chosenForm, Option.isSome_map, Mol.chosenOrder_isSome]
    -- the atoms can be renamed so that twins keep the order of their numbers: then the two
    -- searches are the same search under other names, tie-break and outlines included
    have hR := hf.renames w₁ w₂
    have hT₂ := Mol.twins_isTwins w₂
    have hM₂ := m₂.merges
    rw [← hlen] at hR hT₂ hM₂
    obtain ⟨F, G, hF, hFt⟩ := hT₂.exists_renaming hR
      (fun a b ha hb => hTf a b (List.mem_range.2 ha) (List.mem_range.2 hb))
    have hs := hf.hasStereo_eq w₁ w₂
    have := Renames.searchWithin_isSome (lePair_isOrder leEntry_isOrder) hFt m₁.merges hM₂
      (fun p p' hp hp' hl h => Mol.same_outline_of_renames rfl hlen.symm hs.symm hF hp hp' hl h)
      (fun q q' hq hq' hl h => Mol.same_outline_of_renames hlen.symm rfl hs hF.symm hq hq' hl h)
      List.nodup_range List.nodup_range rfl searchLimit m₁.atoms.length (by simp)
    rw [this, hlen]
  cases h₁ : m₁.chosenForm with
  | none =>
    cases h₂ : m₂.chosenForm with
    | none => rfl
    | some c₂ => rw [h₁, h₂] at hsome; cases hsome
  | some c₁ =>
    cases h₂ : m₂.chosenForm with
    | none => rw [h₁, h₂] at hsome; cases hsome
    | some c₂ =>
      exact congrArg some (Mol.IsChosenForm.unique Mol.noLaterThan_antisymm ⟨f, g, hf⟩
        (Mol.chosenForm_isChosenForm w₁ h₁) (Mol.chosenForm_isChosenForm w₂ h₂))

/-- Theorem 27 of CLAIMS.md. Let a well formed `Mol` have a chosen form. Then
another well formed `Mol` is the same molecule, numbered differently, exactly
when it has that chosen form. The second `Mol` need not be known to have a
chosen form: that it has one is part of what the theorem says. -/
theorem Mol.renumbered_iff_chosenForm_eq (m₁ m₂ c : Mol) (w₁ : m₁.WellFormed)
    (w₂ : m₂.WellFormed) (h : m₁.chosenForm = some c) :
    m₁.Renumbered m₂ ↔ m₂.chosenForm = some c := by
  constructor
  · intro hsame
    rw [← Mol.chosenForm_eq_of_renumbered m₁ m₂ w₁ w₂ hsame]
    exact h
  · intro h₂
    exact (Mol.renumbered_chosenForm m₁ c w₁ h).trans (Mol.renumbered_chosenForm m₂ c w₂ h₂).symm

/-- Theorem 28 of CLAIMS.md. The chosen form of the chosen form of a well
formed `Mol` is itself. -/
theorem Mol.chosenForm_chosenForm (m c : Mol) (w : m.WellFormed) (h : m.chosenForm = some c) :
    c.chosenForm = some c := by
  rw [← Mol.chosenForm_eq_of_renumbered m c w (Mol.chosenForm_wellFormed m c w h)
    (Mol.renumbered_chosenForm m c w h)]
  exact h

/-! ## The command `canonical` -/

/-- The command `canonical` is `rewritten` with the writer of the chosen form. -/
theorem run_canonical_rewritten (text : List Char) :
    run ["canonical".toList, text] = rewritten writeChosen text := by
  simp [run]

/-- `canonical` refuses a well formed `Mol` of more than 1,000 atoms, with the
message of SPEC.md, section 3.2, whatever the search would say. The number and
the message are written out here, so that this proof stops if the limit or the
message of the program is changed. -/
theorem writeChosen_of_large (mol : Mol) (w : mol.WellFormed) (h : 1000 < mol.atoms.length) :
    writeChosen mol = .error "the chosen form is not worked out: more than 1000 atoms".toList := by
  have hl : atomLimit < mol.atoms.length := h
  unfold writeChosen
  simp only [w, not_true_eq_false, ↓reduceIte, hl]
  rfl

/-- For a well formed `Mol` of at most 1,000 atoms the limit changes nothing:
`canonical` goes on with the search, and then with the writer. -/
theorem writeChosen_of_small (mol : Mol) (w : mol.WellFormed) (h : mol.atoms.length ≤ 1000) :
    writeChosen mol =
      match mol.chosenForm with
      | none => .error Message.searchGivesUp
      | some chosen => write chosen := by
  have hl : ¬ atomLimit < mol.atoms.length := Nat.not_lt.2 h
  unfold writeChosen
  simp only [w, not_true_eq_false, ↓reduceIte, hl]
  rfl

/-- A `Mol` and the same molecule, numbered differently, have as many atoms. -/
theorem Mol.Renumbered.length_eq {m₁ m₂ : Mol} (h : m₁.Renumbered m₂) :
    m₁.atoms.length = m₂.atoms.length := by
  obtain ⟨f, g, hfg⟩ := h
  obtain ⟨f', g', hgf⟩ := Mol.Renumbered.symm ⟨f, g, hfg⟩
  exact Nat.le_antisymm (Mol.RenumberedBy.length_le hfg) (Mol.RenumberedBy.length_le hgf)

/-- If `canonical` prints a text, the original text was read as some `Mol` of
at most `atomLimit` atoms, the `Mol` has a chosen form, and the printed text
is what the writer gives for it. -/
theorem rewritten_writeChosen {original written : List Char}
    (h : rewritten writeChosen original
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    ∃ mol chosen, read original = .ok mol ∧ ¬ atomLimit < mol.atoms.length ∧
      mol.chosenForm = some chosen ∧ write chosen = .ok written := by
  unfold rewritten at h
  cases hr : read original with
  | error problem => simp [hr, Output.error] at h
  | ok mol =>
    rw [hr] at h
    simp only at h
    unfold writeChosen at h
    have wf := read_wellFormed original mol hr
    simp only [wf, not_true_eq_false, ↓reduceIte] at h
    by_cases hl : atomLimit < mol.atoms.length
    · simp [hl, Output.error] at h
    · simp only [hl, ↓reduceIte] at h
      cases hc : mol.chosenForm with
      | none => simp [hc, Output.error] at h
      | some chosen =>
        rw [hc] at h
        simp only at h
        cases hw : write chosen with
        | error message => simp [hw, Output.error] at h
        | ok text =>
          rw [hw] at h
          simp only [Output.ok, Output.mk.injEq, and_true] at h
          have : text = written := by simpa using h
          exact ⟨mol, chosen, rfl, hl, hc, this ▸ hw⟩

/-- Theorem 29 of CLAIMS.md. If `canonical` prints a text, then the original
text is read as some `Mol`, that `Mol` has a chosen form (SPEC.md, section
3.2), the printed text is what the writer gives for the chosen form, and
reading the printed text returns the chosen form.

Theorems 30 to 33 say that `canonical` makes one choice for a molecule. This
one says which: the chosen form of the `Mol` that was read, which is the same
molecule with the least key (theorems 23 and 25, with theorem 8). -/
theorem run_canonical_is_chosenForm (original written : List Char)
    (h : run ["canonical".toList, original]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    ∃ mol chosen, read original = .ok mol ∧ mol.chosenForm = some chosen ∧
      write chosen = .ok written ∧ read written = .ok chosen := by
  rw [run_canonical_rewritten] at h
  obtain ⟨mol, chosen, hr, _, hc, hw⟩ := rewritten_writeChosen h
  exact ⟨mol, chosen, hr, hc, hw, read_write chosen written hw⟩

/-- Theorem 30 of CLAIMS.md. The text that `canonical` prints is read as the
same molecule as the original text, numbered differently. -/
theorem run_canonical_same_molecule (original written : List Char)
    (h : run ["canonical".toList, original]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    ∃ mol chosen, read original = .ok mol ∧ read written = .ok chosen ∧ mol.Renumbered chosen := by
  rw [run_canonical_rewritten] at h
  obtain ⟨mol, chosen, hr, _, hc, hw⟩ := rewritten_writeChosen h
  exact ⟨mol, chosen, hr, read_write chosen written hw,
    Mol.renumbered_chosenForm mol chosen (read_wellFormed original mol hr) hc⟩

/-- Theorem 32 of CLAIMS.md. Two texts that are read as the same molecule,
numbered differently, get the same answer from `canonical`: the same text, or
the same error. -/
theorem run_canonical_of_renumbered (t₁ t₂ : List Char) (m₁ m₂ : Mol)
    (h₁ : read t₁ = .ok m₁) (h₂ : read t₂ = .ok m₂) (h : m₁.Renumbered m₂) :
    run ["canonical".toList, t₁] = run ["canonical".toList, t₂] := by
  have w₁ := read_wellFormed t₁ m₁ h₁
  have w₂ := read_wellFormed t₂ m₂ h₂
  have hc := Mol.chosenForm_eq_of_renumbered m₁ m₂ w₁ w₂ h
  rw [run_canonical_rewritten, run_canonical_rewritten]
  simp only [rewritten, h₁, h₂, writeChosen, w₁, w₂, not_true_eq_false, ↓reduceIte, hc,
    h.length_eq]

/-- Theorem 31 of CLAIMS.md. If `canonical` prints a text for one text, it
prints that same text for a second text exactly when the two are read as the
same molecule, numbered differently. So for every text for which it prints a
text, `canonical` decides whether another text is the same molecule (SPEC.md,
section 3.1). The second text need not be known to get a text: that it does
is part of what the theorem says. -/
theorem run_canonical_eq_iff (t₁ t₂ written : List Char)
    (h : run ["canonical".toList, t₁]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    run ["canonical".toList, t₂] = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 } ↔
      ∃ m₁ m₂, read t₁ = .ok m₁ ∧ read t₂ = .ok m₂ ∧ m₁.Renumbered m₂ := by
  constructor
  · intro h₂
    rw [run_canonical_rewritten] at h h₂
    obtain ⟨m₁, c₁, hr₁, _, hc₁, hw₁⟩ := rewritten_writeChosen h
    obtain ⟨m₂, c₂, hr₂, _, hc₂, hw₂⟩ := rewritten_writeChosen h₂
    have hc : c₁ = c₂ := write_injective c₁ c₂ written hw₁ hw₂
    subst hc
    exact ⟨m₁, m₂, hr₁, hr₂,
      (Mol.renumbered_iff_chosenForm_eq m₁ m₂ c₁ (read_wellFormed t₁ m₁ hr₁)
        (read_wellFormed t₂ m₂ hr₂) hc₁).2 hc₂⟩
  · rintro ⟨m₁, m₂, hr₁, hr₂, hsame⟩
    rw [← run_canonical_of_renumbered t₁ t₂ m₁ m₂ hr₁ hr₂ hsame]
    exact h

/-- Theorem 33 of CLAIMS.md. `canonical` applied to its own output prints the
same text again. -/
theorem run_canonical_again (original written : List Char)
    (h : run ["canonical".toList, original]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    run ["canonical".toList, written] = run ["canonical".toList, original] := by
  rw [run_canonical_rewritten] at h
  rw [run_canonical_rewritten, run_canonical_rewritten]
  obtain ⟨mol, chosen, hr, hl, hc, hw⟩ := rewritten_writeChosen h
  have wf := read_wellFormed original mol hr
  have wfc := Mol.chosenForm_wellFormed mol chosen wf hc
  have hcc := Mol.chosenForm_chosenForm mol chosen wf hc
  have hrw := read_write chosen written hw
  have hlc : ¬ atomLimit < chosen.atoms.length := by
    rw [← (Mol.renumbered_chosenForm mol chosen wf hc).length_eq]
    exact hl
  rw [h]
  simp [rewritten, hrw, writeChosen, hcc, hw, wfc, hlc, Output.ok]

/-- Theorem 34 of CLAIMS.md. A text that `canonical` prints comes back
unchanged from `rewrite`: if `canonical` prints `written` for some text, then
`rewrite` prints `written` for `written`. The other way round it does not
hold: `canonical` prints `CCO` for `OCC` (theorem 44), and the tests show that
`rewrite` prints `OCC` for it. -/
theorem run_rewrite_of_canonical (original written : List Char)
    (h : run ["canonical".toList, original]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) :
    run ["rewrite".toList, written]
      = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 } := by
  obtain ⟨_, chosen, _, _, hwrite, hread⟩ := run_canonical_is_chosenForm original written h
  simp [run, rewritten, hread, hwrite, Output.ok]

/-- The atoms of a `Mol` that is another one numbered differently are atoms of
that other one. -/
theorem mem_atoms_of_renumbered {m c : Mol} (h : m.Renumbered c) :
    ∀ a ∈ c.atoms, a ∈ m.atoms := by
  obtain ⟨f, g, hf⟩ := h
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨hg, hfg⟩ := hf.back j hj
  have hat := hf.atoms (g j) hg
  rw [hfg, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hg] at hat
  rw [Option.some.inj hat]
  exact List.getElem_mem hg

/-- Theorem 35 of CLAIMS.md. For a text that is read as a `Mol` without stereo
facts, `canonical` prints a text, or one of three errors, and nothing else: the
`Mol` has more than 1,000 atoms; the search gives up; or the writer needs more
than 99 ring numbers for the chosen form. The theorem says which answers can
come. It does not say when each comes. (For a `Mol` with stereo facts the
writer has more reasons to refuse, SPEC.md, section 12.3.) -/
theorem run_canonical_of_read (text : List Char) (mol : Mol) (h : read text = .ok mol)
    (horientations : mol.orientations = []) (hgeometries : mol.geometries = []) :
    (∃ written, run ["canonical".toList, text]
        = { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }) ∨
      run ["canonical".toList, text]
        = { stdout := [],
            stderr := "error: the chosen form is not worked out: more than 1000 atoms\n".toList,
            exitCode := 1 } ∨
      run ["canonical".toList, text]
        = { stdout := [],
            stderr := ("error: the chosen form is not worked out: too many numberings of this "
              ++ "molecule look alike\n").toList,
            exitCode := 1 } ∨
      run ["canonical".toList, text]
        = { stdout := [],
            stderr := "error: more than 99 ring numbers are needed at the same time\n".toList,
            exitCode := 1 } := by
  have wf := read_wellFormed text mol h
  rw [run_canonical_rewritten]
  unfold rewritten
  simp only [h]
  by_cases hl : 1000 < mol.atoms.length
  · right; left
    rw [writeChosen_of_large mol wf hl]
    rfl
  · rw [writeChosen_of_small mol wf (Nat.not_lt.1 hl)]
    cases hc : mol.chosenForm with
    | none => right; right; left; rfl
    | some c =>
      have wfc := Mol.chosenForm_wellFormed mol c wf hc
      have hfine : ∀ a ∈ c.atoms, a.refusal = none := fun a ha =>
        read_no_refusal text mol h a
          (mem_atoms_of_renumbered (Mol.renumbered_chosenForm mol c wf hc) a ha)
      -- the chosen form has no stereo facts either
      have hnone : c.orientations = [] ∧ c.geometries = [] := by
        obtain ⟨f, g, hf⟩ := Mol.renumbered_chosenForm mol c wf hc
        apply Mol.noStereo_of_not_hasStereo
        rw [hf.hasStereo_eq wf wfc]
        simp [Mol.hasStereo, horientations, hgeometries]
      have hwrite : (∃ t, write c = .ok t) ∨ write c = .error Message.tooManyRingNumbers :=
        Spelling.brackets.write_of_fine wfc hfine hnone.1 hnone.2
      simp only
      rcases hwrite with ⟨t, ht⟩ | he
      · left
        exact ⟨t, by rw [ht]; rfl⟩
      · right; right; right
        rw [he]
        rfl

/-- Theorem 44 of CLAIMS.md: an example. `canonical` writes `CCO` for ethanol,
whether the text begins at the oxygen atom or at a carbon atom. So the search
finds a chosen form here, and the theorems above are not empty. -/
theorem run_canonical_ethanol :
    run ["canonical".toList, "OCC".toList]
      = { stdout := "CCO\n".toList, stderr := [], exitCode := 0 } ∧
    run ["canonical".toList, "CCO".toList]
      = { stdout := "CCO\n".toList, stderr := [], exitCode := 0 } := by
  constructor <;> rfl

end VeriMol
