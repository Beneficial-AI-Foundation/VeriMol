import VeriMol.Core.FluoroGroup
import VeriMol.Proofs.Predicates.FluoroGroup
import VeriMol.Proofs.Stereo

/-!
# The rule "no long perfluorinated group": what is proven

`VeriMol/Proofs/Predicates/FluoroGroup.lean` states the rule: a `Mol` has no
perfluorinated group of `n` or more carbon atoms. It says what a group is,
and nothing about how one is found. `VeriMol/Core/FluoroGroup.lean` has the
checker that the program runs: it works out the carbon atoms of the groups,
spreads from one of them along the bonds, and takes the size of the largest
group that it finds. This file proves theorems 47 and 48 of CLAIMS.md.

**About the rule itself (theorem 47).**

* Linked atoms are linked both ways, and atoms linked to a third are linked
  to each other (`Mol.FluoroLinked.symm`, `Mol.FluoroLinked.trans`). So the
  carbon atoms of the perfluorinated groups of a `Mol` fall into groups, and
  a group does not depend on the atom from which it is entered.
* A smaller `n` is the stricter rule (`Mol.HasFluoroGroup.of_le`; and, as
  a lemma outside the ledger, `Mol.NoFluoroGroup.of_le`).
* The rule gives the same answer for every numbering of the atoms of a
  molecule (`Mol.Renumbered.noFluoroGroup_iff`).

**The checker is right (theorem 48),** for every `Mol` and every `n`.

1. The two tests for one atom are the definitions: of the five conditions
   (`Mol.isSkeletonCarbon_iff`) and of a fluorinated carbon atom
   (`Mol.isFluoroCarbon_iff`).
2. The list of atoms that the checker works out holds exactly the carbon
   atoms of the perfluorinated groups (`Mol.mem_groupCarbons`). The checker
   starts from the fluorinated carbon atoms and adds, round by round, the
   atoms that three of the listed atoms hold. Every atom that it adds is a
   carbon atom of a group. And it leaves none out: when a round adds no
   atom, the list holds every atom that three of its atoms hold, and the
   bound on the number of rounds is large enough for that round to come
   (`Mol.growGroupCarbons_closed`).
3. The search from an atom returns exactly the atoms that are linked to it
   (`Mol.mem_fluoroGroupOf`), each once (`Mol.fluoroGroupOf_nodup`). This has
   two halves. That every atom which the search returns is linked to the
   atom is the easy one (`Mol.spread_sound`). The hard half is that the
   search leaves no atom out (`Mol.spread_complete`): it needs the bound on
   the number of steps to be large enough, and it needs every bond of a found
   atom to have been followed.
4. The number that the checker gives is the size of the largest group: a
   `Mol` has a group of at least `n` exactly when `n` is at most that number
   (`Mol.le_largestFluoroGroup_iff`).
5. So the checker says yes exactly when the rule holds
   (`Mol.hasNoFluoroGroup_iff`).

None of this needs the `Mol` to be sound, or even well formed, except the
statement about numberings, which is about well formed `Mol`s. The filter
asks the rule of sound `Mol`s only, for another reason: only of them does
the rule say something about a compound
(`VeriMol/Proofs/Predicates/Sound.lean`).

With theorem 48 Lean can work the rule out for a given `Mol`: it runs the
checker (the instances of `Decidable` at the end of this file).
`VeriMol/Proofs/Compounds.lean` uses that.
-/

namespace VeriMol

/-! # The rule itself (theorem 47)

## What the definitions mean, for every `Mol` -/

/-- An atom that meets the five conditions is an atom of the `Mol`: its number
is below the number of atoms. -/
theorem Mol.SkeletonCarbon.lt {m : Mol} {c : Nat} (h : m.SkeletonCarbon c) :
    c < m.atoms.length := by
  have carbon : m.elementOf c = some .C := h.1
  cases atom : m.atoms[c]? with
  | none => simp [Mol.elementOf, atom] at carbon
  | some _ => exact (List.getElem?_eq_some_iff.1 atom).1

/-- Both kinds of carbon atoms of a perfluorinated group meet the five
conditions. -/
theorem Mol.GroupCarbon.skeleton {m : Mol} {c : Nat} (h : m.GroupCarbon c) :
    m.SkeletonCarbon c := by
  cases h with
  | fluoro _ hf => exact hf.1
  | branch _ _ _ _ hs => exact hs

/-- A carbon atom of a perfluorinated group is an atom of the `Mol`. -/
theorem Mol.GroupCarbon.lt {m : Mol} {c : Nat} (h : m.GroupCarbon c) : c < m.atoms.length :=
  h.skeleton.lt

/-- Linked atoms are carbon atoms of a perfluorinated group: the atom at which
the way begins. -/
theorem Mol.FluoroLinked.left {m : Mol} {a c : Nat} (h : m.FluoroLinked a c) :
    m.GroupCarbon a := by
  induction h with
  | start ha => exact ha
  | step _ _ _ _ _ ih => exact ih

/-- Linked atoms are carbon atoms of a perfluorinated group: the atom at which
the way ends. -/
theorem Mol.FluoroLinked.right {m : Mol} {a c : Nat} (h : m.FluoroLinked a c) :
    m.GroupCarbon c := by
  cases h with
  | start ha => exact ha
  | step _ _ _ _ hc => exact hc

/-- Theorem 47 of CLAIMS.md, second statement. Atoms that are linked to a
third are linked to each other: a way from `a` to `b` and a way from `b` to
`c` make a way from `a` to `c`. -/
theorem Mol.FluoroLinked.trans {m : Mol} {a b c : Nat} (h₁ : m.FluoroLinked a b)
    (h₂ : m.FluoroLinked b c) : m.FluoroLinked a c := by
  induction h₂ with
  | start _ => exact h₁
  | step x y _ hy hfy ih => exact .step x y ih hy hfy

/-- If `a` is bonded to `b`, then `b` is bonded to `a`. -/
theorem Mol.mem_neighbours_comm {m : Mol} {a b : Nat} :
    a ∈ m.neighbours b ↔ b ∈ m.neighbours a := by
  simp only [Mol.mem_neighbours, Mol.Joined]
  constructor
  · rintro ⟨o, h | h⟩
    · exact ⟨o, Or.inr h⟩
    · exact ⟨o, Or.inl h⟩
  · rintro ⟨o, h | h⟩
    · exact ⟨o, Or.inr h⟩
    · exact ⟨o, Or.inl h⟩

/-- Theorem 47 of CLAIMS.md, first statement. Linked atoms are linked both
ways: a way from `a` to `c` can be gone back. -/
theorem Mol.FluoroLinked.symm {m : Mol} {a c : Nat} (h : m.FluoroLinked a c) :
    m.FluoroLinked c a := by
  induction h with
  | start ha => exact .start ha
  | step x y hx hy hfy ih =>
    exact Mol.FluoroLinked.trans
      (.step y x (.start hfy) (Mol.mem_neighbours_comm.1 hy) hx.right) ih

/-- Every `Mol` has a group of at least 0: the group of no atoms. -/
theorem Mol.hasFluoroGroup_zero (m : Mol) : m.HasFluoroGroup 0 :=
  ⟨0, [], List.nodup_nil, Nat.le_refl 0, fun _ h => absurd h (by simp)⟩

/-- Theorem 47 of CLAIMS.md, third statement. A group of at least `n` is a
group of at least `k`, for every `k` up to `n`. In particular a group of at
least `n + 1` is one of at least `n`. -/
theorem Mol.HasFluoroGroup.of_le {m : Mol} {k n : Nat} (hkn : k ≤ n) (h : m.HasFluoroGroup n) :
    m.HasFluoroGroup k := by
  obtain ⟨a, group, nodup, large, linked⟩ := h
  exact ⟨a, group, nodup, Nat.le_trans hkn large, linked⟩

/-- A smaller number is the stricter rule: a `Mol` without a group of `k` or
more carbon atoms has none of `n` or more, for every `n` from `k` on. -/
theorem Mol.NoFluoroGroup.of_le {m : Mol} {k n : Nat} (hkn : k ≤ n) (h : m.NoFluoroGroup k) :
    m.NoFluoroGroup n :=
  fun has => h (has.of_le hkn)

/-! ## The same answer for every numbering of the atoms

A `Mol` numbers its atoms, and one molecule has a `Mol` for every order in
which its atoms can be listed (`Mol.Renumbered`, SPEC.md, section 3.1). The
rule is about the molecule: it gives the same answer for all of them. -/

/-- An atom has its element at its new number. -/
theorem Mol.SameGraphBy.elementOf {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) {i : Nat} (hi : i < m₁.atoms.length) :
    m₂.elementOf (f i) = m₁.elementOf i := by
  unfold Mol.elementOf
  rw [h.atoms i hi]

/-- The elements around an atom are the same at its new number, in another
order. -/
theorem Mol.SameGraphBy.neighbourElements_perm {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : c < m₁.atoms.length) :
    (m₂.neighbourElements (f c)).Perm (m₁.neighbourElements c) := by
  unfold Mol.neighbourElements
  have := (h.neighbours_perm w₁ w₂ hc).map m₂.elementOf
  rw [List.map_map] at this
  refine this.trans (List.Perm.of_eq (List.map_congr_left fun x hx => ?_))
  exact h.elementOf (Mol.neighbours_lt w₁ hx).1

/-- No bond of an atom is a double, triple or quadruple bond, said with the
atoms that it is joined to. -/
theorem Mol.hasNoMultipleBond_iff (m : Mol) (c : Nat) :
    m.hasNoMultipleBond c = true ↔
      ∀ x order, m.Joined c x order → order = .single ∨ order = .aromatic := by
  unfold Mol.hasNoMultipleBond Mol.Joined
  rw [List.all_eq_true]
  constructor
  · intro h x order hj
    rcases hj with hj | hj
    · simpa using h _ hj
    · simpa using h _ hj
  · intro h bond hbond
    obtain ⟨a, b, order⟩ := bond
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq]
    by_cases ha : a = c
    · subst ha
      exact (h b order (.inl hbond)).elim (fun e => .inl (.inr e)) (fun e => .inr e)
    · by_cases hb : b = c
      · subst hb
        exact (h a order (.inr hbond)).elim (fun e => .inl (.inr e)) (fun e => .inr e)
      · exact .inl (.inl ⟨ha, hb⟩)

/-- An atom that meets the five conditions meets them at its new number. -/
theorem Mol.SameGraphBy.skeletonCarbon {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : m₁.SkeletonCarbon c) : m₂.SkeletonCarbon (f c) := by
  have inside := hc.lt
  have around := h.neighbourElements_perm w₁ w₂ inside
  obtain ⟨carbon, hydrogens, bonds, four, others⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.elementOf inside]
    exact carbon
  · rw [h.atoms c inside]
    exact hydrogens
  · rw [Mol.hasNoMultipleBond_iff] at bonds ⊢
    intro y order hy
    obtain ⟨back, same⟩ := h.back y (Mol.Joined.lt w₂ hy).2
    rw [← same] at hy
    exact bonds (g y) order ((h.bonds c (g y) order inside back).2 hy)
  · rw [around.length_eq]
    exact four
  · exact fun hin => others (around.mem_iff.1 hin)

/-- A fluorinated carbon atom is one at its new number. -/
theorem Mol.SameGraphBy.fluoroCarbon {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : m₁.FluoroCarbon c) : m₂.FluoroCarbon (f c) :=
  ⟨h.skeletonCarbon w₁ w₂ hc.1, (h.neighbourElements_perm w₁ w₂ hc.1.lt).mem_iff.2 hc.2⟩

/-- A carbon atom of a perfluorinated group is one at its new number: a
branch carbon atom keeps its three atoms, which stay different and stay
bonded to it. -/
theorem Mol.SameGraphBy.groupCarbon {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : m₁.GroupCarbon c) : m₂.GroupCarbon (f c) := by
  induction hc with
  | fluoro c hf => exact .fluoro (f c) (h.fluoroCarbon w₁ w₂ hf)
  | branch c x y z hs hxy hxz hyz hx hy hz gx gy gz ihx ihy ihz =>
    exact .branch (f c) (f x) (f y) (f z) (h.skeletonCarbon w₁ w₂ hs)
      (fun e => hxy (h.injective gx.lt gy.lt e)) (fun e => hxz (h.injective gx.lt gz.lt e))
      (fun e => hyz (h.injective gy.lt gz.lt e))
      ((h.mem_neighbours hs.lt gx.lt).2 hx) ((h.mem_neighbours hs.lt gy.lt).2 hy)
      ((h.mem_neighbours hs.lt gz.lt).2 hz) ihx ihy ihz

/-- Atoms that are linked are linked at their new numbers. -/
theorem Mol.SameGraphBy.fluoroLinked {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {a c : Nat} (linked : m₁.FluoroLinked a c) : m₂.FluoroLinked (f a) (f c) := by
  induction linked with
  | start ha => exact .start (h.groupCarbon w₁ w₂ ha)
  | step b c hb hc hfc ih =>
    exact .step (f b) (f c) ih ((h.mem_neighbours hb.right.lt hfc.lt).2 hc)
      (h.groupCarbon w₁ w₂ hfc)

/-- A group of at least `n` is one at the new numbers. -/
theorem Mol.SameGraphBy.hasFluoroGroup {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {n : Nat} (has : m₁.HasFluoroGroup n) : m₂.HasFluoroGroup n := by
  obtain ⟨a, group, nodup, large, linked⟩ := has
  refine ⟨f a, group.map f, ?_, by simpa using large, ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    refine nodup.imp_of_mem ?_
    intro x y hx hy hxy e
    exact hxy (h.injective (linked x hx).right.lt (linked y hy).right.lt e)
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact h.fluoroLinked w₁ w₂ (linked x hx)

/-- Two well formed `Mol`s that are the same molecule, numbered differently,
have a group of at least `n` both or neither. -/
theorem Mol.Renumbered.hasFluoroGroup_iff {m₁ m₂ : Mol} (w₁ : m₁.WellFormed)
    (w₂ : m₂.WellFormed) (h : m₁.Renumbered m₂) (n : Nat) :
    m₁.HasFluoroGroup n ↔ m₂.HasFluoroGroup n := by
  obtain ⟨f, g, by'⟩ := h
  exact ⟨by'.sameGraph.hasFluoroGroup w₁.graph w₂.graph,
    by'.sameGraph.symm.hasFluoroGroup w₂.graph w₁.graph⟩

/-- Theorem 47 of CLAIMS.md, fourth statement. The rule gives the same answer
for every numbering of the atoms of a molecule: of two well formed `Mol`s
that are the same molecule, numbered differently, both have no group of `n`
or more carbon atoms, or neither. -/
theorem Mol.Renumbered.noFluoroGroup_iff {m₁ m₂ : Mol} (w₁ : m₁.WellFormed)
    (w₂ : m₂.WellFormed) (h : m₁.Renumbered m₂) (n : Nat) :
    m₁.NoFluoroGroup n ↔ m₂.NoFluoroGroup n :=
  not_congr (h.hasFluoroGroup_iff w₁ w₂ n)

/-! # The checker is right (theorem 48)

## One atom -/

/-- The first test for one atom is right: it says yes exactly for an atom
that meets the five conditions. -/
theorem Mol.isSkeletonCarbon_iff (m : Mol) (c : Nat) :
    m.isSkeletonCarbon c = true ↔ m.SkeletonCarbon c := by
  unfold Mol.isSkeletonCarbon Mol.SkeletonCarbon Mol.neighbourElements Mol.elementOf
    Mol.hasNoMultipleBond
  cases h : m.atoms[c]? with
  | none => simp
  | some atom =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.map_some, Option.some.injEq, List.length_map]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      exact ⟨h1, h2, h3, h4,
        fun hin => Bool.false_ne_true (h5.symm.trans (List.contains_iff_mem.2 hin))⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩,
        Bool.eq_false_iff.2 (fun hc => h5 (List.contains_iff_mem.1 hc))⟩

/-- The second test for one atom is right: it says yes exactly for a
fluorinated carbon atom. -/
theorem Mol.isFluoroCarbon_iff (m : Mol) (c : Nat) :
    m.isFluoroCarbon c = true ↔ m.FluoroCarbon c := by
  unfold Mol.isFluoroCarbon Mol.FluoroCarbon
  rw [Bool.and_eq_true, Mol.isSkeletonCarbon_iff, List.contains_iff_mem]
  exact Iff.rfl

/-- An atom that meets the five conditions is bonded to four atoms. So both
kinds of carbon atoms of a perfluorinated group are. -/
theorem Mol.SkeletonCarbon.neighbours_length {m : Mol} {c : Nat} (h : m.SkeletonCarbon c) :
    (m.neighbours c).length = 4 := by
  have := h.2.2.2.1
  simpa [Mol.neighbourElements] using this

/-! ## Three different atoms -/

/-- The test for two different numbers is right. -/
theorem hasTwoDifferent_iff (l : List Nat) :
    hasTwoDifferent l = true ↔ ∃ y z, y ≠ z ∧ y ∈ l ∧ z ∈ l := by
  cases l with
  | nil => simp [hasTwoDifferent]
  | cons a rest =>
    simp only [hasTwoDifferent, List.any_eq_true, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨z, hz, hne⟩
      exact ⟨a, z, fun e => hne e.symm, List.mem_cons_self .., List.mem_cons_of_mem _ hz⟩
    · rintro ⟨y, z, hyz, hy, hz⟩
      by_cases hya : y = a
      · subst hya
        rcases List.mem_cons.1 hz with rfl | hz
        · exact absurd rfl hyz
        · exact ⟨z, hz, fun e => hyz e.symm⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd rfl hya
        · exact ⟨y, hy, hya⟩

/-- The test for three different numbers is right. -/
theorem hasThreeDifferent_iff (l : List Nat) :
    hasThreeDifferent l = true ↔
      ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∈ l ∧ y ∈ l ∧ z ∈ l := by
  induction l with
  | nil => simp [hasThreeDifferent]
  | cons a rest ih =>
    rw [hasThreeDifferent, Bool.or_eq_true, hasTwoDifferent_iff, ih]
    have inFilter : ∀ {v : Nat}, v ∈ rest.filter (· != a) ↔ v ∈ rest ∧ v ≠ a := by
      intro v
      simp [List.mem_filter]
    have tail : ∀ {v : Nat}, v ∈ a :: rest → v ≠ a → v ∈ rest := by
      intro v hv hne
      rcases List.mem_cons.1 hv with rfl | hv
      · exact absurd rfl hne
      · exact hv
    constructor
    · rintro (⟨y, z, hyz, hy, hz⟩ | ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩)
      · have hy' := inFilter.1 hy
        have hz' := inFilter.1 hz
        exact ⟨a, y, z, fun e => hy'.2 e.symm, fun e => hz'.2 e.symm, hyz,
          List.mem_cons_self .., List.mem_cons_of_mem _ hy'.1, List.mem_cons_of_mem _ hz'.1⟩
      · exact ⟨x, y, z, hxy, hxz, hyz, List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy,
          List.mem_cons_of_mem _ hz⟩
    · rintro ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
      by_cases hxa : x = a
      · have hya : y ≠ a := fun e => hxy (hxa.trans e.symm)
        have hza : z ≠ a := fun e => hxz (hxa.trans e.symm)
        exact .inl ⟨y, z, hyz, inFilter.2 ⟨tail hy hya, hya⟩, inFilter.2 ⟨tail hz hza, hza⟩⟩
      · by_cases hya : y = a
        · have hza : z ≠ a := fun e => hyz (hya.trans e.symm)
          exact .inl ⟨x, z, hxz, inFilter.2 ⟨tail hx hxa, hxa⟩, inFilter.2 ⟨tail hz hza, hza⟩⟩
        · by_cases hza : z = a
          · exact .inl ⟨x, y, hxy, inFilter.2 ⟨tail hx hxa, hxa⟩, inFilter.2 ⟨tail hy hya, hya⟩⟩
          · exact .inr ⟨x, y, z, hxy, hxz, hyz, tail hx hxa, tail hy hya, tail hz hza⟩

/-! ## The carbon atoms of the groups -/

/-- What one round adds: exactly the atoms of the `Mol` that are not listed
yet, meet the five conditions and are bonded to three different listed
atoms. -/
theorem Mol.mem_newGroupCarbons (m : Mol) (members : List Nat) (c : Nat) :
    c ∈ m.newGroupCarbons members ↔
      c < m.atoms.length ∧ c ∉ members ∧ m.SkeletonCarbon c ∧
      ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (x ∈ m.neighbours c ∧ x ∈ members) ∧ (y ∈ m.neighbours c ∧ y ∈ members) ∧
        (z ∈ m.neighbours c ∧ z ∈ members) := by
  unfold Mol.newGroupCarbons
  rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.and_eq_true,
    Mol.isSkeletonCarbon_iff, hasThreeDifferent_iff]
  have inFilter : ∀ {v : Nat}, v ∈ (m.neighbours c).filter members.contains ↔
      v ∈ m.neighbours c ∧ v ∈ members := by
    intro v
    rw [List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨hlt, ⟨hnot, hskel⟩, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
    refine ⟨hlt, fun hin => ?_, hskel, x, y, z, hxy, hxz, hyz, inFilter.1 hx, inFilter.1 hy,
      inFilter.1 hz⟩
    rw [List.contains_iff_mem.2 hin] at hnot
    cases hnot
  · rintro ⟨hlt, hnot, hskel, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
    refine ⟨hlt, ⟨?_, hskel⟩, x, y, z, hxy, hxz, hyz, inFilter.2 hx, inFilter.2 hy, inFilter.2 hz⟩
    cases hc : members.contains c with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.1 hc) hnot

/-- The rounds add only carbon atoms of a perfluorinated group: an atom that
a round adds is a branch carbon atom, held by three atoms that were listed
before. -/
theorem Mol.growGroupCarbons_sound (m : Mol) : ∀ (rounds : Nat) (members : List Nat),
    (∀ x ∈ members, m.GroupCarbon x) →
    ∀ x ∈ m.growGroupCarbons rounds members, m.GroupCarbon x := by
  intro rounds
  induction rounds with
  | zero => intro members h x hx; exact h x (by simpa [Mol.growGroupCarbons] using hx)
  | succ rounds ih =>
    intro members h x hx
    simp only [Mol.growGroupCarbons] at hx
    split at hx
    · exact h x hx
    · refine ih _ (fun y hy => ?_) x hx
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨_, _, hs, a, b, d, hab, had, hbd, ha, hb, hd⟩ :=
          (m.mem_newGroupCarbons members y).1 hy
        exact .branch y a b d hs hab had hbd ha.1 hb.1 hd.1 (h a ha.2) (h b hb.2) (h d hd.2)
      · exact h y hy

/-- The rounds take no atom off the list. -/
theorem Mol.subset_growGroupCarbons (m : Mol) : ∀ (rounds : Nat) (members : List Nat),
    ∀ x ∈ members, x ∈ m.growGroupCarbons rounds members := by
  intro rounds
  induction rounds with
  | zero => intro members x hx; simpa [Mol.growGroupCarbons] using hx
  | succ rounds ih =>
    intro members x hx
    simp only [Mol.growGroupCarbons]
    split
    · exact hx
    · exact ih _ x (List.mem_append_right _ hx)

/-- The rounds are enough. Say that the listed atoms are different atoms of
the `Mol`, and that there is one round left for every atom of the `Mol` that
is not listed. Then one more round would add nothing to the list that comes
out.

Every round but the last adds at least one atom, and there can be no more
listed atoms than the `Mol` has atoms. So either a round adds nothing before
the rounds are used up, or every atom of the `Mol` is listed. -/
theorem Mol.growGroupCarbons_closed (m : Mol) : ∀ (rounds : Nat) (members : List Nat),
    members.Nodup → (∀ x ∈ members, x < m.atoms.length) →
    m.atoms.length ≤ rounds + members.length →
    m.newGroupCarbons (m.growGroupCarbons rounds members) = [] := by
  intro rounds
  induction rounds with
  | zero =>
    intro members nodup inside enough
    simp only [Mol.growGroupCarbons]
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hlt, hnot, _⟩ := (m.mem_newGroupCarbons members c).1 hc
    have := (List.nodup_cons.2 ⟨hnot, nodup⟩).length_le_of_subset
      (l₂ := List.range m.atoms.length) (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_range.2 hlt
        · exact List.mem_range.2 (inside x hx))
    simp only [List.length_cons, List.length_range] at this
    omega
  | succ rounds ih =>
    intro members nodup inside enough
    simp only [Mol.growGroupCarbons]
    split
    · rename_i hempty
      exact List.isEmpty_iff.1 hempty
    · rename_i hnonempty
      have newIn : ∀ c ∈ m.newGroupCarbons members, c < m.atoms.length ∧ c ∉ members :=
        fun c hc => ⟨((m.mem_newGroupCarbons members c).1 hc).1,
          ((m.mem_newGroupCarbons members c).1 hc).2.1⟩
      refine ih _ ?_ ?_ ?_
      · rw [List.nodup_append]
        refine ⟨List.nodup_range.sublist List.filter_sublist, nodup, ?_⟩
        intro a ha b hb e
        exact (newIn a ha).2 (e ▸ hb)
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact (newIn x hx).1
        · exact inside x hx
      · have : 0 < (m.newGroupCarbons members).length := by
          cases hn : m.newGroupCarbons members with
          | nil => simp [hn] at hnonempty
          | cons _ _ => simp
        simp only [List.length_append]
        omega

/-- Theorem 48 of CLAIMS.md rests on this. The list that the checker works
out holds exactly the carbon atoms of the perfluorinated groups, for every
`Mol`.

That every listed atom is one follows round by round. For the other half,
take a carbon atom of a group. A fluorinated carbon atom is listed from the
start. A branch carbon atom is bonded to three different carbon atoms of a
group, which are listed, and if it were not listed itself, one more round
would add it: but one more round adds nothing. -/
theorem Mol.mem_groupCarbons (m : Mol) (c : Nat) : c ∈ m.groupCarbons ↔ m.GroupCarbon c := by
  unfold Mol.groupCarbons
  constructor
  · exact m.growGroupCarbons_sound _ _
      (fun x hx => .fluoro x ((m.isFluoroCarbon_iff x).1 (List.mem_filter.1 hx).2)) c
  · intro h
    have closed := m.growGroupCarbons_closed m.atoms.length
      ((List.range m.atoms.length).filter m.isFluoroCarbon)
      (List.nodup_range.sublist List.filter_sublist)
      (fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1) (Nat.le_add_right ..)
    induction h with
    | fluoro c hf =>
      exact m.subset_growGroupCarbons _ _ c
        (List.mem_filter.2 ⟨List.mem_range.2 hf.1.lt, (m.isFluoroCarbon_iff c).2 hf⟩)
    | branch c x y z hs hxy hxz hyz hx hy hz _ _ _ ihx ihy ihz =>
      by_cases hmem : c ∈ m.growGroupCarbons m.atoms.length
          ((List.range m.atoms.length).filter m.isFluoroCarbon)
      · exact hmem
      · have added := (m.mem_newGroupCarbons _ c).2
          ⟨hs.lt, hmem, hs, x, y, z, hxy, hxz, hyz, ⟨hx, ihx⟩, ⟨hy, ihy⟩, ⟨hz, ihz⟩⟩
        rw [closed] at added
        cases added

/-! ## The search -/

/-- An atom that the search passes over is found already, or is not on the
list of the atoms that it may go through. -/
theorem spread_skip {members found : List Nat} {c : Nat}
    (h : (found.contains c || !members.contains c) = true) : c ∈ found ∨ c ∉ members := by
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl (List.contains_iff_mem.1 h)
  · refine .inr fun hc => ?_
    rw [List.contains_iff_mem.2 hc] at h
    cases h

/-- An atom that the search takes is new, and is on that list. -/
theorem spread_take {members found : List Nat} {c : Nat}
    (h : ¬ (found.contains c || !members.contains c) = true) : c ∉ found ∧ c ∈ members := by
  rw [Bool.or_eq_true, not_or] at h
  refine ⟨fun hc => h.1 (List.contains_iff_mem.2 hc), List.contains_iff_mem.1 ?_⟩
  cases hf : members.contains c with
  | true => rfl
  | false => exact absurd (by rw [hf]; rfl) h.2

/-- The search finds no atom twice. -/
theorem Mol.spread_nodup (m : Mol) (members : List Nat) :
    ∀ (steps : Nat) (todo found : List Nat),
    found.Nodup → (m.spread members steps todo found).Nodup := by
  intro steps
  induction steps with
  | zero => intro todo found h; simpa [Mol.spread] using h
  | succ steps ih =>
    intro todo found h
    cases todo with
    | nil => simpa [Mol.spread] using h
    | cons c todo =>
      rw [Mol.spread]
      split
      · exact ih _ _ h
      · rename_i hcond
        exact ih _ _ (List.nodup_cons.2 ⟨(spread_take hcond).1, h⟩)

/-- The easy half. Let `members` hold exactly the carbon atoms of the
perfluorinated groups. Then the search returns only atoms that were found
before, and atoms that are linked to an atom which was still to be looked
at. -/
theorem Mol.spread_sound (m : Mol) {members : List Nat}
    (hm : ∀ c, c ∈ members ↔ m.GroupCarbon c) :
    ∀ (steps : Nat) (todo found : List Nat) (x : Nat),
    x ∈ m.spread members steps todo found → x ∈ found ∨ ∃ t ∈ todo, m.FluoroLinked t x := by
  intro steps
  induction steps with
  | zero => intro todo found x h; exact .inl (by simpa [Mol.spread] using h)
  | succ steps ih =>
    intro todo found x h
    cases todo with
    | nil => exact .inl (by simpa [Mol.spread] using h)
    | cons c todo =>
      rw [Mol.spread] at h
      split at h
      · rcases ih _ _ _ h with h | ⟨t, ht, hl⟩
        · exact .inl h
        · exact .inr ⟨t, List.mem_cons_of_mem _ ht, hl⟩
      · rename_i hcond
        have hc := (hm c).1 (spread_take hcond).2
        rcases ih _ _ _ h with h | ⟨t, ht, hl⟩
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr ⟨x, List.mem_cons_self .., .start hc⟩
          · exact .inl h
        · rcases List.mem_append.1 ht with ht | ht
          · exact .inr ⟨c, List.mem_cons_self ..,
              Mol.FluoroLinked.trans (.step c t (.start hc) ht hl.left) hl⟩
          · exact .inr ⟨t, List.mem_cons_of_mem _ ht, hl⟩

/-- The hard half: the search leaves no atom out. Let `members` hold exactly
the carbon atoms of the perfluorinated groups, and say that

* the atoms found so far are different carbon atoms of a group;
* the steps are enough: at least one for every atom that is still to be
  looked at, and four more for every atom of the `Mol` that is not found yet;
* every carbon atom of a group next to an atom that is found is itself
  found, or still to be looked at.

Then the search returns every atom that was found, and every carbon atom of
a group that was to be looked at, and what it returns is closed: with each of
its atoms it holds every carbon atom of a group next to that atom.

The second condition is where the number of steps comes in. A step that
passes an atom over uses up one atom of `todo`. A step that takes an atom
puts its four neighbours into `todo` and makes one atom more found, of which
there can be no more than the `Mol` has atoms. -/
theorem Mol.spread_complete (m : Mol) {members : List Nat}
    (hm : ∀ c, c ∈ members ↔ m.GroupCarbon c) :
    ∀ (steps : Nat) (todo found : List Nat),
    found.Nodup → (∀ x ∈ found, m.GroupCarbon x) →
    todo.length + 4 * (m.atoms.length - found.length) ≤ steps →
    (∀ x ∈ found, ∀ d ∈ m.neighbours x, m.GroupCarbon d → d ∈ found ∨ d ∈ todo) →
    (∀ x ∈ found, x ∈ m.spread members steps todo found) ∧
    (∀ t ∈ todo, m.GroupCarbon t → t ∈ m.spread members steps todo found) ∧
    (∀ x ∈ m.spread members steps todo found, ∀ d ∈ m.neighbours x, m.GroupCarbon d →
      d ∈ m.spread members steps todo found) := by
  intro steps
  induction steps with
  | zero =>
    intro todo found _ _ enough closed
    have empty : todo = [] := List.length_eq_zero_iff.1 (by omega)
    subst empty
    simp only [Mol.spread]
    exact ⟨fun x hx => hx, fun t ht => absurd ht (by simp),
      fun x hx d hd hf => (closed x hx d hd hf).elim id (fun h => absurd h (by simp))⟩
  | succ steps ih =>
    intro todo found nodup group enough closed
    cases todo with
    | nil =>
      simp only [Mol.spread]
      exact ⟨fun x hx => hx, fun t ht => absurd ht (by simp),
        fun x hx d hd hf => (closed x hx d hd hf).elim id (fun h => absurd h (by simp))⟩
    | cons c todo =>
      rw [Mol.spread]
      split
      · -- `c` is found already, or is no carbon atom of a group: it is passed over
        rename_i hcond
        have skip : c ∈ found ∨ ¬ m.GroupCarbon c :=
          (spread_skip hcond).imp id (fun no hc => no ((hm c).2 hc))
        obtain ⟨keeps, takes, closed'⟩ := ih todo found nodup group
          (by simp only [List.length_cons] at enough; omega)
          (fun x hx d hd hf => by
            rcases closed x hx d hd hf with h | h
            · exact .inl h
            · rcases List.mem_cons.1 h with rfl | h
              · exact skip.elim .inl (fun no => absurd hf no)
              · exact .inr h)
        refine ⟨keeps, fun t ht hf => ?_, closed'⟩
        rcases List.mem_cons.1 ht with rfl | ht
        · exact skip.elim (keeps t) (fun no => absurd hf no)
        · exact takes t ht hf
      · -- `c` is a new carbon atom of a group: it is found, and the atoms that it is
        -- bonded to are to be looked at
        rename_i hcond
        have fresh := (spread_take hcond).1
        have hc := (hm c).1 (spread_take hcond).2
        have nodup' : (c :: found).Nodup := List.nodup_cons.2 ⟨fresh, nodup⟩
        have group' : ∀ x ∈ c :: found, m.GroupCarbon x := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hc
          · exact group x hx
        -- the atoms that are found are different atoms of the `Mol`, so there are no
        -- more of them than the `Mol` has atoms
        have room : (c :: found).length ≤ m.atoms.length := by
          have := nodup'.length_le_of_subset (l₂ := List.range m.atoms.length)
            (fun x hx => List.mem_range.2 (group' x hx).lt)
          simpa using this
        obtain ⟨keeps, takes, closed'⟩ := ih (m.neighbours c ++ todo) (c :: found) nodup' group'
          (by
            simp only [List.length_cons, List.length_append,
              hc.skeleton.neighbours_length] at enough room ⊢
            omega)
          (fun x hx d hd hf => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact .inr (List.mem_append_left _ hd)
            · rcases closed x hx d hd hf with h | h
              · exact .inl (List.mem_cons_of_mem _ h)
              · rcases List.mem_cons.1 h with rfl | h
                · exact .inl (List.mem_cons_self ..)
                · exact .inr (List.mem_append_right _ h))
        refine ⟨fun x hx => keeps x (List.mem_cons_of_mem _ hx), fun t ht hf => ?_, closed'⟩
        rcases List.mem_cons.1 ht with rfl | ht
        · exact keeps t (List.mem_cons_self ..)
        · exact takes t (List.mem_append_right _ ht) hf

/-- Theorem 48 of CLAIMS.md, for the search. The search is right, for every
`Mol`: the group that it returns for an atom holds exactly the atoms that are
linked to that atom. -/
theorem Mol.mem_fluoroGroupOf (m : Mol) (a c : Nat) :
    c ∈ m.fluoroGroupOf a ↔ m.FluoroLinked a c := by
  unfold Mol.fluoroGroupOf Mol.fluoroGroupAmong
  constructor
  · intro h
    rcases Mol.spread_sound m m.mem_groupCarbons _ _ _ _ h with h | ⟨t, ht, hl⟩
    · simp at h
    · rw [List.mem_singleton.1 ht] at hl
      exact hl
  · intro h
    obtain ⟨_, takes, closed⟩ := Mol.spread_complete m m.mem_groupCarbons
      (4 * m.atoms.length + 1) [a] []
      List.nodup_nil (by simp) (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
    induction h with
    | start ha => exact takes a (List.mem_singleton.2 rfl) ha
    | step b c _ hc hfc ih => exact closed b ih c hc hfc

/-- The group that the search returns for an atom holds each of its atoms
once. -/
theorem Mol.fluoroGroupOf_nodup (m : Mol) (a : Nat) : (m.fluoroGroupOf a).Nodup :=
  Mol.spread_nodup m _ _ _ _ List.nodup_nil

/-! ## The groups of a `Mol`, and the largest of them -/

/-- Each group that the checker lists is the group of a carbon atom of a
perfluorinated group. -/
theorem Mol.fluoroGroupsFrom_sound (m : Mol) : ∀ (atoms seen : List Nat),
    ∀ group ∈ m.fluoroGroupsFrom m.groupCarbons atoms seen,
      ∃ a, m.GroupCarbon a ∧ group = m.fluoroGroupOf a := by
  intro atoms
  induction atoms with
  | nil => intro seen group h; simp [Mol.fluoroGroupsFrom] at h
  | cons a rest ih =>
    intro seen group h
    rw [Mol.fluoroGroupsFrom] at h
    split at h
    · exact ih _ _ h
    · rename_i hcond
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨a, (m.mem_groupCarbons a).1 (spread_take hcond).2, rfl⟩
      · exact ih _ _ h

/-- The checker leaves no carbon atom of a group out: each one that it is
given was seen before, or stands in one of the groups that it lists. -/
theorem Mol.fluoroGroupsFrom_complete (m : Mol) : ∀ (atoms seen : List Nat),
    ∀ a ∈ atoms, m.GroupCarbon a →
      a ∈ seen ∨ ∃ group ∈ m.fluoroGroupsFrom m.groupCarbons atoms seen, a ∈ group := by
  intro atoms
  induction atoms with
  | nil => intro seen a h; simp at h
  | cons b rest ih =>
    intro seen a h ha
    rw [Mol.fluoroGroupsFrom]
    split
    · rename_i hcond
      rcases List.mem_cons.1 h with rfl | h
      · exact (spread_skip hcond).elim .inl (fun no => absurd ((m.mem_groupCarbons a).2 ha) no)
      · exact ih _ _ h ha
    · rename_i hcond
      rcases List.mem_cons.1 h with rfl | h
      · exact .inr ⟨_, List.mem_cons_self .., (Mol.mem_fluoroGroupOf m a a).2 (.start ha)⟩
      · rcases ih (m.fluoroGroupOf b ++ seen) a h ha with h | ⟨group, hgroup, hmem⟩
        · rcases List.mem_append.1 h with h | h
          · exact .inr ⟨_, List.mem_cons_self .., h⟩
          · exact .inl h
        · exact .inr ⟨group, List.mem_cons_of_mem _ hgroup, hmem⟩

/-- A number is at most the largest of some sizes, taken from `start` on,
exactly when it is at most `start` or at most one of the sizes. -/
theorem le_foldl_max (n : Nat) : ∀ (sizes : List Nat) (start : Nat),
    n ≤ sizes.foldl max start ↔ n ≤ start ∨ ∃ size ∈ sizes, n ≤ size := by
  intro sizes
  induction sizes with
  | nil => intro start; simp
  | cons size rest ih =>
    intro start
    rw [List.foldl_cons, ih]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · rcases Nat.le_total start size with hle | hle
        · rw [Nat.max_eq_right hle] at h
          exact .inr ⟨size, List.mem_cons_self .., h⟩
        · rw [Nat.max_eq_left hle] at h
          exact .inl h
      · exact .inr ⟨s, List.mem_cons_of_mem _ hs, h⟩
    · rintro (h | ⟨s, hs, h⟩)
      · exact .inl (Nat.le_trans h (Nat.le_max_left ..))
      · rcases List.mem_cons.1 hs with rfl | hs
        · exact .inl (Nat.le_trans h (Nat.le_max_right ..))
        · exact .inr ⟨s, hs, h⟩

/-- Theorem 48 of CLAIMS.md, for the number. The size of the largest group is
right, for every `Mol` and every `n`: the `Mol` has a perfluorinated group of
at least `n` carbon atoms exactly when `n` is at most the number that the
checker gives. So that number is the largest `n` for which there is such a
group. -/
theorem Mol.le_largestFluoroGroup_iff (m : Mol) (n : Nat) :
    n ≤ m.largestFluoroGroup ↔ m.HasFluoroGroup n := by
  unfold Mol.largestFluoroGroup Mol.fluoroGroups
  rw [le_foldl_max]
  constructor
  · rintro (h | ⟨size, hsize, h⟩)
    · exact m.hasFluoroGroup_zero.of_le h
    · obtain ⟨group, hgroup, rfl⟩ := List.mem_map.1 hsize
      obtain ⟨a, _, rfl⟩ := Mol.fluoroGroupsFrom_sound m _ _ group hgroup
      exact ⟨a, m.fluoroGroupOf a, Mol.fluoroGroupOf_nodup m a, h,
        fun c hc => (Mol.mem_fluoroGroupOf m a c).1 hc⟩
  · rintro ⟨a, group, nodup, large, linked⟩
    cases group with
    | nil => exact .inl (by simpa using large)
    | cons c rest =>
      have ha : m.GroupCarbon a := (linked c (List.mem_cons_self ..)).left
      rcases Mol.fluoroGroupsFrom_complete m (List.range m.atoms.length) [] a
        (List.mem_range.2 ha.lt) ha with h | ⟨found, hfound, hmem⟩
      · simp at h
      · obtain ⟨b, _, rfl⟩ := Mol.fluoroGroupsFrom_sound m _ _ found hfound
        have hba : m.FluoroLinked b a := (Mol.mem_fluoroGroupOf m b a).1 hmem
        have within : c :: rest ⊆ m.fluoroGroupOf b := fun x hx =>
          (Mol.mem_fluoroGroupOf m b x).2 (hba.trans (linked x hx))
        exact .inr ⟨_, List.mem_map.2 ⟨_, hfound, rfl⟩,
          Nat.le_trans large (nodup.length_le_of_subset within)⟩

/-- Theorem 48 of CLAIMS.md. The checker of the rule is right, for every
`Mol` and every `n`: it says yes exactly when the `Mol` has no perfluorinated
group of `n` or more carbon atoms. -/
theorem Mol.hasNoFluoroGroup_iff (m : Mol) (n : Nat) :
    m.hasNoFluoroGroup n = true ↔ m.NoFluoroGroup n := by
  unfold Mol.hasNoFluoroGroup Mol.NoFluoroGroup
  rw [decide_eq_true_iff, ← Mol.le_largestFluoroGroup_iff, Nat.not_le]

/-! ## Lean can work the rule out -/

/-- Whether a `Mol` has a perfluorinated group of at least `n` carbon atoms
can be worked out: Lean runs the checker for the size of the largest group,
which is right by `Mol.le_largestFluoroGroup_iff`. -/
instance (m : Mol) (n : Nat) : Decidable (m.HasFluoroGroup n) :=
  decidable_of_iff _ (Mol.le_largestFluoroGroup_iff m n)

/-- Whether the rule holds for a `Mol` can be worked out. -/
instance (m : Mol) (n : Nat) : Decidable (m.NoFluoroGroup n) :=
  show Decidable (¬ _) from inferInstance

end VeriMol
