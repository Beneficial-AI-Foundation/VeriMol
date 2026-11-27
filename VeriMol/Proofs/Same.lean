import VeriMol.Core.Same
import VeriMol.Proofs.Follow
import VeriMol.Proofs.Stereo

/-!
# "The same molecule, numbered differently" behaves as "the same" must

Theorems 20 to 22 and 41 to 43 of CLAIMS.md. The definition stands in
`VeriMol/Core/Same.lean` (SPEC.md, section 3.1).

1. Every `Mol` is the same molecule as itself; if one `Mol` is another one
   numbered differently, then so is the other the first; and numbering
   differently twice is numbering differently once (the first three
   statements of theorem 20; the fourth stands in
   `VeriMol/Proofs/Chosen.lean`).
2. The definition is not too weak: with no atom renumbered, two well formed
   `Mol`s that are the same molecule are equal (theorem 21).
3. A well formed `Mol` is fixed by its atoms, by which bonds it has and by
   which stereo facts it has (`Mol.eq_of_sameFacts`, theorem 22). Theorem 21
   rests on the same fact.
4. Two single examples, one each way. `CCO` and `OCC` are read as two
   different `Mol`s that are the same molecule (theorem 41). `C1CCCCC1` and
   `C1CC1.C1CC1` are read as two `Mol`s with the same atoms and as many bonds
   that are not the same molecule (theorem 42).
5. Two examples with stereo facts: two texts of one molecule, and its mirror
   image, which is another one (theorem 43).
-/

namespace VeriMol

/-! ## With the two maps named

`Mol.Renumbered` says that two maps exist. Here are the first three
statements of theorem 20 with the maps named, and two more: two well formed
`Mol`s that are the same molecule both have stereo facts or neither has, and
only what the maps do to the atom numbers of the two `Mol`s matters. -/

/-- Renumbering the places with the map that changes nothing gives the
places. -/
theorem map_id_places (places : List Place) : places.map (Option.map id) = places := by
  induction places with
  | nil => rfl
  | cons p rest ih =>
    rw [List.map_cons, ih]
    cases p <;> rfl

/-- Every `Mol` is itself, with no atom renumbered. -/
theorem Mol.RenumberedBy.refl (m : Mol) : Mol.RenumberedBy id id m m := by
  refine ⟨fun _ h => ⟨h, rfl⟩, fun _ h => ⟨h, rfl⟩, fun _ _ => rfl, fun _ _ _ _ _ => Iff.rfl, ?_,
    fun _ _ _ _ _ _ _ _ => rfl⟩
  intro atom places _ _
  rw [map_id_places]
  rfl

/-- The same renumbering, read backwards. -/
theorem Mol.RenumberedBy.symm {f g : Nat → Nat} {m₁ m₂ : Mol} (hf : Mol.RenumberedBy f g m₁ m₂) :
    Mol.RenumberedBy g f m₂ m₁ := by
  have hs := hf.sameGraph.symm
  refine ⟨hs.forth, hs.back, hs.atoms, hs.bonds, ?_, ?_⟩
  · intro atom places hatom hplaces
    obtain ⟨hg, hfg⟩ := hf.back atom hatom
    have hrange : ∀ i, some i ∈ places.map (Option.map g) → i < m₁.atoms.length := by
      intro i hi
      obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hi
      cases p with
      | none => cases hpi
      | some k =>
        simp only [Option.map_some, Option.some.injEq] at hpi
        subst hpi
        exact (hf.back k (hplaces k hp)).1
    have key := hf.orientations (g atom) (places.map (Option.map g)) hg hrange
    rw [hfg, map_map_places (fun i hi => (hf.back i (hplaces i hi)).2)] at key
    exact key.symm
  · intro a b x y ha hb hx hy
    have key := hf.geometries (g a) (g b) (g x) (g y) (hf.back a ha).1 (hf.back b hb).1
      (hf.back x hx).1 (hf.back y hy).1
    rw [(hf.back a ha).2, (hf.back b hb).2, (hf.back x hx).2, (hf.back y hy).2] at key
    exact key.symm

/-- Two well formed `Mol`s that are the same molecule both have stereo facts,
or neither has. -/
theorem Mol.RenumberedBy.hasStereo_eq {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed) :
    m₂.hasStereo = m₁.hasStereo := by
  rw [Bool.eq_iff_iff]
  exact ⟨h.symm.hasStereo_of w₂ w₁, h.hasStereo_of w₁ w₂⟩

/-- One renumbering after another. -/
theorem Mol.RenumberedBy.trans {f g f' g' : Nat → Nat} {m₁ m₂ m₃ : Mol}
    (hf : Mol.RenumberedBy f g m₁ m₂) (hf' : Mol.RenumberedBy f' g' m₂ m₃) :
    Mol.RenumberedBy (f' ∘ f) (g ∘ g') m₁ m₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hf.forth i hi
    obtain ⟨h3, h4⟩ := hf'.forth (f i) h1
    exact ⟨h3, by simp [Function.comp, h4, h2]⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := hf'.back j hj
    obtain ⟨h3, h4⟩ := hf.back (g' j) h1
    exact ⟨h3, by simp [Function.comp, h4, h2]⟩
  · intro i hi
    obtain ⟨h1, _⟩ := hf.forth i hi
    simp only [Function.comp]
    rw [hf'.atoms (f i) h1, hf.atoms i hi]
  · intro i j order hi hj
    obtain ⟨h1, _⟩ := hf.forth i hi
    obtain ⟨h2, _⟩ := hf.forth j hj
    exact (hf.bonds i j order hi hj).trans (hf'.bonds (f i) (f j) order h1 h2)
  · intro atom places hatom hplaces
    obtain ⟨h1, _⟩ := hf.forth atom hatom
    have hrange : ∀ i, some i ∈ places.map (Option.map f) → i < m₂.atoms.length := by
      intro i hi
      obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hi
      cases p with
      | none => cases hpi
      | some k =>
        simp only [Option.map_some, Option.some.injEq] at hpi
        subst hpi
        exact (hf.forth k (hplaces k hp)).1
    have hmap : places.map (Option.map (f' ∘ f))
        = (places.map (Option.map f)).map (Option.map f') := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      cases p <;> rfl
    rw [hmap]
    exact (hf'.orientations (f atom) _ h1 hrange).trans (hf.orientations atom places hatom hplaces)
  · intro a b x y ha hb hx hy
    exact (hf'.geometries (f a) (f b) (f x) (f y) (hf.forth a ha).1 (hf.forth b hb).1
      (hf.forth x hx).1 (hf.forth y hy).1).trans (hf.geometries a b x y ha hb hx hy)

/-- Only what the two maps do to the atom numbers of the two `Mol`s matters. -/
theorem Mol.RenumberedBy.congr {f g f' g' : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (hf : ∀ i, i < m₁.atoms.length → f' i = f i)
    (hg : ∀ j, j < m₂.atoms.length → g' j = g j) : Mol.RenumberedBy f' g' m₁ m₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := h.forth i hi
    rw [hf i hi, hg _ h1]
    exact ⟨h1, h2⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := h.back j hj
    rw [hg j hj, hf _ h1]
    exact ⟨h1, h2⟩
  · intro i hi
    rw [hf i hi]
    exact h.atoms i hi
  · intro i j order hi hj
    rw [hf i hi, hf j hj]
    exact h.bonds i j order hi hj
  · intro atom places hatom hplaces
    have hmap : places.map (Option.map f') = places.map (Option.map f) := by
      apply List.map_congr_left
      intro p hp
      cases p with
      | none => rfl
      | some k => simp [hf k (hplaces k hp)]
    rw [hf atom hatom, hmap]
    exact h.orientations atom places hatom hplaces
  · intro a b x y ha hb hx hy
    rw [hf a ha, hf b hb, hf x hx, hf y hy]
    exact h.geometries a b x y ha hb hx hy

/-! ## Theorem 20 -/

/-- Theorem 20 of CLAIMS.md, first statement. Every `Mol` is itself, numbered
as it is. -/
theorem Mol.Renumbered.refl (m : Mol) : m.Renumbered m :=
  ⟨id, id, Mol.RenumberedBy.refl m⟩

/-- Theorem 20 of CLAIMS.md, second statement. If `m₂` is `m₁` numbered
differently, then `m₁` is `m₂` numbered differently. -/
theorem Mol.Renumbered.symm {m₁ m₂ : Mol} (h : m₁.Renumbered m₂) : m₂.Renumbered m₁ := by
  obtain ⟨f, g, hf⟩ := h
  exact ⟨g, f, hf.symm⟩

/-- Theorem 20 of CLAIMS.md, third statement. Numbering differently twice is
numbering differently once. -/
theorem Mol.Renumbered.trans {m₁ m₂ m₃ : Mol} (h₁ : m₁.Renumbered m₂) (h₂ : m₂.Renumbered m₃) :
    m₁.Renumbered m₃ := by
  obtain ⟨f, g, hf⟩ := h₁
  obtain ⟨f', g', hf'⟩ := h₂
  exact ⟨f' ∘ f, g ∘ g', hf.trans hf'⟩

/-! ## Theorems 21 and 22 -/

/-- Two lists of bonds in increasing order that hold the same bonds are equal. -/
theorem eq_of_ordered_of_mem_iff {l₁ l₂ : List Bond}
    (h₁ : l₁.Pairwise Bond.before) (h₂ : l₂.Pairwise Bond.before)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ :=
  eq_of_pairwise_of_mem_iff Bond.not_before_self
    (fun x y hxy hyx => by unfold Bond.before at hxy hyx; omega) h₁ h₂ h

/-- Theorem 22 of CLAIMS.md. A well formed `Mol` is fixed by its atoms, by
which bonds it has and by which stereo facts it has: the order of the lists
`bonds`, `orientations` and `geometries` carries no information of its own. -/
theorem Mol.eq_of_sameFacts (first second : Mol) (h₁ : first.WellFormed) (h₂ : second.WellFormed)
    (hatoms : first.atoms = second.atoms)
    (hbonds : ∀ bond, bond ∈ first.bonds ↔ bond ∈ second.bonds)
    (horientations : ∀ x, x ∈ first.orientations ↔ x ∈ second.orientations)
    (hgeometries : ∀ x, x ∈ first.geometries ↔ x ∈ second.geometries) : first = second := by
  have hb : first.bonds = second.bonds := eq_of_ordered_of_mem_iff h₁.2.1 h₂.2.1 hbonds
  have ho : first.orientations = second.orientations :=
    eq_of_pairwise_of_mem_iff (r := fun x y : AtomOrientation => x.atom < y.atom)
      (fun x => Nat.lt_irrefl _) (fun x y hxy => Nat.lt_asymm hxy) h₁.2.2.1 h₂.2.2.1 horientations
  have hg : first.geometries = second.geometries :=
    eq_of_pairwise_of_mem_iff
      (r := fun x y : BondGeometry => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b))
      (fun x => by omega) (fun x y hxy => by omega) h₁.2.2.2.2.1 h₂.2.2.2.2.1 hgeometries
  cases first
  cases second
  simp only at hatoms hb ho hg
  subst hatoms hb ho hg
  rfl

/-- Theorem 21 of CLAIMS.md. The definition is not too weak: if no atom gets
another number, two well formed `Mol`s that are the same molecule are the same
`Mol`. -/
theorem Mol.eq_of_renumberedBy_id {m₁ m₂ : Mol} (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (h : Mol.RenumberedBy id id m₁ m₂) : m₁ = m₂ := by
  have hlen : m₁.atoms.length = m₂.atoms.length := by
    have a := h.forth
    have b := h.back
    simp only [id] at a b
    apply Nat.le_antisymm
    · apply Nat.le_of_not_lt
      intro hlt
      exact absurd (a _ hlt).1 (Nat.lt_irrefl _)
    · apply Nat.le_of_not_lt
      intro hlt
      exact absurd (b _ hlt).1 (Nat.lt_irrefl _)
  have hatoms : m₁.atoms = m₂.atoms := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < m₁.atoms.length
    · exact (h.atoms i hi).symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hbonds : m₁.bonds = m₂.bonds := by
    apply eq_of_ordered_of_mem_iff w₁.2.1 w₂.2.1
    intro x
    obtain ⟨a, b, order⟩ := x
    constructor
    · intro hx
      obtain ⟨hab, hb⟩ := w₁.1 _ hx
      simp only at hab hb
      rcases (h.bonds a b order (by omega) hb).1 (Or.inl hx) with h' | h'
      · exact h'
      · have := (w₂.1 _ h').1
        simp only [id] at this
        omega
    · intro hx
      obtain ⟨hab, hb⟩ := w₂.1 _ hx
      simp only at hab hb
      rcases (h.bonds a b order (by omega) (by omega)).2 (Or.inl hx) with h' | h'
      · exact h'
      · have := (w₁.1 _ h').1
        simp only at this
        omega
  -- the two `Mol`s have the same fixed choices, so they store the same marks
  have hplaces : ∀ j, m₂.places j = m₁.places j := by
    intro j
    unfold Mol.places Mol.neighbours
    rw [hbonds]
  have hothers : ∀ a b, m₂.otherNeighbours a b = m₁.otherNeighbours a b := by
    intro a b
    unfold Mol.otherNeighbours Mol.neighbours
    rw [hbonds]
  have horientations : m₁.orientations = m₂.orientations := by
    apply Mol.orientations_ext w₁ w₂
    intro atom
    by_cases ha : atom < m₂.atoms.length
    · have key := h.stored_orientation w₂.graph ha
      rw [map_id_places, hplaces] at key
      simp only [id] at key
      rw [Mol.orientationOf_places w₁.graph] at key
      exact key.symm
    · cases h1 : m₁.orientationAt atom with
      | some o => exact absurd (Mol.fourPlaces_of_orientationAt w₁ h1).2 (by omega)
      | none =>
        cases h2 : m₂.orientationAt atom with
        | some o => exact absurd (Mol.fourPlaces_of_orientationAt w₂ h2).2 ha
        | none => rfl
  have hgeometries : m₁.geometries = m₂.geometries := by
    apply Mol.geometries_ext w₁ w₂
    intro a b
    -- where one of the two stores a mark, both have the double bond with its neighbours
    have hkey : ∀ x y, (⟨a, b, .double⟩ : Bond) ∈ m₁.bonds →
        (m₁.otherNeighbours a b).head? = some x → (m₁.otherNeighbours b a).head? = some y →
        m₂.geometryAt a b = m₁.geometryAt a b := by
      intro x y hbond hx hy
      have hab := (w₁.1 _ hbond).1
      simp only at hab
      have key := h.stored_geometry w₂.graph (hbonds ▸ hbond) (x := x) (y := y)
        (by rw [hothers]; exact hx) (by rw [hothers]; exact hy)
      simp only [id] at key
      rw [Mol.geometryOf_heads hab hx hy] at key
      exact key
    cases h1 : m₁.geometryAt a b with
    | some s₁ =>
      obtain ⟨hcan, hbond⟩ := Mol.canHave_of_geometryAt w₁ h1
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := Mol.heads_of_canHave hcan
      rw [hkey x y hbond hx hy, h1]
    | none =>
      cases h2 : m₂.geometryAt a b with
      | none => rfl
      | some s₂ =>
        obtain ⟨hcan, hbond⟩ := Mol.canHave_of_geometryAt w₂ h2
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := Mol.heads_of_canHave hcan
        rw [hothers] at hx hy
        rw [← hbonds] at hbond
        rw [← h2, hkey x y hbond hx hy, h1]
  cases m₁; cases m₂; simp_all

/-! ## Single examples

The definition says that a renumbering exists. Here is one case in which it
exists and one in which it does not. Lean works out what the reader returns
for the four texts while it checks the proofs. -/

/-- Whether two atoms are joined can be worked out. -/
instance (m : Mol) (i j : Nat) (order : BondOrder) : Decidable (m.Joined i j order) := by
  unfold Mol.Joined
  infer_instance

/-- Ethanol as `CCO` is read: the oxygen is atom 2. -/
def ethanolFromCarbon : Mol :=
  { atoms := [
      { element := .C, isotope := none, charge := 0, hydrogens := 3 },
      { element := .C, isotope := none, charge := 0, hydrogens := 2 },
      { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single } ] }

/-- Ethanol as `OCC` is read: the oxygen is atom 0. -/
def ethanolFromOxygen : Mol :=
  { atoms := [
      { element := .O, isotope := none, charge := 0, hydrogens := 1 },
      { element := .C, isotope := none, charge := 0, hydrogens := 2 },
      { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single } ] }

/-- Theorem 41 of CLAIMS.md. `CCO` and `OCC` are read as two different `Mol`s,
and they are the same molecule numbered differently: the second is the first
with its atoms numbered backwards. -/
theorem ethanol_renumbered :
    ∃ m₁ m₂, read "CCO".toList = .ok m₁ ∧ read "OCC".toList = .ok m₂ ∧
      m₁ ≠ m₂ ∧ m₁.Renumbered m₂ := by
  refine ⟨ethanolFromCarbon, ethanolFromOxygen, rfl, rfl, by decide, fun i => 2 - i,
    fun i => 2 - i, ?_⟩
  have small : ∀ i, i < 3 → i = 0 ∨ i = 1 ∨ i = 2 := by omega
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  · intro i hi
    have hi' : i < 3 := hi
    exact ⟨show 2 - i < 3 by omega, by omega⟩
  · intro j hj
    have hj' : j < 3 := hj
    exact ⟨show 2 - j < 3 by omega, by omega⟩
  · intro i hi
    rcases small i hi with rfl | rfl | rfl <;> rfl
  · intro i j order hi hj
    rcases small i hi with rfl | rfl | rfl <;> rcases small j hj with rfl | rfl | rfl <;>
      cases order <;> simp [Mol.Joined, ethanolFromCarbon, ethanolFromOxygen]

/-- A carbon atom with two hydrogens. -/
def ch2 : Atom := { element := .C, isotope := none, charge := 0, hydrogens := 2 }

/-- Cyclohexane, as `C1CCCCC1` is read: one ring of six. -/
def cyclohexane : Mol :=
  { atoms := [ch2, ch2, ch2, ch2, ch2, ch2],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 0, b := 5, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 2, b := 3, order := .single },
      { a := 3, b := 4, order := .single },
      { a := 4, b := 5, order := .single } ] }

/-- Two molecules of cyclopropane, as `C1CC1.C1CC1` is read: two rings of
three. -/
def twoCyclopropanes : Mol :=
  { atoms := [ch2, ch2, ch2, ch2, ch2, ch2],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 0, b := 2, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 3, b := 4, order := .single },
      { a := 3, b := 5, order := .single },
      { a := 4, b := 5, order := .single } ] }

/-- Theorem 42 of CLAIMS.md. `C1CCCCC1` (cyclohexane) and `C1CC1.C1CC1` (two
molecules of cyclopropane) are read as two `Mol`s with the same atoms and as
many bonds, and they are not the same molecule numbered differently. Only the
atom numbers in the bonds tell them apart (SPEC.md, section 3): three atoms
that are joined each to each exist in the one and not in the other. -/
theorem cyclohexane_not_renumbered :
    ∃ m₁ m₂, read "C1CCCCC1".toList = .ok m₁ ∧ read "C1CC1.C1CC1".toList = .ok m₂ ∧
      m₁.atoms = m₂.atoms ∧ m₁.bonds.length = m₂.bonds.length ∧ ¬ m₁.Renumbered m₂ := by
  refine ⟨cyclohexane, twoCyclopropanes, rfl, rfl, rfl, rfl, ?_⟩
  rintro ⟨f, g, h⟩
  -- no three atoms of cyclohexane are joined each to each
  have noTriangle : ∀ x, x < 6 → ∀ y, y < 6 → ∀ z, z < 6 →
      ¬ (cyclohexane.Joined x y .single ∧ cyclohexane.Joined y z .single ∧
        cyclohexane.Joined x z .single) := by
    decide
  -- two atoms that are joined in the two cyclopropanes come from two atoms
  -- that are joined in cyclohexane
  have back : ∀ a b, a < 6 → b < 6 → twoCyclopropanes.Joined a b .single →
      cyclohexane.Joined (g a) (g b) .single := by
    intro a b ha hb hab
    obtain ⟨hga, hfa⟩ := h.back a ha
    obtain ⟨hgb, hfb⟩ := h.back b hb
    have := (h.bonds (g a) (g b) .single hga hgb).2
    rw [hfa, hfb] at this
    exact this hab
  -- atoms 0, 1 and 2 of the two cyclopropanes are joined each to each
  exact noTriangle (g 0) (h.back 0 (by decide)).1 (g 1) (h.back 1 (by decide)).1
    (g 2) (h.back 2 (by decide)).1
    ⟨back 0 1 (by decide) (by decide) (by decide), back 1 2 (by decide) (by decide) (by decide),
     back 0 2 (by decide) (by decide) (by decide)⟩

/-! ## Single examples with stereo facts

Two texts for L-alanine store two different marks at the same atom, because
they number its neighbours differently, and they are the same molecule. The
text of the mirror image stores the mark of one of them, and it is not. -/

/-- L-alanine as `N[C@@H](C)C(=O)O` is read: the nitrogen is atom 0. -/
def alanineFromNitrogen : Mol :=
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
    geometries := [] }

/-- L-alanine as `C[C@H](N)C(=O)O` is read: the nitrogen is atom 2. -/
def alanineFromCarbon : Mol :=
  { atoms := [
      { element := .C, isotope := none, charge := 0, hydrogens := 3 },
      { element := .C, isotope := none, charge := 0, hydrogens := 1 },
      { element := .N, isotope := none, charge := 0, hydrogens := 2 },
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
      { atom := 1, orientation := .clockwise } ],
    geometries := [] }

/-- The mirror image of L-alanine, as `N[C@H](C)C(=O)O` is read: the `Mol` of
`N[C@@H](C)C(=O)O` with the other orientation at atom 1. -/
def mirroredAlanine : Mol :=
  { alanineFromNitrogen with orientations := [{ atom := 1, orientation := .clockwise }] }

/-- Theorem 43 of CLAIMS.md, first statement. `N[C@@H](C)C(=O)O` and
`C[C@H](N)C(=O)O` are read as two different `Mol`s, and they are the same
molecule numbered differently: the second is the first with the atoms 0 and 2
exchanged. The two store different marks for atom 1 (`alanineFromNitrogen` and
`alanineFromCarbon` above); the statement does not say that. -/
theorem alanine_renumbered :
    ∃ m₁ m₂, read "N[C@@H](C)C(=O)O".toList = .ok m₁ ∧ read "C[C@H](N)C(=O)O".toList = .ok m₂ ∧
      m₁ ≠ m₂ ∧ m₁.Renumbered m₂ := by
  have r₁ : read "N[C@@H](C)C(=O)O".toList = .ok alanineFromNitrogen := rfl
  have r₂ : read "C[C@H](N)C(=O)O".toList = .ok alanineFromCarbon := rfl
  refine ⟨alanineFromNitrogen, alanineFromCarbon, r₁, r₂, by decide,
    fun i => if i = 0 then 2 else if i = 2 then 0 else i,
    fun i => if i = 0 then 2 else if i = 2 then 0 else i, ?_⟩
  have w₁ := read_wellFormed _ _ r₁
  have w₂ := read_wellFormed _ _ r₂
  have small : ∀ i, i < 6 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  -- the atoms and the bonds; then the stored marks (`Mol.RenumberedBy.of_stored`)
  refine Mol.RenumberedBy.of_stored ⟨?_, ?_, ?_, ?_⟩ w₁ w₂ ?_ ?_
  · intro i hi
    rcases small i hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩
  · intro j hj
    rcases small j hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩
  · intro i hi
    rcases small i hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro i j order hi hj
    rcases small i hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases small j hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases order <;> simp [Mol.Joined, alanineFromNitrogen, alanineFromCarbon]
  · intro j hj
    rcases small j hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro bond _ x y _ _
    rw [Mol.geometryOf_of_nil rfl]
    rfl

/-- Theorem 43 of CLAIMS.md, second statement. `N[C@@H](C)C(=O)O` (L-alanine)
and `N[C@H](C)C(=O)O` (its mirror image) are read as two `Mol`s with the same
atoms and the same bonds, and they are not the same molecule numbered
differently. Only the stored orientation tells them apart. -/
theorem alanine_not_mirrored :
    ∃ m₁ m₂, read "N[C@@H](C)C(=O)O".toList = .ok m₁ ∧ read "N[C@H](C)C(=O)O".toList = .ok m₂ ∧
      m₁.atoms = m₂.atoms ∧ m₁.bonds = m₂.bonds ∧ ¬ m₁.Renumbered m₂ := by
  have r₁ : read "N[C@@H](C)C(=O)O".toList = .ok alanineFromNitrogen := rfl
  have r₂ : read "N[C@H](C)C(=O)O".toList = .ok mirroredAlanine := rfl
  refine ⟨alanineFromNitrogen, mirroredAlanine, r₁, r₂, rfl, rfl, ?_⟩
  rintro ⟨f, g, h⟩
  have small : ∀ i, i < 6 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  -- the six atoms of alanine are six different atoms, so no atom gets another number
  have hfix : ∀ i, i < 6 → f i = i := by
    intro i hi
    have hat := h.atoms i hi
    have hlt : f i < 6 := (h.forth i hi).1
    rcases small i hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases small (f _) hlt with e | e | e | e | e | e <;> rw [e] at hat <;>
      first | exact e | exact absurd hat (by decide)
  have hgfix : ∀ j, j < 6 → g j = j := by
    intro j hj
    obtain ⟨hg, hfg⟩ := h.back j hj
    rw [hfix (g j) hg] at hfg
    exact hfg
  -- so the two `Mol`s would be equal (theorem 21), and they are not
  have hid : Mol.RenumberedBy id id alanineFromNitrogen mirroredAlanine :=
    h.congr (fun i hi => (hfix i hi).symm) (fun j hj => (hgfix j hj).symm)
  exact absurd (Mol.eq_of_renumberedBy_id (read_wellFormed _ _ r₁) (read_wellFormed _ _ r₂) hid)
    (by decide)

end VeriMol
