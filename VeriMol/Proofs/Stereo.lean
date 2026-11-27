import VeriMol.Core.Read
import VeriMol.Core.Same

/-!
# The two statements about the arrangement in space (SPEC.md, section 12.1)

`VeriMol/Core/Stereo.lean` works two statements out from the marks that a `Mol`
stores: the orientation of an atom for its places in some order
(`Mol.orientationOf`), and the geometry of a double bond for two neighbours
(`Mol.geometryOf`). This file holds what the other proofs need about them:

1. what "well formed" gives for neighbours and places
   (`Mol.neighbours_rising`, `Mol.places_rising`), and where the stored marks
   stand (`Mol.orientationAt_eq_some`, `Mol.geometryAt_eq_some`); the proofs
   of the round trip use the last two as well;
2. for the fixed choice each statement gives the stored mark
   (`Mol.orientationOf_places`, `Mol.geometryOf_heads`);
3. if the atoms and the bonds of `m₂` are those of `m₁` under new numbers
   (`Mol.SameGraphBy`), and every mark that `m₂` stores is what `m₁` says for
   the fixed choice of `m₂`, then `m₂` is `m₁` numbered differently
   (`Mol.RenumberedBy.of_stored`). `VeriMol/Proofs/Same.lean` and
   `VeriMol/Proofs/Chosen.lean` show "numbered differently" in this way. The
   other way round, a `Mol` that is another one numbered differently stores
   these marks (`Mol.RenumberedBy.stored_orientation`,
   `Mol.RenumberedBy.stored_geometry`).

The statements ask that the `Mol` is well formed, or only that its atoms and
bonds are as a well formed `Mol` wants them (`Mol.GraphWellFormed`); the
docstrings do not repeat it.
-/

namespace VeriMol

/-! ## Counting swaps

Whether two orders of the same places differ by an even or an odd number of
swaps does not depend on how the places are numbered
(`fallingPairs_map_perm`). No theory of permutations is needed: the pairs
whose order the renumbering reverses are counted (`reversedPairs`), and that
count does not depend on the order of the list. -/

/-- Whether `f` reverses the order of `x` and `y`. It does not matter which of
the two is named first. -/
def reverses (f : Nat → Nat) (x y : Nat) : Bool :=
  (x < y && f y < f x) || (y < x && f x < f y)

/-- The number of pairs of a list whose order `f` reverses. -/
def reversedPairs (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: rest => (rest.filter (reverses f x)).length + reversedPairs f rest

theorem reverses_comm (f : Nat → Nat) (x y : Nat) : reverses f x y = reverses f y x := by
  simp [reverses, Bool.or_comm]

/-- If for every entry of a list exactly one of `p` and `q` holds exactly when
`r` holds, then the entries with `p` and the entries with `q`, counted
together, are odd exactly when the entries with `r` are. -/
theorem count_add_count (p q r : Nat → Bool) :
    ∀ l : List Nat, (∀ y ∈ l, (p y != q y) = r y) →
      ((l.filter p).length + (l.filter q).length) % 2 = (l.filter r).length % 2
  | [], _ => rfl
  | y :: l, h => by
    have ih := count_add_count p q r l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hy := h y List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p y <;> cases hq : q y <;> cases hr : r y <;> simp [hp, hq, hr] at hy ⊢ <;> omega

/-- The falling pairs of the renumbered list and those of the list itself are,
taken together, odd exactly when the pairs whose order the renumbering
reverses are. -/
theorem fallingPairs_map (f : Nat → Nat) :
    ∀ l : List Nat, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      (fallingPairs (l.map f) + fallingPairs l) % 2 = reversedPairs f l % 2
  | [], _, _ => rfl
  | x :: rest, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    have ih := fallingPairs_map f rest hnd.2
      (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    have hcount := count_add_count (fun y => decide (f y < f x)) (fun y => decide (y < x))
      (reverses f x) rest
      (by
        intro y hy
        have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
        have hfne : f y ≠ f x := fun h =>
          hne (hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self h)
        simp only [reverses]
        by_cases h1 : f y < f x <;> by_cases h2 : y < x <;> simp [h1, h2] <;> omega)
    have hmap : ((rest.map f).filter (· < f x)).length
        = (rest.filter (fun y => decide (f y < f x))).length := by
      rw [List.filter_map, List.length_map]; rfl
    simp only [List.map_cons, fallingPairs, reversedPairs, hmap]
    omega

/-- The number of pairs whose order `f` reverses is the same for every order
of the list. -/
theorem reversedPairs_perm (f : Nat → Nat) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    reversedPairs f l₁ = reversedPairs f l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [reversedPairs, ih]; rw [(List.Perm.filter _ ‹_›).length_eq]
  | swap x y l =>
    simp only [reversedPairs, List.filter_cons, reverses_comm f y x]
    cases reverses f x y <;> simp <;> omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Two orders of the same places differ by an even or an odd number of swaps,
and that does not depend on how the places are numbered. -/
theorem fallingPairs_map_perm (f : Nat → Nat) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) (hnd : l₁.Nodup)
    (hinj : ∀ x ∈ l₁, ∀ y ∈ l₁, f x = f y → x = y) :
    (fallingPairs (l₁.map f) + fallingPairs l₁) % 2
      = (fallingPairs (l₂.map f) + fallingPairs l₂) % 2 := by
  rw [fallingPairs_map f l₁ hnd hinj,
    fallingPairs_map f l₂ (h.nodup_iff.mp hnd)
      (fun x hx y hy => hinj x (h.mem_iff.mpr hx) y (h.mem_iff.mpr hy)),
    reversedPairs_perm f h]

/-- A list in rising order has no falling pair. -/
theorem fallingPairs_of_rising : ∀ l : List Nat, l.Pairwise (· < ·) → fallingPairs l = 0
  | [], _ => rfl
  | x :: rest, h => by
    rw [List.pairwise_cons] at h
    have : rest.filter (· < x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy
      have := h.1 y hy
      simp; omega
    simp [fallingPairs, this, fallingPairs_of_rising rest h.2]

/-! ## Turning a mark round -/

theorem Orientation.turnedIf_false (o : Orientation) : o.turnedIf false = o := rfl

theorem Orientation.turnedIf_turnedIf (o : Orientation) (s t : Bool) :
    (o.turnedIf s).turnedIf t = o.turnedIf (s != t) := by
  cases o <;> cases s <;> cases t <;> rfl

theorem Geometry.turnedIf_turnedIf (o : Geometry) (s t : Bool) :
    (o.turnedIf s).turnedIf t = o.turnedIf (s != t) := by
  cases o <;> cases s <;> cases t <;> rfl

/-! ## Lists in a strict order -/

/-- Two lists in the same strict order that hold the same entries are equal. -/
theorem eq_of_pairwise_of_mem_iff {α : Type} {r : α → α → Prop} (hirr : ∀ x, ¬ r x x)
    (hasym : ∀ x y, r x y → ¬ r y x) {l₁ l₂ : List α} (h₁ : l₁.Pairwise r) (h₂ : l₂.Pairwise r)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd ((h y).2 (List.mem_cons_self ..)) (by simp)
  | cons x xs ih =>
    cases l₂ with
    | nil => exact absurd ((h x).1 (List.mem_cons_self ..)) (by simp)
    | cons y ys =>
      rw [List.pairwise_cons] at h₁ h₂
      have hxy : x = y := by
        have hx := (h x).1 (List.mem_cons_self ..)
        have hy := (h y).2 (List.mem_cons_self ..)
        rcases List.mem_cons.1 hx with rfl | hx'
        · rfl
        · rcases List.mem_cons.1 hy with rfl | hy'
          · rfl
          · exact absurd (h₁.1 y hy') (hasym _ _ (h₂.1 x hx'))
      subst hxy
      congr 1
      apply ih h₁.2 h₂.2
      intro z
      constructor
      · intro hz
        rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (h₁.1 z hz) (hirr z)
        · exact hz'
      · intro hz
        rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (h₂.1 z hz) (hirr z)
        · exact hz'

/-- In a list in which no two entries have the property `p`, an entry that
has it is the one that `find?` finds. -/
theorem find?_of_pairwise {α : Type} {p : α → Bool} {l : List α} {x : α}
    (hl : l.Pairwise (fun a b => ¬ (p a = true ∧ p b = true))) (hx : x ∈ l) (hp : p x = true) :
    l.find? p = some x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    by_cases hy : p y = true
    · rcases List.mem_cons.1 hx with rfl | hx'
      · simp [hy]
      · exact absurd ⟨hy, hp⟩ (hl.1 x hx')
    · rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd hp hy
      · simp [hy, ih hl.2 hx']

/-! ## The neighbours of an atom -/

/-- The part of "well formed" that is about the atoms and the bonds. -/
def Mol.GraphWellFormed (m : Mol) : Prop :=
  (∀ bond ∈ m.bonds, bond.a < bond.b ∧ bond.b < m.atoms.length) ∧ m.bonds.Pairwise Bond.before

theorem Mol.WellFormed.graph {m : Mol} (w : m.WellFormed) : m.GraphWellFormed := ⟨w.1, w.2.1⟩

/-- The neighbours of an atom are the atoms that it is joined to. -/
theorem Mol.mem_neighbours {m : Mol} {atom x : Nat} :
    x ∈ m.neighbours atom ↔ ∃ order, m.Joined atom x order := by
  unfold Mol.neighbours Mol.Joined
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨bond, hbond, hx⟩
    obtain ⟨a, b, order⟩ := bond
    simp only at hx
    split at hx
    · rename_i hb
      cases hx
      subst hb
      exact ⟨order, Or.inr hbond⟩
    · split at hx
      · rename_i ha
        cases hx
        subst ha
        exact ⟨order, Or.inl hbond⟩
      · cases hx
  · rintro ⟨order, h | h⟩
    · refine ⟨_, h, ?_⟩
      by_cases hx : x = atom
      · simp [hx]
      · simp [hx]
    · exact ⟨_, h, by simp⟩

/-- A neighbour is another atom of the `Mol`. -/
theorem Mol.neighbours_lt {m : Mol} (w : m.GraphWellFormed) {atom x : Nat}
    (h : x ∈ m.neighbours atom) : x < m.atoms.length ∧ atom < m.atoms.length ∧ x ≠ atom := by
  obtain ⟨order, h | h⟩ := Mol.mem_neighbours.1 h
  · have := w.1 _ h
    simp only at this
    omega
  · have := w.1 _ h
    simp only at this
    omega

/-- Two atoms that are joined by a bond are atoms of the `Mol`. -/
theorem Mol.Joined.lt {m : Mol} (w : m.GraphWellFormed) {i j : Nat} {order : BondOrder}
    (h : m.Joined i j order) : i < m.atoms.length ∧ j < m.atoms.length := by
  rcases h with h | h
  · have := w.1 _ h
    simp only at this
    omega
  · have := w.1 _ h
    simp only at this
    omega

/-- The neighbours of an atom stand in rising order. -/
theorem Mol.neighbours_rising {m : Mol} (w : m.GraphWellFormed) (atom : Nat) :
    (m.neighbours atom).Pairwise (· < ·) := by
  unfold Mol.neighbours
  refine List.Pairwise.filterMap _ ?_ (w.2.imp_of_mem (R := Bond.before)
    (S := fun x y => Bond.before x y ∧ x.a < x.b ∧ y.a < y.b) ?_)
  · intro x y hxy n hn n' hn'
    obtain ⟨hbefore, hx, hy⟩ := hxy
    unfold Bond.before at hbefore
    split at hn
    · cases hn
      split at hn'
      · cases hn'; omega
      · split at hn'
        · cases hn'; omega
        · cases hn'
    · split at hn
      · cases hn
        split at hn'
        · cases hn'; omega
        · split at hn'
          · cases hn'; omega
          · cases hn'
      · cases hn
  · intro x y hx hy hxy
    exact ⟨hxy, (w.1 x hx).1, (w.1 y hy).1⟩

theorem Mol.neighbours_nodup {m : Mol} (w : m.GraphWellFormed) (atom : Nat) :
    (m.neighbours atom).Nodup :=
  (Mol.neighbours_rising w atom).imp (fun h => Nat.ne_of_lt h)

theorem Mol.mem_otherNeighbours {m : Mol} {atom partner x : Nat} :
    x ∈ m.otherNeighbours atom partner ↔ x ∈ m.neighbours atom ∧ x ≠ partner := by
  simp [Mol.otherNeighbours]

theorem Mol.otherNeighbours_nodup {m : Mol} (w : m.GraphWellFormed) (atom partner : Nat) :
    (m.otherNeighbours atom partner).Nodup :=
  (Mol.neighbours_nodup w atom).sublist List.filter_sublist

/-- The places of an atom in the fixed order stand in the rising order of
their numbers. -/
theorem Mol.places_rising {m : Mol} (w : m.GraphWellFormed) (atom : Nat) :
    ((m.places atom).map placeCode).Pairwise (· < ·) := by
  have hn : ((m.neighbours atom).map some |>.map placeCode).Pairwise (· < ·) := by
    rw [List.map_map, List.pairwise_map]
    exact (Mol.neighbours_rising w atom).imp
      (fun h => by simp only [Function.comp, placeCode]; omega)
  unfold Mol.places
  split
  · simp only [List.map_cons, List.singleton_append, List.pairwise_cons]
    refine ⟨?_, hn⟩
    intro c hc
    simp only [List.map_map, List.mem_map, Function.comp, placeCode] at hc
    obtain ⟨x, _, rfl⟩ := hc
    simp only [placeCode]
    omega
  · simpa using hn

/-- The places of an atom that hold an atom are exactly its neighbours. -/
theorem Mol.mem_places {m : Mol} {atom x : Nat} :
    some x ∈ m.places atom ↔ x ∈ m.neighbours atom := by
  unfold Mol.places
  split <;> simp

/-! ## The stored marks -/

/-- The mark that is stored for an atom is the mark of its entry in the list. -/
theorem Mol.orientationAt_eq_some {m : Mol} (w : m.WellFormed) {atom : Nat} {o : Orientation} :
    m.orientationAt atom = some o ↔ ⟨atom, o⟩ ∈ m.orientations := by
  unfold Mol.orientationAt
  constructor
  · intro h
    obtain ⟨x, hx, ho⟩ := Option.map_eq_some_iff.1 h
    have hmem := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    obtain ⟨a, o'⟩ := x
    simp only [beq_iff_eq] at hp
    simp only at ho
    subst hp ho
    exact hmem
  · intro h
    have hfind : (m.orientations.find? fun x => x.atom == atom) = some ⟨atom, o⟩ := by
      refine find?_of_pairwise (w.2.2.1.imp ?_) h (by simp)
      intro a b hab hboth
      simp only [beq_iff_eq] at hboth
      omega
    rw [hfind]
    rfl

/-- The mark that is stored for a double bond is the mark of its entry in the
list. -/
theorem Mol.geometryAt_eq_some {m : Mol} (w : m.WellFormed) {a b : Nat} {s : Geometry} :
    m.geometryAt a b = some s ↔ ⟨a, b, s⟩ ∈ m.geometries := by
  unfold Mol.geometryAt
  constructor
  · intro h
    obtain ⟨x, hx, ho⟩ := Option.map_eq_some_iff.1 h
    have hmem := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    obtain ⟨a', b', s'⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    simp only at ho
    obtain ⟨rfl, rfl⟩ := hp
    subst ho
    exact hmem
  · intro h
    have hfind : (m.geometries.find? fun x => x.a == a && x.b == b) = some ⟨a, b, s⟩ := by
      refine find?_of_pairwise (w.2.2.2.2.1.imp ?_) h (by simp)
      intro x y hxy hboth
      simp only [Bool.and_eq_true, beq_iff_eq] at hboth
      omega
    rw [hfind]
    rfl

/-- An atom with an orientation is an atom of the `Mol` with four places. -/
theorem Mol.fourPlaces_of_orientationAt {m : Mol} (w : m.WellFormed) {atom : Nat} {o : Orientation}
    (h : m.orientationAt atom = some o) :
    m.hasFourPlaces atom = true ∧ atom < m.atoms.length := by
  have hfour : m.hasFourPlaces atom = true :=
    w.2.2.2.1 ⟨atom, o⟩ ((Mol.orientationAt_eq_some w).1 h)
  refine ⟨hfour, ?_⟩
  unfold Mol.hasFourPlaces at hfour
  apply Classical.byContradiction
  intro hnot
  rw [List.getElem?_eq_none (by omega)] at hfour
  cases hfour

/-- A double bond with a geometry is a double bond of the `Mol` that can have
one. -/
theorem Mol.canHave_of_geometryAt {m : Mol} (w : m.WellFormed) {a b : Nat} {s : Geometry}
    (h : m.geometryAt a b = some s) :
    m.canHaveGeometry a b = true ∧ (⟨a, b, .double⟩ : Bond) ∈ m.bonds := by
  have hcan : m.canHaveGeometry a b = true :=
    w.2.2.2.2.2 ⟨a, b, s⟩ ((Mol.geometryAt_eq_some w).1 h)
  refine ⟨hcan, ?_⟩
  unfold Mol.canHaveGeometry at hcan
  simp only [Bool.and_eq_true] at hcan
  simpa using hcan.1.1

/-- Two well formed `Mol`s that store the same mark for every atom have the
same list of orientations. -/
theorem Mol.orientations_ext {m m' : Mol} (w : m.WellFormed) (w' : m'.WellFormed)
    (h : ∀ atom, m.orientationAt atom = m'.orientationAt atom) :
    m.orientations = m'.orientations := by
  refine eq_of_pairwise_of_mem_iff (r := fun x y : AtomOrientation => x.atom < y.atom)
    (fun x => Nat.lt_irrefl _) (fun x y hxy => Nat.lt_asymm hxy) w.2.2.1 w'.2.2.1 ?_
  rintro ⟨atom, o⟩
  rw [← Mol.orientationAt_eq_some w, ← Mol.orientationAt_eq_some w', h]

/-- Two well formed `Mol`s that store the same mark for every pair of atoms
have the same list of geometries. -/
theorem Mol.geometries_ext {m m' : Mol} (w : m.WellFormed) (w' : m'.WellFormed)
    (h : ∀ a b, m.geometryAt a b = m'.geometryAt a b) :
    m.geometries = m'.geometries := by
  refine eq_of_pairwise_of_mem_iff
    (r := fun x y : BondGeometry => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b))
    (fun x => by omega) (fun x y hxy => by omega) w.2.2.2.2.1 w'.2.2.2.2.1 ?_
  rintro ⟨a, b, s⟩
  rw [← Mol.geometryAt_eq_some w, ← Mol.geometryAt_eq_some w', h]

/-! ## The two statements for the fixed choice -/

/-- For the places in the fixed order, the first statement gives the stored
mark. -/
theorem Mol.orientationOf_places {m : Mol} (w : m.GraphWellFormed) (atom : Nat) :
    m.orientationOf atom (m.places atom) = m.orientationAt atom := by
  unfold Mol.orientationOf
  cases m.orientationAt atom with
  | none => rfl
  | some stored =>
    simp only [List.Perm.refl, ↓reduceIte, fallingPairs_of_rising _ (Mol.places_rising w atom)]
    rfl

/-- The second statement does not depend on which of the two atoms of the
double bond is named first. -/
theorem Mol.geometryOf_comm (m : Mol) (a b x y : Nat) :
    m.geometryOf b a y x = m.geometryOf a b x y := by
  unfold Mol.geometryOf
  rw [Nat.min_comm b a, Nat.max_comm b a]
  cases m.geometryAt (min a b) (max a b) with
  | none => rfl
  | some stored =>
    simp only
    rw [Bool.and_comm]
    split
    · congr 2
      exact bne_comm
    · rfl

/-- For the lowest-numbered neighbours, the second statement gives the stored
mark. -/
theorem Mol.geometryOf_heads {m : Mol} {a b x y : Nat} (hab : a < b)
    (hx : (m.otherNeighbours a b).head? = some x) (hy : (m.otherNeighbours b a).head? = some y) :
    m.geometryOf a b x y = m.geometryAt a b := by
  unfold Mol.geometryOf
  rw [Nat.min_eq_left (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt hab)]
  cases m.geometryAt a b with
  | none => rfl
  | some stored =>
    have h1 : x ∈ m.otherNeighbours a b := List.mem_of_mem_head? hx
    have h2 : y ∈ m.otherNeighbours b a := List.mem_of_mem_head? hy
    simp [h1, h2, hx, hy, Geometry.turnedIf]

/-! ## The same atoms and bonds under new numbers -/

/-- The part of `Mol.RenumberedBy` that is about the atoms and the bonds. -/
structure Mol.SameGraphBy (f g : Nat → Nat) (m₁ m₂ : Mol) : Prop where
  forth : ∀ i, i < m₁.atoms.length → f i < m₂.atoms.length ∧ g (f i) = i
  back : ∀ j, j < m₂.atoms.length → g j < m₁.atoms.length ∧ f (g j) = j
  atoms : ∀ i, i < m₁.atoms.length → m₂.atoms[f i]? = m₁.atoms[i]?
  bonds : ∀ i j order, i < m₁.atoms.length → j < m₁.atoms.length →
    (m₁.Joined i j order ↔ m₂.Joined (f i) (f j) order)

theorem Mol.RenumberedBy.sameGraph {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) : Mol.SameGraphBy f g m₁ m₂ :=
  ⟨h.forth, h.back, h.atoms, h.bonds⟩

theorem Mol.SameGraphBy.symm {f g : Nat → Nat} {m₁ m₂ : Mol} (hf : Mol.SameGraphBy f g m₁ m₂) :
    Mol.SameGraphBy g f m₂ m₁ := by
  refine ⟨hf.back, hf.forth, ?_, ?_⟩
  · intro j hj
    obtain ⟨hg, hfg⟩ := hf.back j hj
    have := hf.atoms (g j) hg
    rw [hfg] at this
    exact this.symm
  · intro i j order hi hj
    obtain ⟨hgi, hfgi⟩ := hf.back i hi
    obtain ⟨hgj, hfgj⟩ := hf.back j hj
    have := hf.bonds (g i) (g j) order hgi hgj
    rw [hfgi, hfgj] at this
    exact this.symm

/-- The new numbers are different for different atoms. -/
theorem Mol.SameGraphBy.injective {f g : Nat → Nat} {m₁ m₂ : Mol} (h : Mol.SameGraphBy f g m₁ m₂)
    {i j : Nat} (hi : i < m₁.atoms.length) (hj : j < m₁.atoms.length) (e : f i = f j) : i = j := by
  rw [← (h.forth i hi).2, e, (h.forth j hj).2]

/-- The neighbours of an atom are its neighbours at their new numbers. -/
theorem Mol.SameGraphBy.mem_neighbours {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) {atom x : Nat} (ha : atom < m₁.atoms.length)
    (hx : x < m₁.atoms.length) : f x ∈ m₂.neighbours (f atom) ↔ x ∈ m₁.neighbours atom := by
  rw [Mol.mem_neighbours, Mol.mem_neighbours]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, (h.bonds atom x o ha hx).2 ho⟩
  · rintro ⟨o, ho⟩
    exact ⟨o, (h.bonds atom x o ha hx).1 ho⟩

theorem Mol.SameGraphBy.neighbours_perm {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {atom : Nat} (ha : atom < m₁.atoms.length) :
    (m₂.neighbours (f atom)).Perm ((m₁.neighbours atom).map f) := by
  have hnd : ((m₁.neighbours atom).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine (Mol.neighbours_nodup w₁ atom).imp_of_mem ?_
    intro x y hx hy hxy e
    exact hxy (h.injective (Mol.neighbours_lt w₁ hx).1 (Mol.neighbours_lt w₁ hy).1 e)
  rw [List.perm_ext_iff_of_nodup (Mol.neighbours_nodup w₂ _) hnd]
  intro y
  constructor
  · intro hy
    have hylt := (Mol.neighbours_lt w₂ hy).1
    obtain ⟨hgy, hfgy⟩ := h.back y hylt
    rw [← hfgy] at hy
    exact List.mem_map.2 ⟨g y, (h.mem_neighbours ha hgy).1 hy, hfgy⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact (h.mem_neighbours ha (Mol.neighbours_lt w₁ hx).1).2 hx

theorem Mol.SameGraphBy.places_perm {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {atom : Nat} (ha : atom < m₁.atoms.length) :
    (m₂.places (f atom)).Perm ((m₁.places atom).map (Option.map f)) := by
  have hp := h.neighbours_perm w₁ w₂ ha
  have hlen : (m₂.neighbours (f atom)).length = (m₁.neighbours atom).length := by
    simpa using hp.length_eq
  have hsome : ((m₂.neighbours (f atom)).map some).Perm
      (((m₁.neighbours atom).map some).map (Option.map f)) := by
    have := hp.map some
    rw [List.map_map] at this
    rw [List.map_map]
    exact this
  unfold Mol.places
  rw [hlen]
  split
  · simp only [List.map_append, List.map_cons, List.map_nil, Option.map_none]
    exact List.Perm.append (List.Perm.refl _) hsome
  · simpa using hsome

/-- The other neighbours of an atom are its other neighbours at their new
numbers. -/
theorem Mol.SameGraphBy.mem_otherNeighbours {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) {atom partner x : Nat} (ha : atom < m₁.atoms.length)
    (hp : partner < m₁.atoms.length) (hx : x < m₁.atoms.length) :
    f x ∈ m₂.otherNeighbours (f atom) (f partner) ↔ x ∈ m₁.otherNeighbours atom partner := by
  rw [Mol.mem_otherNeighbours, Mol.mem_otherNeighbours, h.mem_neighbours ha hx]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e => h2 (by rw [e])⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e => h2 (h.injective hx hp e)⟩

theorem Mol.SameGraphBy.otherNeighbours_length {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {atom partner : Nat} (ha : atom < m₁.atoms.length) (hp : partner < m₁.atoms.length) :
    (m₂.otherNeighbours (f atom) (f partner)).length =
      (m₁.otherNeighbours atom partner).length := by
  have hnd : ((m₁.otherNeighbours atom partner).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine (Mol.otherNeighbours_nodup w₁ atom partner).imp_of_mem ?_
    intro x y hx hy hxy e
    exact hxy (h.injective (Mol.neighbours_lt w₁ (Mol.mem_otherNeighbours.1 hx).1).1
      (Mol.neighbours_lt w₁ (Mol.mem_otherNeighbours.1 hy).1).1 e)
  have hperm : (m₂.otherNeighbours (f atom) (f partner)).Perm
      ((m₁.otherNeighbours atom partner).map f) := by
    rw [List.perm_ext_iff_of_nodup (Mol.otherNeighbours_nodup w₂ _ _) hnd]
    intro y
    constructor
    · intro hy
      have hylt := (Mol.neighbours_lt w₂ (Mol.mem_otherNeighbours.1 hy).1).1
      obtain ⟨hgy, hfgy⟩ := h.back y hylt
      rw [← hfgy] at hy
      exact List.mem_map.2 ⟨g y, (h.mem_otherNeighbours ha hp hgy).1 hy, hfgy⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (h.mem_otherNeighbours ha hp
        (Mol.neighbours_lt w₁ (Mol.mem_otherNeighbours.1 hx).1).1).2 hx
  simpa using hperm.length_eq

/-! ## From the stored marks to the two statements

When the atoms get new numbers, the fixed order of the places of an atom
changes, and so can the stored mark. What follows says how the stored marks
of the two `Mol`s must be related so that the two statements carry over, and
that they are related so whenever the statements carry over. -/

/-- A renumbering of the atoms, as a renumbering of the numbers of the
places. -/
def codeMap (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | code + 1 => f code + 1

theorem map_placeCode_map (f : Nat → Nat) (l : List Place) :
    (l.map (Option.map f)).map placeCode = (l.map placeCode).map (codeMap f) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, ih]
    cases p <;> rfl

/-- Renumbering the places and then renumbering them back gives the places. -/
theorem map_map_places {f g : Nat → Nat} {l : List Place}
    (h : ∀ i, some i ∈ l → g (f i) = i) : (l.map (Option.map f)).map (Option.map g) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    cases x with
    | none => rfl
    | some i => simp [h i List.mem_cons_self]

theorem parity_of_sum {a b c : Nat} (h : (b + c) % 2 = a % 2) :
    ((a % 2 == 1) != (b % 2 == 1)) = (c % 2 == 1) := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  have hc := Nat.mod_two_eq_zero_or_one c
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    simp [ha, hb, hc] <;> omega

/-- **The first statement carries over** when the stored mark of the atom at
its new number is what the old `Mol` says for the new fixed order of its
places. -/
theorem Mol.SameGraphBy.orientationOf_eq {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {atom : Nat} (ha : atom < m₁.atoms.length)
    (hstored : m₂.orientationAt (f atom)
      = m₁.orientationOf atom ((m₂.places (f atom)).map (Option.map g)))
    (places : List Place) (hplaces : ∀ i, some i ∈ places → i < m₁.atoms.length) :
    m₂.orientationOf (f atom) (places.map (Option.map f)) = m₁.orientationOf atom places := by
  -- the new fixed order, said with the old numbers, holds the old places
  have hback : ∀ i, some i ∈ m₂.places (f atom) → f (g i) = i := by
    intro i hi
    exact (h.back i (Mol.neighbours_lt w₂ (Mol.mem_places.1 hi)).1).2
  have hQ : ((m₂.places (f atom)).map (Option.map g)).Perm (m₁.places atom) := by
    have := (h.places_perm w₁ w₂ ha).map (Option.map g)
    rw [map_map_places (fun i hi =>
      (h.forth i (Mol.neighbours_lt w₁ (Mol.mem_places.1 hi)).1).2)] at this
    exact this
  have hstored' : m₂.orientationAt (f atom) = (m₁.orientationAt atom).map (fun s =>
      s.turnedIf
        (fallingPairs (((m₂.places (f atom)).map (Option.map g)).map placeCode) % 2 == 1)) := by
    rw [hstored]
    unfold Mol.orientationOf
    cases m₁.orientationAt atom with
    | none => rfl
    | some s => simp [hQ]
  unfold Mol.orientationOf
  rw [hstored']
  cases m₁.orientationAt atom with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    by_cases hperm : places.Perm (m₁.places atom)
    · have hperm₂ : (places.map (Option.map f)).Perm (m₂.places (f atom)) :=
        (hperm.map _).trans (h.places_perm w₁ w₂ ha).symm
      simp only [hperm, hperm₂, ↓reduceIte, Option.some.injEq]
      rw [Orientation.turnedIf_turnedIf]
      congr 1
      rw [map_placeCode_map f places, map_placeCode_map g (m₂.places (f atom))]
      apply parity_of_sum
      -- the codes of the places, and the codes of the new fixed order
      have hLperm : (places.map placeCode).Perm
          (((m₂.places (f atom)).map placeCode).map (codeMap g)) := by
        rw [← map_placeCode_map]
        exact (hperm.trans hQ.symm).map placeCode
      have hnd : (places.map placeCode).Nodup := by
        have hrise := (Mol.places_rising w₁ atom).imp (fun {a b} (hab : a < b) => Nat.ne_of_lt hab)
        exact ((hperm.map placeCode).nodup_iff).2 hrise
      have hinj : ∀ x ∈ places.map placeCode, ∀ y ∈ places.map placeCode,
          codeMap f x = codeMap f y → x = y := by
        intro x hx y hy e
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        cases p with
        | none =>
          cases q with
          | none => rfl
          | some j => simp [placeCode, codeMap] at e
        | some i =>
          cases q with
          | none => simp [placeCode, codeMap] at e
          | some j =>
            simp only [placeCode, codeMap, Nat.add_right_cancel_iff] at e
            rw [h.injective (hplaces i hp) (hplaces j hq) e]
      have hround : (((m₂.places (f atom)).map placeCode).map (codeMap g)).map (codeMap f)
          = (m₂.places (f atom)).map placeCode := by
        rw [← map_placeCode_map, ← map_placeCode_map, map_map_places hback]
      have key := fallingPairs_map_perm (codeMap f) hLperm hnd hinj
      rw [hround, fallingPairs_of_rising _ (Mol.places_rising w₂ (f atom))] at key
      omega
    · have hperm₂ : ¬ (places.map (Option.map f)).Perm (m₂.places (f atom)) := by
        intro hp
        apply hperm
        have := hp.map (Option.map g)
        rw [map_map_places (fun i hi => (h.forth i (hplaces i hi)).2)] at this
        exact this.trans hQ
      simp only [hperm, hperm₂, ↓reduceIte]

/-- In a list of at most two entries that holds an entry `u` other than its
first one, every entry is the first one or `u`. -/
theorem eq_head_or_of_length_le_two {l : List Nat} {first u x : Nat} (hlen : l.length ≤ 2)
    (hfirst : l.head? = some first) (hu : u ∈ l) (hx : x ∈ l) (hne : first ≠ u) :
    x = first ∨ x = u := by
  match l, hlen, hfirst, hu, hx with
  | [a], _, hfirst, hu, hx =>
    simp only [List.head?_cons, Option.some.injEq] at hfirst
    simp only [List.mem_singleton] at hu hx
    omega
  | [a, b], _, hfirst, hu, hx =>
    simp only [List.head?_cons, Option.some.injEq] at hfirst
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hx
    omega

/-- On one side of a double bond: going from the first neighbour to `u` and
from `u` to `x` turns the answer as often as going from the first neighbour
to `x`. -/
theorem side_turns {l : List Nat} {first u x : Nat} (hlen : l.length ≤ 2)
    (hfirst : l.head? = some first) (hu : u ∈ l) (hx : x ∈ l) :
    ((first == u) != (u == x)) = !(first == x) := by
  by_cases h1 : first = u
  · have e1 : (first == u) = true := by simpa using h1
    by_cases h2 : u = x
    · have e2 : (u == x) = true := by simpa using h2
      have e3 : (first == x) = true := by simpa using h1.trans h2
      rw [e1, e2, e3]
      rfl
    · have e2 : (u == x) = false := by simpa using h2
      have e3 : (first == x) = false := by
        have : ¬ first = x := fun e => h2 (h1.symm.trans e)
        simpa using this
      rw [e1, e2, e3]
      rfl
  · have e1 : (first == u) = false := by simpa using h1
    by_cases h2 : u = x
    · have e2 : (u == x) = true := by simpa using h2
      have e3 : (first == x) = false := by
        have : ¬ first = x := fun e => h1 (e.trans h2.symm)
        simpa using this
      rw [e1, e2, e3]
      rfl
    · have e2 : (u == x) = false := by simpa using h2
      have e3 : (first == x) = true := by
        rcases eq_head_or_of_length_le_two hlen hfirst hu hx h1 with h3 | h3
        · simpa using h3.symm
        · exact absurd h3.symm h2
      rw [e1, e2, e3]
      rfl

theorem bne_of_sides (p p' q q' r r' : Bool) (h : (p != q) = !r) (h' : (p' != q') = !r') :
    ((p != p') != (q != q')) = (r != r') := by
  cases p <;> cases p' <;> cases q <;> cases q' <;> cases r <;> cases r' <;> simp_all

/-- **The second statement carries over** when the stored mark of the double
bond at its new numbers is what the old `Mol` says for the new
lowest-numbered neighbours. -/
theorem Mol.SameGraphBy.geometryOf_eq {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.GraphWellFormed)
    {a b : Nat} (ha : a < m₁.atoms.length) (hb : b < m₁.atoms.length)
    (hstored : ∀ x' y', (m₂.otherNeighbours (f a) (f b)).head? = some x' →
      (m₂.otherNeighbours (f b) (f a)).head? = some y' →
      m₂.geometryAt (min (f a) (f b)) (max (f a) (f b)) = m₁.geometryOf a b (g x') (g y'))
    {x y : Nat} (hx : x < m₁.atoms.length) (hy : y < m₁.atoms.length) :
    m₂.geometryOf (f a) (f b) (f x) (f y) = m₁.geometryOf a b x y := by
  have hmemx := h.mem_otherNeighbours ha hb hx
  have hmemy := h.mem_otherNeighbours hb ha hy
  by_cases hin : x ∈ m₁.otherNeighbours a b ∧ y ∈ m₁.otherNeighbours b a
  · obtain ⟨hx1, hy1⟩ := hin
    have hx2 := hmemx.2 hx1
    have hy2 := hmemy.2 hy1
    -- the lowest-numbered neighbours, old and new
    obtain ⟨x₁, hx₁⟩ : ∃ x₁, (m₁.otherNeighbours a b).head? = some x₁ := by
      cases hl : m₁.otherNeighbours a b with
      | nil => rw [hl] at hx1; cases hx1
      | cons z _ => exact ⟨z, rfl⟩
    obtain ⟨y₁, hy₁⟩ : ∃ y₁, (m₁.otherNeighbours b a).head? = some y₁ := by
      cases hl : m₁.otherNeighbours b a with
      | nil => rw [hl] at hy1; cases hy1
      | cons z _ => exact ⟨z, rfl⟩
    obtain ⟨x₂, hx₂⟩ : ∃ x₂, (m₂.otherNeighbours (f a) (f b)).head? = some x₂ := by
      cases hl : m₂.otherNeighbours (f a) (f b) with
      | nil => rw [hl] at hx2; cases hx2
      | cons z _ => exact ⟨z, rfl⟩
    obtain ⟨y₂, hy₂⟩ : ∃ y₂, (m₂.otherNeighbours (f b) (f a)).head? = some y₂ := by
      cases hl : m₂.otherNeighbours (f b) (f a) with
      | nil => rw [hl] at hy2; cases hy2
      | cons z _ => exact ⟨z, rfl⟩
    have hx₂mem := List.mem_of_mem_head? hx₂
    have hy₂mem := List.mem_of_mem_head? hy₂
    obtain ⟨hgx, hfgx⟩ := h.back x₂ (Mol.neighbours_lt w₂ (Mol.mem_otherNeighbours.1 hx₂mem).1).1
    obtain ⟨hgy, hfgy⟩ := h.back y₂ (Mol.neighbours_lt w₂ (Mol.mem_otherNeighbours.1 hy₂mem).1).1
    have hu : g x₂ ∈ m₁.otherNeighbours a b := by
      rw [← hfgx] at hx₂mem
      exact (h.mem_otherNeighbours ha hb hgx).1 hx₂mem
    have hv : g y₂ ∈ m₁.otherNeighbours b a := by
      rw [← hfgy] at hy₂mem
      exact (h.mem_otherNeighbours hb ha hgy).1 hy₂mem
    have hst := hstored x₂ y₂ hx₂ hy₂
    unfold Mol.geometryOf at hst ⊢
    rw [hst]
    cases hs : m₁.geometryAt (min a b) (max a b) with
    | none => rfl
    | some s =>
      -- each of the two atoms has at most two other neighbours
      have hcan := (Mol.canHave_of_geometryAt w₁ hs).1
      have hlens : (m₁.otherNeighbours a b).length ≤ 2 ∧ (m₁.otherNeighbours b a).length ≤ 2 := by
        unfold Mol.canHaveGeometry at hcan
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcan
        rcases Nat.le_total a b with hab | hab
        · rw [Nat.min_eq_left hab, Nat.max_eq_right hab] at hcan
          omega
        · rw [Nat.min_eq_right hab, Nat.max_eq_left hab] at hcan
          omega
      have e1 : (x₂ == f x) = (g x₂ == x) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        constructor
        · intro e
          rw [e, (h.forth x hx).2]
        · intro e
          rw [← e, hfgx]
      have e2 : (y₂ == f y) = (g y₂ == y) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        constructor
        · intro e
          rw [e, (h.forth y hy).2]
        · intro e
          rw [← e, hfgy]
      have hside1 := side_turns hlens.1 hx₁ hu hx1
      have hside2 := side_turns hlens.2 hy₁ hv hy1
      have hturn := bne_of_sides _ _ _ _ _ _ hside1 hside2
      have c1 : (m₁.otherNeighbours a b).contains (g x₂) = true := by simpa using hu
      have c2 : (m₁.otherNeighbours b a).contains (g y₂) = true := by simpa using hv
      have c3 : (m₁.otherNeighbours a b).contains x = true := by simpa using hx1
      have c4 : (m₁.otherNeighbours b a).contains y = true := by simpa using hy1
      have c5 : (m₂.otherNeighbours (f a) (f b)).contains (f x) = true := by simpa using hx2
      have c6 : (m₂.otherNeighbours (f b) (f a)).contains (f y) = true := by simpa using hy2
      simp only [c1, c2, c3, c4, c5, c6, Bool.and_self, ↓reduceIte,
        hx₁, hy₁, hx₂, hy₂, Option.some_beq_some, e1, e2, Geometry.turnedIf_turnedIf, hturn]
  · -- `x` or `y` is no neighbour of its atom: neither `Mol` answers
    have hin₂ : ¬ (f x ∈ m₂.otherNeighbours (f a) (f b)
        ∧ f y ∈ m₂.otherNeighbours (f b) (f a)) := by
      rintro ⟨h1, h2⟩
      exact hin ⟨hmemx.1 h1, hmemy.1 h2⟩
    have hc₁ : ((m₁.otherNeighbours a b).contains x
        && (m₁.otherNeighbours b a).contains y) = false := by
      by_cases hxm : x ∈ m₁.otherNeighbours a b
      · have hym : y ∉ m₁.otherNeighbours b a := fun hy' => hin ⟨hxm, hy'⟩
        have : (m₁.otherNeighbours b a).contains y = false := by simpa using hym
        rw [this, Bool.and_false]
      · have : (m₁.otherNeighbours a b).contains x = false := by simpa using hxm
        rw [this, Bool.false_and]
    have hc₂ : ((m₂.otherNeighbours (f a) (f b)).contains (f x)
        && (m₂.otherNeighbours (f b) (f a)).contains (f y)) = false := by
      by_cases hxm : f x ∈ m₂.otherNeighbours (f a) (f b)
      · have hym : f y ∉ m₂.otherNeighbours (f b) (f a) := fun hy' => hin₂ ⟨hxm, hy'⟩
        have : (m₂.otherNeighbours (f b) (f a)).contains (f y) = false := by simpa using hym
        rw [this, Bool.and_false]
      · have : (m₂.otherNeighbours (f a) (f b)).contains (f x) = false := by simpa using hxm
        rw [this, Bool.false_and]
    unfold Mol.geometryOf
    rw [hc₁, hc₂]
    cases m₂.geometryAt (min (f a) (f b)) (max (f a) (f b)) <;>
      cases m₁.geometryAt (min a b) (max a b) <;> rfl

/-- **From the stored marks to "numbered differently".** If the atoms and the
bonds of `m₂` are those of `m₁` under new numbers, and every stored mark of
`m₂` is what `m₁` says for the fixed choice of `m₂`, then `m₂` is `m₁`
numbered differently. -/
theorem Mol.RenumberedBy.of_stored {f g : Nat → Nat} {m₁ m₂ : Mol} (h : Mol.SameGraphBy f g m₁ m₂)
    (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (ho : ∀ j, j < m₂.atoms.length →
      m₂.orientationAt j = m₁.orientationOf (g j) ((m₂.places j).map (Option.map g)))
    (hg : ∀ bond ∈ m₂.bonds, ∀ x y, (m₂.otherNeighbours bond.a bond.b).head? = some x →
      (m₂.otherNeighbours bond.b bond.a).head? = some y →
      m₂.geometryAt bond.a bond.b = m₁.geometryOf (g bond.a) (g bond.b) (g x) (g y)) :
    Mol.RenumberedBy f g m₁ m₂ := by
  refine ⟨h.forth, h.back, h.atoms, h.bonds, ?_, ?_⟩
  · intro atom places ha hplaces
    refine h.orientationOf_eq w₁.graph w₂.graph ha ?_ places hplaces
    have := ho (f atom) (h.forth atom ha).1
    rw [(h.forth atom ha).2] at this
    exact this
  · intro a b x y ha hb hx hy
    refine h.geometryOf_eq w₁ w₂.graph ha hb ?_ hx hy
    intro x' y' hx' hy'
    by_cases hj : ∃ o, m₂.Joined (f a) (f b) o
    · obtain ⟨o, hjo | hjo⟩ := hj
      · have hlt := (w₂.1 _ hjo).1
        simp only at hlt
        have := hg _ hjo x' y' hx' hy'
        simp only [(h.forth a ha).2, (h.forth b hb).2] at this
        rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)]
        exact this
      · have hlt := (w₂.1 _ hjo).1
        simp only at hlt
        have := hg _ hjo y' x' hy' hx'
        simp only [(h.forth a ha).2, (h.forth b hb).2] at this
        rw [Nat.min_eq_right (Nat.le_of_lt hlt), Nat.max_eq_left (Nat.le_of_lt hlt), this]
        exact Mol.geometryOf_comm m₁ a b (g x') (g y')
    · -- the two atoms are not bonded: neither `Mol` stores a mark
      have h₂ : m₂.geometryAt (min (f a) (f b)) (max (f a) (f b)) = none := by
        cases hs : m₂.geometryAt (min (f a) (f b)) (max (f a) (f b)) with
        | none => rfl
        | some s =>
          exfalso
          apply hj
          have hbond := (Mol.canHave_of_geometryAt w₂ hs).2
          rcases Nat.le_total (f a) (f b) with hab | hab
          · rw [Nat.min_eq_left hab, Nat.max_eq_right hab] at hbond
            exact ⟨.double, Or.inl hbond⟩
          · rw [Nat.min_eq_right hab, Nat.max_eq_left hab] at hbond
            exact ⟨.double, Or.inr hbond⟩
      have h₁ : m₁.geometryAt (min a b) (max a b) = none := by
        cases hs : m₁.geometryAt (min a b) (max a b) with
        | none => rfl
        | some s =>
          exfalso
          apply hj
          have hbond := (Mol.canHave_of_geometryAt w₁ hs).2
          rcases Nat.le_total a b with hab | hab
          · rw [Nat.min_eq_left hab, Nat.max_eq_right hab] at hbond
            exact ⟨.double, (h.bonds a b .double ha hb).1 (Or.inl hbond)⟩
          · rw [Nat.min_eq_right hab, Nat.max_eq_left hab] at hbond
            exact ⟨.double, (h.bonds a b .double ha hb).1 (Or.inr hbond)⟩
      rw [h₂]
      unfold Mol.geometryOf
      rw [h₁]

/-- If `m₂` is `m₁` numbered differently, the mark that `m₂` stores for an
atom is what `m₁` says for the fixed order of the places in `m₂`. -/
theorem Mol.RenumberedBy.stored_orientation {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₂ : m₂.GraphWellFormed) {j : Nat}
    (hj : j < m₂.atoms.length) :
    m₂.orientationAt j = m₁.orientationOf (g j) ((m₂.places j).map (Option.map g)) := by
  have hlt : ∀ i, some i ∈ m₂.places j → i < m₂.atoms.length := fun i hi =>
    (Mol.neighbours_lt w₂ (Mol.mem_places.1 hi)).1
  have key := h.orientations (g j) ((m₂.places j).map (Option.map g)) (h.back j hj).1 (by
    intro i hi
    obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hi
    cases p with
    | none => cases hpi
    | some k =>
      simp only [Option.map_some, Option.some.injEq] at hpi
      subst hpi
      exact (h.back k (hlt k hp)).1)
  rw [(h.back j hj).2, map_map_places (fun i hi => (h.back i (hlt i hi)).2),
    Mol.orientationOf_places w₂ j] at key
  exact key

/-- If `m₂` is `m₁` numbered differently, the mark that `m₂` stores for a
double bond is what `m₁` says for the lowest-numbered neighbours in `m₂`. -/
theorem Mol.RenumberedBy.stored_geometry {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₂ : m₂.GraphWellFormed) {bond : Bond}
    (hb : bond ∈ m₂.bonds) {x y : Nat}
    (hx : (m₂.otherNeighbours bond.a bond.b).head? = some x)
    (hy : (m₂.otherNeighbours bond.b bond.a).head? = some y) :
    m₂.geometryAt bond.a bond.b = m₁.geometryOf (g bond.a) (g bond.b) (g x) (g y) := by
  obtain ⟨hab, hblt⟩ := w₂.1 bond hb
  have halt : bond.a < m₂.atoms.length := by omega
  have hxlt := (Mol.neighbours_lt w₂ (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hx)).1).1
  have hylt := (Mol.neighbours_lt w₂ (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hy)).1).1
  have key := h.geometries (g bond.a) (g bond.b) (g x) (g y) (h.back _ halt).1 (h.back _ hblt).1
    (h.back _ hxlt).1 (h.back _ hylt).1
  rw [(h.back _ halt).2, (h.back _ hblt).2, (h.back _ hxlt).2, (h.back _ hylt).2,
    Mol.geometryOf_heads hab hx hy] at key
  exact key

/-- A double bond that can have a geometry has a lowest-numbered other
neighbour at each of its two atoms. -/
theorem Mol.heads_of_canHave {m : Mol} {a b : Nat} (h : m.canHaveGeometry a b = true) :
    (∃ x, (m.otherNeighbours a b).head? = some x) ∧
      ∃ y, (m.otherNeighbours b a).head? = some y := by
  unfold Mol.canHaveGeometry at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  constructor
  · cases hl : m.otherNeighbours a b with
    | nil => rw [hl] at h1; simp at h1
    | cons z _ => exact ⟨z, rfl⟩
  · cases hl : m.otherNeighbours b a with
    | nil => rw [hl] at h2; simp at h2
    | cons z _ => exact ⟨z, rfl⟩

/-- A `Mol` without orientations says nothing about the orientation of an
atom. -/
theorem Mol.orientationOf_of_nil {m : Mol} (h : m.orientations = []) (atom : Nat)
    (places : List Place) : m.orientationOf atom places = none := by
  unfold Mol.orientationOf Mol.orientationAt
  rw [h]
  rfl

/-- A `Mol` without geometries says nothing about the geometry of a double
bond. -/
theorem Mol.geometryOf_of_nil {m : Mol} (h : m.geometries = []) (a b x y : Nat) :
    m.geometryOf a b x y = none := by
  unfold Mol.geometryOf Mol.geometryAt
  rw [h]
  rfl

/-! ## What carries over with the atoms and the bonds -/

/-- Where the first statement gives an answer, the atom has a stored mark. -/
theorem Mol.orientationAt_of_orientationOf {m : Mol} {atom : Nat} {places : List Place}
    {o : Orientation} (h : m.orientationOf atom places = some o) :
    ∃ s, m.orientationAt atom = some s := by
  unfold Mol.orientationOf at h
  cases hs : m.orientationAt atom with
  | none => rw [hs] at h; cases h
  | some s => exact ⟨s, rfl⟩

/-- Where the second statement gives an answer, the double bond has a stored
mark. -/
theorem Mol.geometryAt_of_geometryOf {m : Mol} {a b x y : Nat} {s : Geometry}
    (h : m.geometryOf a b x y = some s) : ∃ t, m.geometryAt (min a b) (max a b) = some t := by
  unfold Mol.geometryOf at h
  cases hs : m.geometryAt (min a b) (max a b) with
  | none => rw [hs] at h; cases h
  | some t => exact ⟨t, rfl⟩

/-- An atom has four places exactly when it has them at its new number. -/
theorem Mol.SameGraphBy.hasFourPlaces {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {atom : Nat} (ha : atom < m₁.atoms.length) :
    m₂.hasFourPlaces (f atom) = m₁.hasFourPlaces atom := by
  unfold Mol.hasFourPlaces
  rw [h.atoms atom ha, (h.neighbours_perm w₁ w₂ ha).length_eq, List.length_map]

/-- A double bond that can have a geometry can have one at its new numbers. -/
theorem Mol.SameGraphBy.canHaveGeometry {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {a b : Nat} (ha : a < m₁.atoms.length) (hb : b < m₁.atoms.length) (hab : f a < f b)
    (hcan : m₁.canHaveGeometry (min a b) (max a b) = true) :
    m₂.canHaveGeometry (f a) (f b) = true := by
  have hlen1 := h.otherNeighbours_length w₁ w₂ ha hb
  have hlen2 := h.otherNeighbours_length w₁ w₂ hb ha
  unfold Mol.canHaveGeometry at hcan ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcan ⊢
  obtain ⟨⟨hbond, hla⟩, hlb⟩ := hcan
  have hbond' : (⟨min a b, max a b, .double⟩ : Bond) ∈ m₁.bonds := by simpa using hbond
  have hmem : ∀ (hj : m₁.Joined a b .double), (⟨f a, f b, .double⟩ : Bond) ∈ m₂.bonds := by
    intro hj
    rcases (h.bonds a b .double ha hb).1 hj with h' | h'
    · exact h'
    · have := (w₂.1 _ h').1
      simp only at this
      omega
  rcases Nat.le_total a b with hle | hle
  · rw [Nat.min_eq_left hle, Nat.max_eq_right hle] at hbond' hla hlb
    refine ⟨⟨by simpa using hmem (Or.inl hbond'), ?_⟩, ?_⟩
    · rw [hlen1]; exact hla
    · rw [hlen2]; exact hlb
  · rw [Nat.min_eq_right hle, Nat.max_eq_left hle] at hbond' hla hlb
    refine ⟨⟨by simpa using hmem (Or.inr hbond'), ?_⟩, ?_⟩
    · rw [hlen1]; exact hlb
    · rw [hlen2]; exact hla

theorem Mol.hasStereo_iff {m : Mol} :
    m.hasStereo = true ↔ m.orientations ≠ [] ∨ m.geometries ≠ [] := by
  simp [Mol.hasStereo]

/-- An atom with an orientation has one at its new number. -/
theorem Mol.RenumberedBy.orientationAt_some {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) {atom : Nat} {o : Orientation}
    (hat : m₁.orientationAt atom = some o) : ∃ s, m₂.orientationAt (f atom) = some s := by
  have hlt := (Mol.fourPlaces_of_orientationAt w₁ hat).2
  have key := h.orientations atom (m₁.places atom) hlt (fun i hi =>
    (Mol.neighbours_lt w₁.graph (Mol.mem_places.1 hi)).1)
  rw [Mol.orientationOf_places w₁.graph, hat] at key
  exact Mol.orientationAt_of_orientationOf key

/-- A double bond with a geometry has one at its new numbers. -/
theorem Mol.RenumberedBy.geometryAt_some {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) {a b : Nat} {s : Geometry}
    (hat : m₁.geometryAt a b = some s) :
    ∃ t, m₂.geometryAt (min (f a) (f b)) (max (f a) (f b)) = some t := by
  obtain ⟨hcan, hbond⟩ := Mol.canHave_of_geometryAt w₁ hat
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := Mol.heads_of_canHave hcan
  obtain ⟨hab, hblt⟩ := w₁.1 _ hbond
  simp only at hab hblt
  have hplt := (Mol.neighbours_lt w₁.graph
    (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hp)).1).1
  have hqlt := (Mol.neighbours_lt w₁.graph
    (Mol.mem_otherNeighbours.1 (List.mem_of_mem_head? hq)).1).1
  have key := h.geometries a b p q (by omega) hblt hplt hqlt
  rw [Mol.geometryOf_heads hab hp hq, hat] at key
  exact Mol.geometryAt_of_geometryOf key

/-- A `Mol` with a stereo fact still has one when its atoms are numbered
differently. -/
theorem Mol.RenumberedBy.hasStereo_of {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.RenumberedBy f g m₁ m₂) (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (hs : m₁.hasStereo = true) : m₂.hasStereo = true := by
  rw [Mol.hasStereo_iff] at hs ⊢
  rcases hs with hs | hs
  · left
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hs
    obtain ⟨atom, o⟩ := x
    obtain ⟨s, hs₂⟩ := h.orientationAt_some w₁ ((Mol.orientationAt_eq_some w₁).2 hx)
    exact List.ne_nil_of_mem ((Mol.orientationAt_eq_some w₂).1 hs₂)
  · right
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hs
    obtain ⟨a, b, s⟩ := x
    obtain ⟨t, ht⟩ := h.geometryAt_some w₁ ((Mol.geometryAt_eq_some w₁).2 hx)
    exact List.ne_nil_of_mem ((Mol.geometryAt_eq_some w₂).1 ht)

/-! ## Where no mark is stored -/

/-- An atom with an orientation is an atom of the `Mol`. -/
theorem Mol.orientation_lt {m : Mol} (w : m.WellFormed) {x : AtomOrientation}
    (hx : x ∈ m.orientations) : x.atom < m.atoms.length := by
  obtain ⟨atom, o⟩ := x
  exact (Mol.fourPlaces_of_orientationAt w ((Mol.orientationAt_eq_some w).2 hx)).2

/-- No mark is stored for a number that is no atom of the `Mol`. -/
theorem Mol.orientationAt_of_ge {m : Mol} (w : m.WellFormed) {atom : Nat}
    (h : m.atoms.length ≤ atom) : m.orientationAt atom = none := by
  cases hs : m.orientationAt atom with
  | none => rfl
  | some o => exact absurd (Mol.fourPlaces_of_orientationAt w hs).2 (by omega)

/-- A `Mol` without atoms has no stereo facts. -/
theorem Mol.noStereo_of_noAtoms {m : Mol} (w : m.WellFormed) (h : m.atoms.length = 0) :
    m.orientations = [] ∧ m.geometries = [] := by
  constructor
  · apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    have := Mol.orientation_lt w hx
    omega
  · apply List.eq_nil_iff_forall_not_mem.2
    rintro ⟨a, b, s⟩ hx
    have hbond := (Mol.canHave_of_geometryAt w ((Mol.geometryAt_eq_some w).2 hx)).2
    have := (w.1 _ hbond).2
    simp only at this
    omega

theorem Mol.noStereo_of_not_hasStereo {m : Mol} (h : m.hasStereo = false) :
    m.orientations = [] ∧ m.geometries = [] := by
  simpa [Mol.hasStereo] using h

end VeriMol
