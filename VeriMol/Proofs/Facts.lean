import VeriMol.Proofs.Follow
import VeriMol.Proofs.Stereo

/-!
# From the notes of the reader to the stereo facts

The reader notes the stereo marks of a text and where they stand, and
`stereoFacts` (`VeriMol/Core/ReadMarks.lean`) works out what they say. This
file shows: if the notes are those of a text that a spelling writes for a well
formed `Mol` (`VeriMol/Core/Write.lean`), then `stereoFacts` gives exactly the
stereo facts of that `Mol`, and no problem (`stereoFacts_back`).

"The notes of such a text" is said without the reader
(`VeriMol/Core/Read.lean`):

* which bonds were written with a ring number, and at which place among the
  ring numbers of their two atoms (`ringEntry`);
* that the bonds with a direction mark are those that the writer chose, each
  with the mark that it chose (`chooseMarks`);
* that the atoms with `@` or `@@` are the atoms with an orientation, each
  with the mark that the writer wrote for it.

`VeriMol/Proofs/RoundTrip.lean` shows that the reader notes exactly this for
the two spellings, and so proves theorems 11 and 12 of CLAIMS.md.
-/

namespace VeriMol

/-! ## The marks that the writer chose -/

/-- A link holds: both of its bonds have a mark, and the two marks are the
same exactly when the link asks for that. -/
def LinkHolds (marks : List ((Nat × Nat) × Bool)) (link : Link) : Prop :=
  ∃ x y, markAmong marks link.first = some x ∧ markAmong marks link.second = some y ∧
    (x == y) = link.same

/-- `sameKey` says yes exactly for two equal pairs of atoms. -/
theorem sameKey_iff (x y : Nat × Nat) : sameKey x y = true ↔ x = y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp [sameKey]

/-- A bond that has a mark among `marks` is an entry of `marks`. -/
theorem mem_of_markAmong {marks : List ((Nat × Nat) × Bool)} {key : Nat × Nat} {up : Bool}
    (h : markAmong marks key = some up) : (key, up) ∈ marks := by
  unfold markAmong at h
  obtain ⟨found, hfound, hup⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hfound
  have hp := List.find?_some hfound
  have hkey : found.1 = key := (sameKey_iff _ _).1 hp
  obtain ⟨k, u⟩ := found
  simp only at hup hkey
  subst hup hkey
  exact hmem

/-- One pass over the links adds marks only for bonds of the links. -/
theorem spreadOnce_keys (S : Nat × Nat → Prop) (links : List Link)
    (hlinks : ∀ link ∈ links, S link.first ∧ S link.second) :
    ∀ marks : List ((Nat × Nat) × Bool), (∀ x ∈ marks, S x.1) →
      ∀ x ∈ spreadOnce links marks, S x.1 := by
  unfold spreadOnce
  induction links with
  | nil =>
    intro marks h
    exact h
  | cons link rest ih =>
    intro marks h
    simp only [List.foldl_cons]
    apply ih (fun l hl => hlinks l (List.mem_cons_of_mem _ hl))
    intro x hx
    split at hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact h x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact (hlinks link List.mem_cons_self).2
    · rcases List.mem_append.1 hx with hx | hx
      · exact h x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact (hlinks link List.mem_cons_self).1
    · exact h x hx

/-- The same for any number of passes. -/
theorem spreadTimes_keys (S : Nat × Nat → Prop) (links : List Link)
    (hlinks : ∀ link ∈ links, S link.first ∧ S link.second) :
    ∀ (passes : Nat) (marks : List ((Nat × Nat) × Bool)), (∀ x ∈ marks, S x.1) →
      ∀ x ∈ spreadTimes links passes marks, S x.1 := by
  intro passes
  induction passes with
  | zero =>
    intro marks h
    exact h
  | succ passes ih =>
    intro marks h
    simp only [spreadTimes]
    exact ih _ (spreadOnce_keys S links hlinks marks h)

/-- Every mark that is chosen stands at a bond of the list of bonds to be
marked, or at a bond of a link. -/
theorem markGroups_keys (S : Nat × Nat → Prop) (links : List Link) (passes : Nat)
    (hlinks : ∀ link ∈ links, S link.first ∧ S link.second) :
    ∀ (keys : List (Nat × Nat)) (marks : List ((Nat × Nat) × Bool)), (∀ k ∈ keys, S k) →
      (∀ x ∈ marks, S x.1) → ∀ x ∈ markGroups links passes keys marks, S x.1 := by
  intro keys
  induction keys with
  | nil =>
    intro marks _ h
    exact h
  | cons key rest ih =>
    intro marks hkeys h
    simp only [markGroups]
    split
    · exact ih marks (fun k hk => hkeys k (List.mem_cons_of_mem _ hk)) h
    · apply ih _ (fun k hk => hkeys k (List.mem_cons_of_mem _ hk))
      apply spreadTimes_keys S links hlinks
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact hkeys key List.mem_cons_self

/-- `chooseMarks`, taken apart: the links of the double bonds with a geometry,
the bonds that are to be marked, all links, and what the function checked
before it gave the marks. -/
theorem chooseMarks_ok {mol : Mol} {marks : List ((Nat × Nat) × Bool)}
    (h : chooseMarks mol = .ok marks) :
    ∃ (first : List Link) (marked : List (Nat × Nat)) (links : List Link),
      first = (mol.geometries.map (geometryLink mol)).filterMap id ∧
      (mol.geometries.map (geometryLink mol)).any Option.isNone = false ∧
      marked = (mol.bonds.filterMap fun bond =>
        if first.any (fun link =>
            sameKey link.first (bond.a, bond.b) || sameKey link.second (bond.a, bond.b))
        then some (bond.a, bond.b) else none) ∧
      links = first ++ (mol.geometries.flatMap fun geometry =>
        [sideLink mol marked geometry.a geometry.b,
          sideLink mol marked geometry.b geometry.a].filterMap id) ∧
      (mol.bonds.any fun bond =>
        (mol.geometryAt bond.a bond.b).isNone && wouldGetGeometry mol marked bond) = false ∧
      marks = markGroups links marked.length marked [] ∧
      ∀ link ∈ links, LinkHolds marks link := by
  unfold chooseMarks at h
  simp only at h
  split at h
  · cases h
  · rename_i hfound
    split at h
    · cases h
    · rename_i hwould
      split at h
      · rename_i hall
        cases h
        refine ⟨_, _, _, rfl, by simpa using hfound, rfl, rfl, by simpa using hwould, rfl, ?_⟩
        intro link hlink
        have hl := List.all_eq_true.1 hall link hlink
        split at hl
        · rename_i x y hx hy
          exact ⟨x, y, hx, hy, by simpa using hl⟩
        · cases hl
      · cases h

/-- `reference`, taken apart: the neighbour whose bond gets the mark, and what
the function gives for it. -/
theorem reference_eq_some {mol : Mol} {e partner : Nat} {found : (Nat × Nat) × Bool}
    (h : reference mol e partner = some found) :
    ∃ x, (mol.otherNeighbours e partner).find? (fun x => canCarryMark mol e x) = some x ∧
      found = (bondKey e x,
        decide (e < x) == ((mol.otherNeighbours e partner).head? == some x)) := by
  unfold reference at h
  split at h
  · cases h
  · rename_i x hx
    cases h
    exact ⟨x, hx, rfl⟩

/-- `geometryLink`, taken apart: what `reference` gives at the two atoms of
the double bond, and the link that is made of it. -/
theorem geometryLink_eq_some {mol : Mol} {g : BondGeometry} {link : Link}
    (h : geometryLink mol g = some link) :
    ∃ atA atB, reference mol g.a g.b = some atA ∧ reference mol g.b g.a = some atB ∧
      link = ⟨atA.1, atB.1, (atA.2 == atB.2) == (g.geometry == .sameSide)⟩ := by
  unfold geometryLink at h
  split at h
  · rename_i atA atB hA hB
    cases h
    exact ⟨atA, atB, hA, hB, rfl⟩
  · cases h

/-- Whether a bond can carry a mark depends on its two atoms only, not on
which of them is named first. -/
theorem canCarryMark_congr (mol : Mol) {e x e' x' : Nat} (h : bondKey e x = bondKey e' x') :
    canCarryMark mol e x = canCarryMark mol e' x' := by
  unfold canCarryMark
  simp only [h]

/-- One of the two atoms of a bond key is the first atom it was made from. -/
theorem bondKey_has (e x : Nat) : (bondKey e x).1 = e ∨ (bondKey e x).2 = e := by
  unfold bondKey
  rcases Nat.le_total e x with h | h
  · exact Or.inl (Nat.min_eq_left h)
  · exact Or.inr (Nat.max_eq_left h)

/-- A neighbour of an atom is joined to it by a bond of the `Mol`, whose two
atoms are the bond key. -/
theorem bond_of_neighbour {mol : Mol} (w : mol.GraphWellFormed) {e x : Nat}
    (h : x ∈ mol.neighbours e) : ∃ bond ∈ mol.bonds, (bond.a, bond.b) = bondKey e x := by
  obtain ⟨order, hj | hj⟩ := Mol.mem_neighbours.1 h
  · have hlt := (w.1 _ hj).1
    simp only at hlt
    refine ⟨_, hj, ?_⟩
    unfold bondKey
    rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)]
  · have hlt := (w.1 _ hj).1
    simp only at hlt
    refine ⟨_, hj, ?_⟩
    unfold bondKey
    rw [Nat.min_eq_right (Nat.le_of_lt hlt), Nat.max_eq_left (Nat.le_of_lt hlt)]

/-- What is known of the marks that `chooseMarks` gives. -/
structure MarksChosen (mol : Mol) (marks : List ((Nat × Nat) × Bool)) : Prop where
  /-- every double bond with a geometry has its link, and the link holds -/
  links : ∀ g ∈ mol.geometries, ∃ link, geometryLink mol g = some link ∧ LinkHolds marks link
  /-- two marked bonds at one atom of a double bond with a geometry point to
  opposite sides -/
  sides : ∀ g ∈ mol.geometries, ∀ e partner,
    ((e = g.a ∧ partner = g.b) ∨ (e = g.b ∧ partner = g.a)) →
    ∀ x y mx my, mol.otherNeighbours e partner = [x, y] →
      markAmong marks (bondKey e x) = some mx → markAmong marks (bondKey e y) = some my →
      (mx == my) = (decide (e < x) != decide (e < y))
  /-- a bond with a mark can carry one -/
  canCarry : ∀ e x up, markAmong marks (bondKey e x) = some up → canCarryMark mol e x = true
  /-- a bond with a mark stands at an atom of a double bond with a geometry -/
  touches : ∀ key up, markAmong marks key = some up →
    ∃ g ∈ mol.geometries, key.1 = g.a ∨ key.2 = g.a ∨ key.1 = g.b ∨ key.2 = g.b
  /-- a double bond that can have a geometry and has none gets none from the
  marks: at one of its two atoms no bond to another neighbour is marked -/
  noGeometry : ∀ bond ∈ mol.bonds, mol.geometryAt bond.a bond.b = none →
    (∀ x ∈ mol.otherNeighbours bond.a bond.b, markAmong marks (bondKey bond.a x) = none) ∨
    (∀ x ∈ mol.otherNeighbours bond.b bond.a, markAmong marks (bondKey bond.b x) = none) ∨
    bond.order ≠ .double ∨ mol.canHaveGeometry bond.a bond.b = false

/-- The marks that `chooseMarks` gives for a well formed `Mol`. -/
theorem marksChosen {mol : Mol} (w : mol.WellFormed) {marks : List ((Nat × Nat) × Bool)}
    (h : chooseMarks mol = .ok marks) : MarksChosen mol marks := by
  obtain ⟨first, marked, links, hfirst, hsome, hmarked, hlinks, hwould, hmarks, hhold⟩ :=
    chooseMarks_ok h
  -- the links of the double bonds with a geometry
  have hmemFirst : ∀ link, link ∈ first ↔ ∃ g ∈ mol.geometries, geometryLink mol g = some link := by
    intro link
    rw [hfirst]
    simp [List.mem_filterMap]
  have hlinkOf : ∀ g ∈ mol.geometries, ∃ link, geometryLink mol g = some link := by
    intro g hg
    cases hl : geometryLink mol g with
    | some link => exact ⟨link, rfl⟩
    | none =>
      exfalso
      have : (mol.geometries.map (geometryLink mol)).any Option.isNone = true := by
        rw [List.any_eq_true]
        exact ⟨none, List.mem_map.2 ⟨g, hg, hl⟩, rfl⟩
      rw [hsome] at this
      cases this
  -- a bond key of a first link is the key of a bond that can carry a mark, at
  -- an atom of its double bond
  have hend : ∀ link ∈ first, ∀ key, (key = link.first ∨ key = link.second) →
      ∃ g ∈ mol.geometries, ∃ e x, (e = g.a ∨ e = g.b) ∧ x ∈ mol.neighbours e ∧
        canCarryMark mol e x = true ∧ key = bondKey e x := by
    intro link hlink key hkey
    obtain ⟨g, hg, hgl⟩ := (hmemFirst link).1 hlink
    obtain ⟨atA, atB, hA, hB, rfl⟩ := geometryLink_eq_some hgl
    obtain ⟨xa, hxa, rfl⟩ := reference_eq_some hA
    obtain ⟨xb, hxb, rfl⟩ := reference_eq_some hB
    rcases hkey with rfl | rfl
    · exact ⟨g, hg, g.a, xa, Or.inl rfl,
        (Mol.mem_otherNeighbours.1 (List.mem_of_find?_eq_some hxa)).1, List.find?_some hxa, rfl⟩
    · exact ⟨g, hg, g.b, xb, Or.inr rfl,
        (Mol.mem_otherNeighbours.1 (List.mem_of_find?_eq_some hxb)).1, List.find?_some hxb, rfl⟩
  -- the bonds that are to be marked
  have hmemMarked : ∀ key, key ∈ marked ↔ ∃ bond ∈ mol.bonds, key = (bond.a, bond.b) ∧
      ∃ link ∈ first, link.first = key ∨ link.second = key := by
    intro key
    rw [hmarked, List.mem_filterMap]
    constructor
    · rintro ⟨bond, hbond, hif⟩
      split at hif
      · rename_i hany
        cases hif
        obtain ⟨link, hlink, hor⟩ := List.any_eq_true.1 hany
        rw [Bool.or_eq_true, sameKey_iff, sameKey_iff] at hor
        exact ⟨bond, hbond, rfl, link, hlink, hor⟩
      · cases hif
    · rintro ⟨bond, hbond, rfl, link, hlink, hor⟩
      refine ⟨bond, hbond, ?_⟩
      have hany : (first.any fun link =>
          sameKey link.first (bond.a, bond.b) || sameKey link.second (bond.a, bond.b)) = true := by
        rw [List.any_eq_true]
        refine ⟨link, hlink, ?_⟩
        rw [Bool.or_eq_true, sameKey_iff, sameKey_iff]
        exact hor
      simp only [hany, ↓reduceIte]
  have hendMarked : ∀ link ∈ first, link.first ∈ marked ∧ link.second ∈ marked := by
    intro link hlink
    constructor
    · obtain ⟨g, _, e, x, _, hx, _, hk⟩ := hend link hlink link.first (Or.inl rfl)
      obtain ⟨bond, hbond, hb⟩ := bond_of_neighbour w.graph hx
      exact (hmemMarked _).2 ⟨bond, hbond, by rw [hk, hb], link, hlink, Or.inl rfl⟩
    · obtain ⟨g, _, e, x, _, hx, _, hk⟩ := hend link hlink link.second (Or.inr rfl)
      obtain ⟨bond, hbond, hb⟩ := bond_of_neighbour w.graph hx
      exact (hmemMarked _).2 ⟨bond, hbond, by rw [hk, hb], link, hlink, Or.inr rfl⟩
  -- every link joins two bonds that are to be marked
  have hsideOf : ∀ {e partner : Nat} {link : Link}, sideLink mol marked e partner = some link →
      ∃ x y, mol.otherNeighbours e partner = [x, y] ∧ bondKey e x ∈ marked ∧
        bondKey e y ∈ marked ∧
        link = ⟨bondKey e x, bondKey e y, decide (e < x) != decide (e < y)⟩ := by
    intro e partner link hs
    unfold sideLink at hs
    split at hs
    · rename_i x y hxy
      split at hs
      · rename_i hboth
        cases hs
        rw [Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at hboth
        obtain ⟨⟨k1, hk1, hs1⟩, ⟨k2, hk2, hs2⟩⟩ := hboth
        rw [sameKey_iff] at hs1 hs2
        exact ⟨x, y, hxy, hs1 ▸ hk1, hs2 ▸ hk2, rfl⟩
      · cases hs
    · cases hs
  have hlinkMarked : ∀ link ∈ links, link.first ∈ marked ∧ link.second ∈ marked := by
    intro link hlink
    rw [hlinks] at hlink
    rcases List.mem_append.1 hlink with hl | hl
    · exact hendMarked link hl
    · obtain ⟨g, _, hgl⟩ := List.mem_flatMap.1 hl
      obtain ⟨found, hfound, hid⟩ := List.mem_filterMap.1 hgl
      simp only [id] at hid
      subst hid
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfound
      rcases hfound with hside | hside
      · obtain ⟨x, y, _, h1, h2, rfl⟩ := hsideOf hside.symm
        exact ⟨h1, h2⟩
      · obtain ⟨x, y, _, h1, h2, rfl⟩ := hsideOf hside.symm
        exact ⟨h1, h2⟩
  -- so every mark stands at a bond that is to be marked
  have hkeys : ∀ key up, markAmong marks key = some up → key ∈ marked := by
    intro key up hup
    have hmem := mem_of_markAmong hup
    rw [hmarks] at hmem
    exact markGroups_keys (fun k => k ∈ marked) links marked.length hlinkMarked marked []
      (fun k hk => hk) (fun x hx => by cases hx) (key, up) hmem
  have hkeyOf : ∀ key up, markAmong marks key = some up →
      ∃ g ∈ mol.geometries, ∃ e x, (e = g.a ∨ e = g.b) ∧ x ∈ mol.neighbours e ∧
        canCarryMark mol e x = true ∧ key = bondKey e x := by
    intro key up hup
    obtain ⟨bond, _, _, link, hlink, hor⟩ := (hmemMarked key).1 (hkeys key up hup)
    exact hend link hlink key (by rcases hor with h | h <;> simp [h])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨link, hl⟩ := hlinkOf g hg
    refine ⟨link, hl, hhold link ?_⟩
    rw [hlinks]
    exact List.mem_append_left _ ((hmemFirst link).2 ⟨g, hg, hl⟩)
  · intro g hg e partner hep x y mx my hxy hmx hmy
    -- the link between the two marked bonds is one of the links
    have hside : sideLink mol marked e partner
        = some ⟨bondKey e x, bondKey e y, decide (e < x) != decide (e < y)⟩ := by
      unfold sideLink
      rw [hxy]
      have h1 : marked.any (sameKey (bondKey e x)) = true := by
        rw [List.any_eq_true]
        exact ⟨_, hkeys _ mx hmx, (sameKey_iff _ _).2 rfl⟩
      have h2 : marked.any (sameKey (bondKey e y)) = true := by
        rw [List.any_eq_true]
        exact ⟨_, hkeys _ my hmy, (sameKey_iff _ _).2 rfl⟩
      simp only [h1, h2, Bool.and_self, ↓reduceIte]
    have hin : (⟨bondKey e x, bondKey e y, decide (e < x) != decide (e < y)⟩ : Link) ∈ links := by
      rw [hlinks]
      apply List.mem_append_right
      rw [List.mem_flatMap]
      refine ⟨g, hg, ?_⟩
      rw [List.mem_filterMap]
      rcases hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, by rw [hside]; exact List.mem_cons_self, rfl⟩
      · exact ⟨_, by rw [hside]; exact List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    obtain ⟨x', y', hx', hy', hsame⟩ := hhold _ hin
    simp only at hx' hy' hsame
    rw [hmx] at hx'
    rw [hmy] at hy'
    cases hx'
    cases hy'
    exact hsame
  · intro e x up hup
    obtain ⟨g, _, e', x', _, _, hcan, hk⟩ := hkeyOf _ up hup
    rw [canCarryMark_congr mol hk]
    exact hcan
  · intro key up hup
    obtain ⟨g, hg, e, x, he, _, _, rfl⟩ := hkeyOf key up hup
    refine ⟨g, hg, ?_⟩
    rcases he with rfl | rfl
    · rcases bondKey_has g.a x with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases bondKey_has g.b x with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · intro bond hbond hnone
    have hw := List.any_eq_false.1 hwould bond hbond
    rw [hnone] at hw
    simp only [Option.isNone_none, Bool.true_and] at hw
    unfold wouldGetGeometry at hw
    -- a bond that is not to be marked has no mark
    have hnoMark : ∀ e x, marked.any (sameKey (bondKey e x)) = false →
        markAmong marks (bondKey e x) = none := by
      intro e x hany
      cases hm : markAmong marks (bondKey e x) with
      | none => rfl
      | some up =>
        exfalso
        have : marked.any (sameKey (bondKey e x)) = true := by
          rw [List.any_eq_true]
          exact ⟨_, hkeys _ up hm, (sameKey_iff _ _).2 rfl⟩
        rw [hany] at this
        cases this
    by_cases hd : bond.order = .double
    · by_cases hc : mol.canHaveGeometry bond.a bond.b = true
      · by_cases h1 : ((mol.otherNeighbours bond.a bond.b).any fun x =>
            marked.any (sameKey (bondKey bond.a x))) = true
        · right; left
          have h2 : ((mol.otherNeighbours bond.b bond.a).any fun x =>
              marked.any (sameKey (bondKey bond.b x))) = false := by
            simpa [hd, hc, h1] using hw
          intro x hx
          exact hnoMark _ _ (List.any_eq_false.1 h2 x hx |> fun h => by simpa using h)
        · left
          intro x hx
          have h1' : ((mol.otherNeighbours bond.a bond.b).any fun x =>
              marked.any (sameKey (bondKey bond.a x))) = false := by simpa using h1
          exact hnoMark _ _ (List.any_eq_false.1 h1' x hx |> fun h => by simpa using h)
      · right; right; right
        simpa using hc
    · right; right; left
      exact hd

/-! ## The direction marks that the reader noted -/

/-- The reader noted a direction for exactly the bonds that carry a mark, each
with what its mark says. -/
structure DirectionsNoted (mol : Mol) (marks : List ((Nat × Nat) × Bool))
    (directions : List Direction) : Prop where
  /-- every direction that was noted stands at a bond of the `Mol` with a mark,
  and says what that mark says -/
  marked : ∀ d ∈ directions, ∃ e ∈ mol.bonds, d.a = e.a ∧ d.b = e.b ∧
    markAmong marks (e.a, e.b) = some d.above
  /-- every bond with a mark has a direction that was noted -/
  noted : ∀ e ∈ mol.bonds, ∀ up, markAmong marks (e.a, e.b) = some up →
    ∃ d ∈ directions, d.a = e.a ∧ d.b = e.b ∧ d.above = up

/-- Whether the text says that the neighbour `x` lies above `e`: as the mark of
their bond says it. -/
theorem aboveOf_side {mol : Mol} {marks : List ((Nat × Nat) × Bool)} {directions : List Direction}
    (w : mol.GraphWellFormed) (hd : DirectionsNoted mol marks directions) {e x : Nat}
    (hx : x ∈ mol.neighbours e) :
    (aboveOf directions x e).map (·.1)
      = (markAmong marks (bondKey e x)).map fun up => if e < x then up else !up := by
  obtain ⟨bond, hbond, hkey⟩ := bond_of_neighbour w hx
  unfold aboveOf directionOf
  have hk : (min x e, max x e) = bondKey e x := by
    unfold bondKey
    rw [Nat.min_comm, Nat.max_comm]
  have hk1 : min x e = (bondKey e x).1 := congrArg Prod.fst hk
  have hk2 : max x e = (bondKey e x).2 := congrArg Prod.snd hk
  rw [hk1, hk2]
  have hb1 : bond.a = (bondKey e x).1 := congrArg Prod.fst hkey
  have hb2 : bond.b = (bondKey e x).2 := congrArg Prod.snd hkey
  cases hf : directions.find? (fun direction =>
      direction.a == (bondKey e x).1 && direction.b == (bondKey e x).2) with
  | some d =>
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨e', _, ha, hb, hmark⟩ := hd.marked d hmem
    have hm : markAmong marks (bondKey e x) = some d.above := by
      have : (e'.a, e'.b) = bondKey e x := by
        rw [← ha, ← hb, hp.1, hp.2]
      rw [← this]
      exact hmark
    rw [hm]
    rfl
  | none =>
    cases hm : markAmong marks (bondKey e x) with
    | none => rfl
    | some up =>
      exfalso
      rw [← hkey] at hm
      obtain ⟨d, hdmem, ha, hb, _⟩ := hd.noted bond hbond up hm
      have := List.find?_eq_none.1 hf d hdmem
      simp [ha, hb, hb1, hb2] at this

/-- A neighbour whose bond has no mark is not among the marked ones. -/
theorem aboveOf_none {mol : Mol} {marks : List ((Nat × Nat) × Bool)} {directions : List Direction}
    (w : mol.GraphWellFormed) (hd : DirectionsNoted mol marks directions) {e x : Nat}
    (hx : x ∈ mol.neighbours e) (hm : markAmong marks (bondKey e x) = none) :
    aboveOf directions x e = none := by
  have := aboveOf_side w hd hx
  rw [hm] at this
  cases h : aboveOf directions x e with
  | none => rfl
  | some found => rw [h] at this; cases this

/-- A neighbour whose bond has a mark is among the marked ones, with the side
that the mark says. -/
theorem aboveOf_some {mol : Mol} {marks : List ((Nat × Nat) × Bool)} {directions : List Direction}
    (w : mol.GraphWellFormed) (hd : DirectionsNoted mol marks directions) {e x : Nat} {up : Bool}
    (hx : x ∈ mol.neighbours e) (hm : markAmong marks (bondKey e x) = some up) :
    ∃ position, aboveOf directions x e = some (if e < x then up else !up, position) := by
  have := aboveOf_side w hd hx
  rw [hm] at this
  cases h : aboveOf directions x e with
  | none => rw [h] at this; cases this
  | some found =>
    rw [h] at this
    obtain ⟨side, position⟩ := found
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨position, by rw [this]⟩

/-- One atom of a double bond with a geometry. The bond that the writer chose
for its mark carries the mark `m`. Then the reader finds a marked neighbour
there, finds no contradiction, and takes the lowest-numbered neighbour to lie
on the side that the writer meant. -/
theorem side_read {mol : Mol} {marks : List ((Nat × Nat) × Bool)} {directions : List Direction}
    (w : mol.WellFormed) (hc : MarksChosen mol marks) (hd : DirectionsNoted mol marks directions)
    {g : BondGeometry} (hg : g ∈ mol.geometries) {e partner : Nat}
    (hep : (e = g.a ∧ partner = g.b) ∨ (e = g.b ∧ partner = g.a))
    {found : (Nat × Nat) × Bool} {m : Bool} (href : reference mol e partner = some found)
    (hm : markAmong marks found.1 = some m)
    (hlen : (mol.otherNeighbours e partner).length = 1 ∨
      (mol.otherNeighbours e partner).length = 2) :
    (markedOthers mol directions e partner).isEmpty = false ∧
      contradiction (markedOthers mol directions e partner) = none ∧
      lowestAbove (mol.otherNeighbours e partner) (markedOthers mol directions e partner)
        = (m == found.2) := by
  obtain ⟨xr, hfind, rfl⟩ := reference_eq_some href
  simp only at hm
  have hnb : ∀ z ∈ mol.otherNeighbours e partner, z ∈ mol.neighbours e :=
    fun z hz => (Mol.mem_otherNeighbours.1 hz).1
  have hnd := Mol.otherNeighbours_nodup w.graph e partner
  unfold markedOthers
  match hothers : mol.otherNeighbours e partner, hlen with
  | [x], _ =>
    rw [hothers] at hfind hnb
    have hxr : xr = x := by
      simp only [List.find?_cons, List.find?_nil] at hfind
      split at hfind
      · exact (Option.some.inj hfind).symm
      · cases hfind
    subst hxr
    obtain ⟨px, hax⟩ := aboveOf_some w.graph hd (hnb xr List.mem_cons_self) hm
    simp only [List.filterMap_cons, List.filterMap_nil, hax, Option.map_some, List.isEmpty_cons,
      contradiction, lowestAbove, List.head?_cons, beq_self_eq_true, ↓reduceIte, true_and]
    by_cases hlt : e < xr <;> cases m <;> simp [hlt]
  | [x, y], _ =>
    rw [hothers] at hfind hnb hnd
    have hxy : x ≠ y := by
      intro e'
      rw [e'] at hnd
      simp at hnd
    have hxy' : (some x == some y) = false := by simpa using hxy
    simp only [List.find?_cons, List.find?_nil] at hfind
    by_cases hpx : canCarryMark mol e x = true
    · -- the writer chose the bond to the lower neighbour
      simp only [hpx] at hfind
      have hxr : xr = x := (Option.some.inj hfind).symm
      subst hxr
      obtain ⟨px, hax⟩ := aboveOf_some w.graph hd (hnb xr List.mem_cons_self) hm
      cases hmy : markAmong marks (bondKey e y) with
      | none =>
        have hay := aboveOf_none w.graph hd (hnb y (List.mem_cons_of_mem _ List.mem_cons_self)) hmy
        simp only [List.filterMap_cons, List.filterMap_nil, hax, hay, Option.map_some,
          Option.map_none, List.isEmpty_cons, contradiction, lowestAbove, List.head?_cons,
          beq_self_eq_true, ↓reduceIte, true_and]
        by_cases hlt : e < xr <;> cases m <;> simp [hlt]
      | some my =>
        obtain ⟨py, hay⟩ :=
          aboveOf_some w.graph hd (hnb y (List.mem_cons_of_mem _ List.mem_cons_self)) hmy
        have hside := hc.sides g hg e partner hep xr y m my hothers hm hmy
        simp only [List.filterMap_cons, List.filterMap_nil, hax, hay, Option.map_some,
          List.isEmpty_cons, contradiction, lowestAbove, List.head?_cons, beq_self_eq_true,
          ↓reduceIte, true_and]
        by_cases hlt : e < xr <;> by_cases hlt' : e < y <;> cases m <;> cases my <;>
          simp_all
    · -- the bond to the lower neighbour cannot carry a mark, so the writer
      -- chose the other one
      have hpx' : canCarryMark mol e x = false := by simpa using hpx
      simp only [hpx'] at hfind
      have hxr : xr = y := by
        split at hfind
        · exact (Option.some.inj hfind).symm
        · cases hfind
      subst hxr
      have hmx : markAmong marks (bondKey e x) = none := by
        cases hmx : markAmong marks (bondKey e x) with
        | none => rfl
        | some up => exact absurd (hc.canCarry e x up hmx) hpx
      have hax := aboveOf_none w.graph hd (hnb x List.mem_cons_self) hmx
      obtain ⟨py, hay⟩ :=
        aboveOf_some w.graph hd (hnb xr (List.mem_cons_of_mem _ List.mem_cons_self)) hm
      simp only [List.filterMap_cons, List.filterMap_nil, hax, hay, Option.map_some,
        Option.map_none, List.isEmpty_cons, contradiction, lowestAbove, List.head?_cons, hxy',
        Bool.false_eq_true, ↓reduceIte, true_and]
      by_cases hlt : e < xr <;> cases m <;> simp [hlt]
  | [], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h

/-- The two marks of a link that holds give the geometry of its double bond
back. `x` and `y` are the two marks (`true` for `/`), and `fa` and `fb` say,
for each of the two marked bonds, whether `/` there says that the
lowest-numbered neighbour lies above (what `reference` gives with the bond). -/
theorem geometry_of_link (x y fa fb : Bool) (geometry : Geometry)
    (h : (x == y) = ((fa == fb) == (geometry == Geometry.sameSide))) :
    (if ((x == fa) == (y == fb)) = true then Geometry.sameSide else Geometry.oppositeSides)
      = geometry := by
  cases geometry <;> cases x <;> cases y <;> cases fa <;> cases fb <;> simp_all

/-- **The geometries come back.** For a bond of the `Mol`, the marks that the
reader noted give the geometry that the `Mol` stores for it, with no problem,
or nothing if it stores none. -/
theorem geometryOfMarks_back {mol : Mol} {marks : List ((Nat × Nat) × Bool)}
    {directions : List Direction} (w : mol.WellFormed) (hc : MarksChosen mol marks)
    (hd : DirectionsNoted mol marks directions) {bond : Bond} (hbond : bond ∈ mol.bonds) :
    geometryOfMarks mol directions bond
      = (mol.geometryAt bond.a bond.b).map fun geometry =>
          ([], some ⟨bond.a, bond.b, geometry⟩) := by
  cases hg : mol.geometryAt bond.a bond.b with
  | some geometry =>
    have hmem := (Mol.geometryAt_eq_some w).1 hg
    obtain ⟨hcan, hdouble⟩ := Mol.canHave_of_geometryAt w hg
    -- the bond is that double bond
    have horder : bond.order = .double := by
      have := key_unique w.2.1 hbond hdouble rfl rfl
      rw [this]
    obtain ⟨link, hlink, x, y, hx, hy, hsame⟩ := hc.links _ hmem
    obtain ⟨atA, atB, hA, hB, rfl⟩ := geometryLink_eq_some hlink
    simp only at hx hy hsame
    have hlens : ((mol.otherNeighbours bond.a bond.b).length = 1 ∨
          (mol.otherNeighbours bond.a bond.b).length = 2) ∧
        ((mol.otherNeighbours bond.b bond.a).length = 1 ∨
          (mol.otherNeighbours bond.b bond.a).length = 2) := by
      unfold Mol.canHaveGeometry at hcan
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcan
      exact ⟨hcan.1.2, hcan.2⟩
    obtain ⟨hA1, hA2, hA3⟩ := side_read w hc hd hmem (Or.inl ⟨rfl, rfl⟩) hA hx hlens.1
    obtain ⟨hB1, hB2, hB3⟩ := side_read w hc hd hmem (Or.inr ⟨rfl, rfl⟩) hB hy hlens.2
    simp only at hA1 hA2 hA3 hB1 hB2 hB3
    unfold geometryOfMarks
    simp only [horder, hcan, hA1, hB1, hA2, hB2, hA3, hB3, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, Bool.or_self, Bool.false_eq_true, List.filterMap_cons, List.filterMap_nil,
      Option.map_none, List.isEmpty_nil, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      BondGeometry.mk.injEq, true_and]
    exact geometry_of_link x y atA.2 atB.2 geometry hsame
  | none =>
    simp only [Option.map_none]
    unfold geometryOfMarks
    rcases hc.noGeometry bond hbond hg with hnone | hnone | hnone | hnone
    · have hempty : markedOthers mol directions bond.a bond.b = [] := by
        unfold markedOthers
        rw [List.filterMap_eq_nil_iff]
        intro x hx
        rw [aboveOf_none w.graph hd (Mol.mem_otherNeighbours.1 hx).1 (hnone x hx)]
        rfl
      simp only [hempty, List.isEmpty_nil, Bool.true_or, ↓reduceIte, ite_self]
    · have hempty : markedOthers mol directions bond.b bond.a = [] := by
        unfold markedOthers
        rw [List.filterMap_eq_nil_iff]
        intro x hx
        rw [aboveOf_none w.graph hd (Mol.mem_otherNeighbours.1 hx).1 (hnone x hx)]
        rfl
      simp only [hempty, List.isEmpty_nil, Bool.or_true, ↓reduceIte, ite_self]
    · have : (bond.order == BondOrder.double) = false := by simpa using hnone
      simp only [this, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · simp only [hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-! ## The places of the ring numbers

Both spellings write the ring numbers of an atom in the same order: first
those that close, in the order of the atoms where they opened, and then those
that open, in the order of the atoms where they will close. `ring` says which
bonds a spelling writes with a ring number. -/

/-- A bond that closes at atom `i` with a ring number. -/
def closesAt (ring : Bond → Bool) (i : Nat) (e : Bond) : Bool := e.b == i && ring e

/-- A bond that opens at atom `i` with a ring number. -/
def opensAt (ring : Bond → Bool) (i : Nat) (e : Bond) : Bool := e.a == i && ring e

/-- The place of the ring number of the bond between `a` and `b` among the ring
numbers of `b`, where it closes: as many ring numbers close at `b` before it. -/
def placeB (l : List Bond) (ring : Bond → Bool) (a b : Nat) : Nat :=
  (l.filter fun x => decide (x.a < a) && closesAt ring b x).length

/-- Its place among the ring numbers of `a`, where it opens: behind all that
close at `a`, and behind those that open at `a` before it. -/
def placeA (l : List Bond) (ring : Bond → Bool) (a b : Nat) : Nat :=
  (l.filter (closesAt ring a)).length
    + (l.filter fun x => decide (x.b < b) && opensAt ring a x).length

/-- What the reader notes for a bond that is written with a ring number. -/
def ringEntry (l : List Bond) (ring : Bond → Bool) (e : Bond) : RingBond :=
  ⟨e.a, e.b, placeA l ring e.a e.b, placeB l ring e.a e.b⟩

/-- The place of the ring number that joins atom `i` to atom `j`, among the
ring numbers of `i`. -/
def rankAt (l : List Bond) (ring : Bond → Bool) (i j : Nat) : Nat :=
  if j < i then placeB l ring j i else placeA l ring i j

/-- A property that holds more often is counted at least as often. -/
theorem length_filter_le_of_imp {δ : Type} (p q : δ → Bool) :
    ∀ l : List δ, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    have ih := length_filter_le_of_imp p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- A property that holds more often is counted more often, if one entry tells
the two apart. -/
theorem length_filter_lt_of_imp {δ : Type} (p q : δ → Bool) :
    ∀ l : List δ, (∀ x ∈ l, p x = true → q x = true) → (∃ y ∈ l, q y = true ∧ p y = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, h => by
    obtain ⟨y, hy, _⟩ := h
    simp at hy
  | x :: l, h, hex => by
    have hle := length_filter_le_of_imp p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    obtain ⟨y, hy, hqy, hpy⟩ := hex
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hqy, hpy]
      omega
    · have ih := length_filter_lt_of_imp p q l (fun z hz => h z (List.mem_cons_of_mem _ hz))
        ⟨y, hy, hqy, hpy⟩
      cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- At one atom, the ring number of a bond to a lower atom stands before that
of a bond to a higher atom. -/
theorem rank_mono {l : List Bond} {ring : Bond → Bool} (hab : ∀ e ∈ l, e.a < e.b) {i j j' : Nat}
    (hj : ∃ e ∈ l, ring e = true ∧ ((e.a = j ∧ e.b = i) ∨ (e.a = i ∧ e.b = j)))
    (hj' : ∃ e ∈ l, ring e = true ∧ ((e.a = j' ∧ e.b = i) ∨ (e.a = i ∧ e.b = j')))
    (hlt : j < j') : rankAt l ring i j < rankAt l ring i j' := by
  obtain ⟨e, he, hre, hcase⟩ := hj
  obtain ⟨e', he', hre', hcase'⟩ := hj'
  have hab1 := hab e he
  have hab2 := hab e' he'
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- j is below i
    have hji : j < i := by omega
    have hstrict : placeB l ring j i < (l.filter (closesAt ring i)).length := by
      unfold placeB
      apply length_filter_lt_of_imp
      · intro x _ hx
        simp only [Bool.and_eq_true] at hx
        exact hx.2
      · exact ⟨e, he, by simp [closesAt, hb, hre], by simp [ha]⟩
    by_cases hj'i : j' < i
    · simp only [rankAt, hji, hj'i, ↓reduceIte]
      unfold placeB
      apply length_filter_lt_of_imp
      · intro x _ hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        exact ⟨by omega, hx.2⟩
      · exact ⟨e, he, by simp [closesAt, hb, ha, hre, hlt], by simp [ha]⟩
    · simp only [rankAt, hji, hj'i, ↓reduceIte]
      unfold placeA
      omega
  · -- j is above i, and so is j'
    have hij : ¬ j < i := by omega
    have hij' : ¬ j' < i := by omega
    simp only [rankAt, hij, hij', ↓reduceIte]
    unfold placeA
    have : (l.filter (fun x => decide (x.b < j) && opensAt ring i x)).length <
        (l.filter (fun x => decide (x.b < j') && opensAt ring i x)).length := by
      apply length_filter_lt_of_imp
      · intro x _ hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        exact ⟨by omega, hx.2⟩
      · exact ⟨e, he, by simp [opensAt, hb, ha, hre, hlt], by simp [hb]⟩
    omega

/-! ## What the reader noted for the ring numbers -/

/-- The reader noted exactly the bonds that are written with a ring number,
each with the places of its two ring numbers. -/
def RingsNoted (l : List Bond) (ring : Bond → Bool) (rings : List RingBond) : Prop :=
  rings.Perm ((l.filter ring).map (ringEntry l ring))

/-- The notes are exactly the entries of the bonds that are written with a
ring number. -/
theorem RingsNoted.mem_iff {l : List Bond} {ring : Bond → Bool} {rings : List RingBond}
    (h : RingsNoted l ring rings) (r : RingBond) :
    r ∈ rings ↔ ∃ e ∈ l, ring e = true ∧ r = ringEntry l ring e := by
  rw [List.Perm.mem_iff h, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, (List.mem_filter.1 he).1, (List.mem_filter.1 he).2, rfl⟩
  · rintro ⟨e, he, hr, rfl⟩
    exact ⟨e, List.mem_filter.2 ⟨he, hr⟩, rfl⟩

/-- The note of a bond that is written with a ring number. -/
theorem RingsNoted.ringBondOf_ring {l : List Bond} {ring : Bond → Bool} {rings : List RingBond}
    (h : RingsNoted l ring rings) (hl : l.Pairwise Bond.before) {e : Bond} (he : e ∈ l)
    (hr : ring e = true) : ringBondOf rings e.a e.b = some (ringEntry l ring e) := by
  unfold ringBondOf
  cases hf : rings.find? (fun r => r.a == e.a && r.b == e.b) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf (ringEntry l ring e) ((h.mem_iff _).2 ⟨e, he, hr, rfl⟩)
    simp [ringEntry] at this
  | some r =>
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨e', he', _, rfl⟩ := (h.mem_iff r).1 hmem
    have : e' = e := key_unique hl he' he hp.1 hp.2
    rw [this]

/-- A bond that is written by position has no note. -/
theorem RingsNoted.ringBondOf_chain {l : List Bond} {ring : Bond → Bool} {rings : List RingBond}
    (h : RingsNoted l ring rings) {a b : Nat}
    (hchain : ∀ e ∈ l, e.a = a → e.b = b → ring e = false) : ringBondOf rings a b = none := by
  unfold ringBondOf
  rw [List.find?_eq_none]
  intro r hr hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨e, he, hre, rfl⟩ := (h.mem_iff r).1 hr
  have := hchain e he hp.1 hp.2
  rw [hre] at this
  cases this

/-- Counting the entries with one of two properties, when no entry has both. -/
theorem length_filter_or {δ : Type} (p q : δ → Bool) :
    ∀ l : List δ, (∀ x ∈ l, ¬ (p x = true ∧ q x = true)) →
      (l.filter fun x => p x || q x).length = (l.filter p).length + (l.filter q).length
  | [], _ => rfl
  | x :: l, h => by
    have ih := length_filter_or p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- How many ring numbers the reader counts at an atom: those that close there
and those that open there. -/
theorem RingsNoted.ringNumbersAt {l : List Bond} {ring : Bond → Bool} {rings : List RingBond}
    (h : RingsNoted l ring rings) (hab : ∀ e ∈ l, e.a < e.b) (atom : Nat) :
    ringNumbersAt rings atom
      = (l.filter (closesAt ring atom)).length + (l.filter (opensAt ring atom)).length := by
  unfold VeriMol.ringNumbersAt
  rw [(List.Perm.filter _ h).length_eq, List.filter_map, List.length_map, List.filter_filter]
  rw [← length_filter_or]
  · congr 1
    apply List.filter_congr
    intro e _
    simp only [Function.comp, ringEntry, closesAt, opensAt]
    cases ring e <;> cases (e.a == atom) <;> cases (e.b == atom) <;> rfl
  · intro e he hboth
    have := hab e he
    simp only [closesAt, opensAt, Bool.and_eq_true, beq_iff_eq] at hboth
    omega

/-! ## The orientation of an atom

The mark of an atom is said for the order in which the text writes its places.
The writer works that order out from where it writes the atoms (`placeKey` in
`VeriMol/Core/Write.lean`; `parKey` below is the same, said with any function
that gives an atom its parent), and the reader from what it noted
(`writtenKey`). Both give the same order. -/

/-- How a spelling writes the bonds of a `Mol`: `par` gives the atom that an
atom is written next to, if there is one, and `ring` says which bonds get a
ring number: those that do not join an atom to the atom it is written next
to. -/
structure Written (mol : Mol) (par : Nat → Option Nat) (ring : Bond → Bool) : Prop where
  ring_iff : ∀ e ∈ mol.bonds, ring e = true ↔ par e.b ≠ some e.a
  par_lt : ∀ x p, par x = some p → p < x

/-- Where a spelling writes a place of atom `atom`, as a key: the atom that it
is written next to; its fourth place; its ring numbers, in the order of the
other atom's number; the later atoms that are written next to it. -/
def parKey (par : Nat → Option Nat) (atom : Nat) : Place → Nat × Nat
  | none => (1, 0)
  | some other =>
    if par atom = some other then (0, 0)
    else if par other = some atom then (3, other) else (2, other)

/-- Two ways of giving keys to places that put every two places of a list in
the same order have as many pairs in falling order. -/
theorem fallingKeys_congr (f g : Place → Nat × Nat) :
    ∀ l : List Place, (∀ p ∈ l, ∀ q ∈ l, keyBefore (f p) (f q) = keyBefore (g p) (g q)) →
      fallingKeys (l.map f) = fallingKeys (l.map g)
  | [], _ => rfl
  | x :: rest, h => by
    have ih := fallingKeys_congr f g rest
      (fun p hp q hq => h p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, fallingKeys, ih, List.filter_map, List.length_map]
    congr 2
    apply List.filter_congr
    intro q hq
    exact h q (List.mem_cons_of_mem _ hq) x List.mem_cons_self

/-- The key that the reader gives to a place is the key of the writer, or
both are keys of a ring number: the reader's with the place of the number,
the writer's with the other atom. -/
theorem key_shape {mol : Mol} (w : mol.GraphWellFormed) {par : Nat → Option Nat}
    {ring : Bond → Bool} {rings : List RingBond} (hw : Written mol par ring)
    (hr : RingsNoted mol.bonds ring rings) {atom : Nat} {p : Place} (hp : p ∈ mol.places atom) :
    (writtenKey rings atom p = parKey par atom p ∧ (parKey par atom p).1 ≠ 2) ∨
    ∃ x, (∃ e ∈ mol.bonds, ring e = true ∧ ((e.a = x ∧ e.b = atom) ∨ (e.a = atom ∧ e.b = x))) ∧
      writtenKey rings atom p = (2, rankAt mol.bonds ring atom x) ∧ parKey par atom p = (2, x) := by
  cases p with
  | none => exact Or.inl ⟨rfl, by simp [parKey]⟩
  | some x =>
    obtain ⟨order, hj | hj⟩ := Mol.mem_neighbours.1 (Mol.mem_places.1 hp)
    · -- the bond leads to a later atom
      have hlt := (w.1 _ hj).1
      simp only at hlt
      have hnlt : ¬ x < atom := by omega
      have hnotpar : par atom ≠ some x := fun e => by
        have := hw.par_lt _ _ e
        omega
      cases hre : ring ⟨atom, x, order⟩ with
      | true =>
        right
        have hpar : par x ≠ some atom := (hw.ring_iff _ hj).1 hre
        refine ⟨x, ⟨_, hj, hre, Or.inr ⟨rfl, rfl⟩⟩, ?_, ?_⟩
        · have := hr.ringBondOf_ring w.2 hj hre
          simp only at this
          simp only [writtenKey, hnlt, ↓reduceIte, this, rankAt, ringEntry]
        · simp only [parKey, hnotpar, hpar, ↓reduceIte]
      | false =>
        left
        have hpar : par x = some atom := by
          apply Classical.byContradiction
          intro hne
          have := (hw.ring_iff _ hj).2 hne
          rw [hre] at this
          cases this
        have hnone : ringBondOf rings atom x = none := by
          apply hr.ringBondOf_chain
          intro e he ha hb
          have : e = ⟨atom, x, order⟩ := key_unique w.2 he hj ha hb
          rw [this, hre]
        constructor
        · simp only [writtenKey, hnlt, ↓reduceIte, hnone, parKey, hnotpar, hpar]
        · simp only [parKey, hnotpar, hpar, ↓reduceIte]
          decide
    · -- the bond comes from an earlier atom
      have hlt := (w.1 _ hj).1
      simp only at hlt
      have hnotchild : par x ≠ some atom := fun e => by
        have := hw.par_lt _ _ e
        omega
      cases hre : ring ⟨x, atom, order⟩ with
      | true =>
        right
        have hpar : par atom ≠ some x := (hw.ring_iff _ hj).1 hre
        refine ⟨x, ⟨_, hj, hre, Or.inl ⟨rfl, rfl⟩⟩, ?_, ?_⟩
        · have := hr.ringBondOf_ring w.2 hj hre
          simp only at this
          simp only [writtenKey, hlt, ↓reduceIte, this, rankAt, ringEntry]
        · simp only [parKey, hnotchild, hpar, ↓reduceIte]
      | false =>
        left
        have hpar : par atom = some x := by
          apply Classical.byContradiction
          intro hne
          have := (hw.ring_iff _ hj).2 hne
          rw [hre] at this
          cases this
        have hnone : ringBondOf rings x atom = none := by
          apply hr.ringBondOf_chain
          intro e he ha hb
          have : e = ⟨x, atom, order⟩ := key_unique w.2 he hj ha hb
          rw [this, hre]
        constructor
        · simp only [writtenKey, hlt, ↓reduceIte, hnone, parKey, hpar]
        · simp only [parKey, hpar, ↓reduceIte]
          decide

/-- The reader and the writer put every two places of an atom in the same
order. -/
theorem keys_agree {mol : Mol} (w : mol.GraphWellFormed) {par : Nat → Option Nat}
    {ring : Bond → Bool} {rings : List RingBond} (hw : Written mol par ring)
    (hr : RingsNoted mol.bonds ring rings) (atom : Nat) :
    ∀ p ∈ mol.places atom, ∀ q ∈ mol.places atom,
      keyBefore (writtenKey rings atom p) (writtenKey rings atom q)
        = keyBefore (parKey par atom p) (parKey par atom q) := by
  intro p hp q hq
  have hab : ∀ e ∈ mol.bonds, e.a < e.b := fun e he => (w.1 e he).1
  rcases key_shape w hw hr hp with ⟨h1, h1'⟩ | ⟨x, hx, h1, h1'⟩ <;>
    rcases key_shape w hw hr hq with ⟨h2, h2'⟩ | ⟨y, hy, h2, h2'⟩
  · rw [h1, h2]
  · rw [h1, h2, h2']
    have hb : ((parKey par atom p).1 == 2) = false := by simpa using h1'
    simp [keyBefore, hb]
  · rw [h1, h2, h1']
    have hb : ((2 : Nat) == (parKey par atom q).1) = false := by
      have : ¬ (2 = (parKey par atom q).1) := fun e => h2' e.symm
      simpa using this
    simp [keyBefore, hb]
  · rw [h1, h2, h1', h2']
    have hiff : rankAt mol.bonds ring atom x < rankAt mol.bonds ring atom y ↔ x < y := by
      constructor
      · intro hrank
        apply Classical.byContradiction
        intro hnot
        by_cases heq : x = y
        · subst heq
          omega
        · have := rank_mono hab hy hx (by omega)
          omega
      · intro hlt
        exact rank_mono hab hx hy hlt
    simp [keyBefore, hiff]

/-- The reader takes an atom to be written next to an earlier atom exactly
when one of its bonds to an earlier atom has no ring number. -/
theorem hasParent_iff {mol : Mol} (w : mol.GraphWellFormed) {ring : Bond → Bool}
    {rings : List RingBond} (hr : RingsNoted mol.bonds ring rings) (atom : Nat) :
    hasParent mol rings atom = true ↔ ∃ e ∈ mol.bonds, e.b = atom ∧ ring e = false := by
  unfold hasParent
  rw [List.any_eq_true]
  constructor
  · rintro ⟨other, hother, hboth⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hboth
    obtain ⟨hlt, hnone⟩ := hboth
    obtain ⟨order, hj | hj⟩ := Mol.mem_neighbours.1 hother
    · have := (w.1 _ hj).1
      simp only at this
      omega
    · refine ⟨_, hj, rfl, ?_⟩
      cases hre : ring ⟨other, atom, order⟩ with
      | false => rfl
      | true =>
        have := hr.ringBondOf_ring w.2 hj hre
        simp only at this
        rw [hnone] at this
        cases this
  · rintro ⟨e, he, rfl, hre⟩
    refine ⟨e.a, Mol.mem_neighbours.2 ⟨e.order, Or.inr he⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
    refine ⟨(w.1 e he).1, ?_⟩
    apply hr.ringBondOf_chain
    intro e' he' ha hb
    have : e' = e := key_unique w.2 he' he ha hb
    rw [this, hre]

/-- **The orientations come back.** The mark that a spelling writes for an
atom with an orientation, read with the notes of the reader, gives the
orientation that the `Mol` stores. `atomBefore` and `numbersAtAtom` are what
the writer asked `centreRefusal` with. -/
theorem orientationOfMark_back {mol : Mol} (w : mol.WellFormed) {par : Nat → Option Nat}
    {ring : Bond → Bool} {rings : List RingBond} (hw : Written mol par ring)
    (hr : RingsNoted mol.bonds ring rings) {atom : Nat} {stored : Orientation}
    (hat : mol.orientationAt atom = some stored) {atomBefore : Bool} {numbersAtAtom : Nat}
    (hparent : atomBefore = true ↔ ∃ e ∈ mol.bonds, e.b = atom ∧ ring e = false)
    (hcount : numbersAtAtom = (mol.bonds.filter (closesAt ring atom)).length
      + (mol.bonds.filter (opensAt ring atom)).length)
    (hrefusal : centreRefusal mol atom atomBefore numbersAtAtom = none) (position : Nat) :
    orientationOfMark mol rings ⟨atom, mol.turnedForText atom (parKey par atom) stored, position⟩
      = .ok ⟨atom, stored⟩ := by
  have hfour := (Mol.fourPlaces_of_orientationAt w hat).1
  have hpar : hasParent mol rings atom = atomBefore := by
    rw [Bool.eq_iff_iff]
    exact (hasParent_iff w.graph hr atom).trans hparent.symm
  have hnum : ringNumbersAt rings atom = numbersAtAtom := by
    rw [hr.ringNumbersAt (fun e he => (w.1 e he).1) atom, hcount]
  have hkeys : fallingKeys ((mol.places atom).map (writtenKey rings atom))
      = fallingKeys ((mol.places atom).map (parKey par atom)) :=
    fallingKeys_congr _ _ _ (keys_agree w.graph hw hr atom)
  unfold centreRefusal at hrefusal
  unfold orientationOfMark Mol.turnedForText
  simp only [hfour, hpar, hnum, hkeys, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  split at hrefusal
  · cases hrefusal
  · rename_i h1
    split at hrefusal
    · cases hrefusal
    · rename_i h2
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Orientation.turnedIf_turnedIf,
        bne_self_eq_false, Orientation.turnedIf_false]

/-! ## All marks of a text -/

/-- `filterMap` gives the same list for two functions that agree on the entries
of the list. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The first problem of a list is one of its problems. -/
theorem mem_of_firstProblem : ∀ {problems : List Problem} {problem : Problem},
    firstProblem problems = some problem → problem ∈ problems
  | [], _, h => by cases h
  | p :: rest, problem, h => by
    simp only [firstProblem] at h
    split at h
    · cases h
      exact List.mem_cons_self
    · rename_i other hother
      split at h
      · cases h
        exact List.mem_cons_of_mem _ (mem_of_firstProblem hother)
      · cases h
        exact List.mem_cons_self

/-- The orientations of a well formed `Mol`, atom by atom. -/
theorem Mol.orientations_eq_filterMap {mol : Mol} (w : mol.WellFormed) :
    ((List.range mol.atoms.length).filterMap fun atom =>
        (mol.orientationAt atom).map fun stored => (⟨atom, stored⟩ : AtomOrientation))
      = mol.orientations := by
  refine eq_of_pairwise_of_mem_iff (r := fun x y : AtomOrientation => x.atom < y.atom)
    (fun x => Nat.lt_irrefl _) (fun x y hxy => Nat.lt_asymm hxy) ?_ w.2.2.1 ?_
  · refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
    intro a a' haa o ho o' ho'
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 ho
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 ho'
    exact haa
  · rintro ⟨atom, o⟩
    rw [List.mem_filterMap, ← Mol.orientationAt_eq_some w]
    constructor
    · rintro ⟨a, _, ha⟩
      obtain ⟨stored, hs, heq⟩ := Option.map_eq_some_iff.1 ha
      cases heq
      exact hs
    · intro h
      exact ⟨atom, List.mem_range.2 (Mol.fourPlaces_of_orientationAt w h).2, by rw [h]; rfl⟩

/-- The geometries of a well formed `Mol`, bond by bond. -/
theorem Mol.geometries_eq_filterMap {mol : Mol} (w : mol.WellFormed) :
    (mol.bonds.filterMap fun bond =>
        (mol.geometryAt bond.a bond.b).map fun geometry =>
          (⟨bond.a, bond.b, geometry⟩ : BondGeometry))
      = mol.geometries := by
  refine eq_of_pairwise_of_mem_iff
    (r := fun x y : BondGeometry => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b))
    (fun x => by omega) (fun x y hxy => by omega) ?_ w.2.2.2.2.1 ?_
  · refine List.Pairwise.filterMap _ ?_ w.2.1
    intro bond bond' hbb g hg g' hg'
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hg
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hg'
    exact hbb
  · rintro ⟨a, b, s⟩
    rw [List.mem_filterMap, ← Mol.geometryAt_eq_some w]
    constructor
    · rintro ⟨bond, _, hb⟩
      obtain ⟨geometry, hgeo, heq⟩ := Option.map_eq_some_iff.1 hb
      cases heq
      exact hgeo
    · intro h
      exact ⟨⟨a, b, .double⟩, (Mol.canHave_of_geometryAt w h).2, by simp [h]⟩

/-- The reader noted `@` or `@@` for exactly the atoms with an orientation,
each with the mark that the spelling writes for it. -/
structure MarkedNoted (mol : Mol) (par : Nat → Option Nat) (marked : List MarkedAtom) : Prop where
  without : ∀ atom, mol.orientationAt atom = none →
    marked.find? (fun found => found.atom == atom) = none
  withOne : ∀ atom stored, mol.orientationAt atom = some stored → ∃ position,
    marked.find? (fun found => found.atom == atom)
      = some ⟨atom, mol.turnedForText atom (parKey par atom) stored, position⟩

/-- The writer asked whether the atom `number`, which has an orientation, can
be written where it stands, and was not refused (`centreRefusal`). `ring`
says which bonds the spelling writes with a ring number. -/
def CentreAsked (mol : Mol) (ring : Bond → Bool) (number : Nat) : Prop :=
  ∃ (atomBefore : Bool) (numbersAtAtom : Nat),
    (atomBefore = true ↔ ∃ e ∈ mol.bonds, e.b = number ∧ ring e = false) ∧
    numbersAtAtom = (mol.bonds.filter (closesAt ring number)).length
      + (mol.bonds.filter (opensAt ring number)).length ∧
    centreRefusal mol number atomBefore numbersAtAtom = none

/-- **The stereo facts come back.** If the reader noted what a spelling writes
for a well formed `Mol`, then the stereo step of the reader gives the stereo
facts of that `Mol`, and no problem.

`par` and `ring` say how the spelling writes the bonds. `hcentres` says that
the writer asked for every atom with an orientation whether it can be written
where it stands, and was not refused. -/
theorem stereoFacts_back {mol : Mol} (w : mol.WellFormed) {marks : List ((Nat × Nat) × Bool)}
    (hmarks : chooseMarks mol = .ok marks) {par : Nat → Option Nat} {ring : Bond → Bool}
    (hw : Written mol par ring) {rings : List RingBond} {directions : List Direction}
    {marked : List MarkedAtom} (hr : RingsNoted mol.bonds ring rings)
    (hd : DirectionsNoted mol marks directions) (hm : MarkedNoted mol par marked)
    (hcentres : ∀ atom stored, mol.orientationAt atom = some stored →
      CentreAsked mol ring atom) :
    stereoFacts mol rings directions marked = .ok (mol.orientations, mol.geometries) := by
  have hc := marksChosen w hmarks
  -- the atoms: every mark gives the stored orientation
  have hatoms : ((List.range mol.atoms.length).filterMap fun atom =>
        (marked.find? fun found => found.atom == atom).map (orientationOfMark mol rings))
      = (List.range mol.atoms.length).filterMap fun atom =>
        (mol.orientationAt atom).map fun stored => Except.ok ⟨atom, stored⟩ := by
    apply filterMap_congr
    intro atom _
    cases hat : mol.orientationAt atom with
    | none =>
      rw [hm.without atom hat]
      rfl
    | some stored =>
      obtain ⟨position, hfound⟩ := hm.withOne atom stored hat
      obtain ⟨atomBefore, numbersAtAtom, hparent, hcount, hrefusal⟩ := hcentres atom stored hat
      rw [hfound]
      simp only [Option.map_some]
      rw [orientationOfMark_back w hw hr hat hparent hcount hrefusal]
  -- the bonds: the marks give every stored geometry, and no other
  have hjudged : (mol.bonds.filterMap fun bond =>
        (geometryOfMarks mol directions bond).map fun verdict => (bond, verdict))
      = mol.bonds.filterMap fun bond =>
        (mol.geometryAt bond.a bond.b).map fun geometry =>
          (bond, (([] : List Problem), some (⟨bond.a, bond.b, geometry⟩ : BondGeometry))) := by
    apply filterMap_congr
    intro bond hbond
    rw [geometryOfMarks_back w hc hd hbond]
    cases mol.geometryAt bond.a bond.b <;> rfl
  -- no mark stands alone
  have halone : ∀ d ∈ directions,
      ((mol.bonds.filterMap fun bond =>
        (mol.geometryAt bond.a bond.b).map fun geometry =>
          (bond, (([] : List Problem), some (⟨bond.a, bond.b, geometry⟩ : BondGeometry)))).any
        fun found => d.a == found.1.a || d.a == found.1.b || d.b == found.1.a
          || d.b == found.1.b) = true := by
    intro d hdmem
    obtain ⟨e, _, ha, hb, hmark⟩ := hd.marked d hdmem
    obtain ⟨g, hg, htouch⟩ := hc.touches _ _ hmark
    simp only at htouch
    have hgat := (Mol.geometryAt_eq_some w).2 hg
    rw [List.any_eq_true]
    refine ⟨(⟨g.a, g.b, .double⟩, ([], some ⟨g.a, g.b, g.geometry⟩)), ?_, ?_⟩
    · rw [List.mem_filterMap]
      exact ⟨⟨g.a, g.b, .double⟩, (Mol.canHave_of_geometryAt w hgat).2, by simp [hgat]⟩
    · simp only [ha, hb, Bool.or_eq_true, beq_iff_eq]
      rcases htouch with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
  unfold stereoFacts
  simp only [hatoms, hjudged]
  split
  · -- there is no problem
    rename_i problem hproblem
    exfalso
    have hmem := mem_of_firstProblem hproblem
    rcases List.mem_append.1 hmem with hmem | hmem
    · rcases List.mem_append.1 hmem with hmem | hmem
      · obtain ⟨found, hfound, hp⟩ := List.mem_filterMap.1 hmem
        obtain ⟨atom, _, hat⟩ := List.mem_filterMap.1 hfound
        cases horient : mol.orientationAt atom with
        | none => rw [horient] at hat; cases hat
        | some stored =>
          rw [horient] at hat
          cases hat
          cases hp
      · obtain ⟨found, hfound, hp⟩ := List.mem_flatMap.1 hmem
        obtain ⟨bond, _, hb⟩ := List.mem_filterMap.1 hfound
        cases hgeo : mol.geometryAt bond.a bond.b with
        | none => rw [hgeo] at hb; cases hb
        | some geometry =>
          rw [hgeo] at hb
          cases hb
          cases hp
    · obtain ⟨d, hdmem, _⟩ := List.mem_map.1 hmem
      obtain ⟨hdin, hnot⟩ := List.mem_filter.1 hdmem
      rw [halone d hdin] at hnot
      cases hnot
  · -- and the two lists are those of the `Mol`
    congr 2
    · rw [List.filterMap_filterMap, ← Mol.orientations_eq_filterMap w]
      apply filterMap_congr
      intro atom _
      cases mol.orientationAt atom <;> rfl
    · rw [List.filterMap_filterMap, ← Mol.geometries_eq_filterMap w]
      apply filterMap_congr
      intro bond _
      cases mol.geometryAt bond.a bond.b <;> rfl

end VeriMol
