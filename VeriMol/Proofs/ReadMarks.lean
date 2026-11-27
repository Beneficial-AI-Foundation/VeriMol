import VeriMol.Core.ReadMarks

/-!
# What the stereo step of the reader gives (SPEC.md, section 12.2)

`stereoFacts` (`VeriMol/Core/ReadMarks.lean`) turns the stereo marks of a text
into stereo facts. For a `Mol` whose bonds are in order, the two lists that it
gives are as a well formed `Mol` wants them (`stereoFacts_wellFormed`): in
order, each atom with four places, each bond a double bond that can have a
geometry.
-/

namespace VeriMol

/-- What `orientationOfMark` gives is an orientation of the atom that carries
the mark, and that atom has four places. -/
theorem orientationOfMark_ok {mol : Mol} {rings : List RingBond} {marked : MarkedAtom}
    {orientation : AtomOrientation} (h : orientationOfMark mol rings marked = .ok orientation) :
    orientation.atom = marked.atom ∧ mol.hasFourPlaces marked.atom = true := by
  unfold orientationOfMark at h
  split at h
  · cases h
  · rename_i hfour
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, by simpa using hfour⟩

/-- What `geometryOfMarks` gives is a geometry of the bond it was asked about,
and that bond is a double bond that can have a geometry. -/
theorem geometryOfMarks_some {mol : Mol} {directions : List Direction} {bond : Bond}
    {problems : List Problem} {geometry : BondGeometry}
    (h : geometryOfMarks mol directions bond = some (problems, some geometry)) :
    geometry.a = bond.a ∧ geometry.b = bond.b ∧ mol.canHaveGeometry bond.a bond.b = true := by
  unfold geometryOfMarks at h
  split at h
  · rename_i hcan
    simp only [Bool.and_eq_true] at hcan
    simp only at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hg⟩ := h
      split at hg
      · cases hg
        exact ⟨rfl, rfl, hcan.2⟩
      · cases hg
  · cases h

/-- The two lists of stereo facts that `stereoFacts` gives for a `Mol` whose
bonds are in order are as a well formed `Mol` wants them. -/
theorem stereoFacts_wellFormed {mol : Mol} {rings : List RingBond} {directions : List Direction}
    {marked : List MarkedAtom} {facts : List AtomOrientation × List BondGeometry}
    (hbonds : mol.bonds.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)))
    (h : stereoFacts mol rings directions marked = .ok facts) :
    facts.1.Pairwise (fun x y => x.atom < y.atom) ∧
      (∀ x ∈ facts.1, mol.hasFourPlaces x.atom = true) ∧
      facts.2.Pairwise (fun x y => x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)) ∧
      (∀ x ∈ facts.2, mol.canHaveGeometry x.a x.b = true) := by
  unfold stereoFacts at h
  simp only at h
  split at h
  · cases h
  · cases h
    simp only [List.filterMap_filterMap]
    -- an orientation that comes out for the number `atom` is an orientation of that atom
    have hof : ∀ (atom : Nat) (o : AtomOrientation),
        (((marked.find? fun m => m.atom == atom).map (orientationOfMark mol rings)).bind
          fun found => match found with
            | .ok orientation => some orientation
            | .error _ => none) = some o →
        o.atom = atom ∧ mol.hasFourPlaces o.atom = true := by
      intro atom o ho
      rw [Option.bind_eq_some_iff] at ho
      obtain ⟨found, hfound, hok⟩ := ho
      rw [Option.map_eq_some_iff] at hfound
      obtain ⟨m, hm, rfl⟩ := hfound
      have hma : m.atom = atom := by simpa using List.find?_some hm
      split at hok
      · rename_i orientation heq
        cases hok
        obtain ⟨h1, h2⟩ := orientationOfMark_ok heq
        rw [h1, hma]
        exact ⟨rfl, hma ▸ h2⟩
      · cases hok
    -- a geometry that comes out for a bond is a geometry of that bond
    have hgo : ∀ (bond : Bond) (g : BondGeometry),
        (((geometryOfMarks mol directions bond).map fun verdict => (bond, verdict)).bind
          fun found => found.2.2) = some g →
        g.a = bond.a ∧ g.b = bond.b ∧ mol.canHaveGeometry bond.a bond.b = true := by
      intro bond g hg
      rw [Option.bind_eq_some_iff] at hg
      obtain ⟨found, hfound, hsome⟩ := hg
      rw [Option.map_eq_some_iff] at hfound
      obtain ⟨verdict, hverdict, rfl⟩ := hfound
      obtain ⟨problems, geometry⟩ := verdict
      simp only at hsome
      subst hsome
      exact geometryOfMarks_some hverdict
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
      intro a a' haa o ho o' ho'
      rw [(hof a o ho).1, (hof a' o' ho').1]
      exact haa
    · intro x hx
      obtain ⟨atom, -, hatom⟩ := List.mem_filterMap.mp hx
      exact (hof atom x hatom).2
    · refine List.Pairwise.filterMap _ ?_ hbonds
      intro bond bond' hbb g hg g' hg'
      obtain ⟨h1, h2, -⟩ := hgo bond g hg
      obtain ⟨h1', h2', -⟩ := hgo bond' g' hg'
      rw [h1, h2, h1', h2']
      exact hbb
    · intro x hx
      obtain ⟨bond, -, hbond⟩ := List.mem_filterMap.mp hx
      obtain ⟨h1, h2, h3⟩ := hgo bond x hbond
      rw [h1, h2]
      exact h3

end VeriMol
