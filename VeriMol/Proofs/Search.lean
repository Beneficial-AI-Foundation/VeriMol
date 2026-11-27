import VeriMol.Core.Search

/-!
# What the search for the least order finds

The search of `VeriMol/Core/Search.lean` holds, after every round, beginnings
of that length whose key is the least, and every beginning with the least key
counts as the same as one that is held (`Holds`, `search_holds`). Without
outlines, "counts as the same" is "is equal": the search then holds exactly
the beginnings with the least key. So what it ends with are orders with the
least key (`search_least`).

What the outlines must do is said by `Merges`: two beginnings with the same
outline can be extended by the same items, the extensions get the same
entries, and they have the same outline again.

The search with a limit gives the same answer whenever it gives one
(`searchWithin_eq`).

If the items are given other names, and the keys do not depend on the names,
a renamed beginning has the same key (`Renames`). `VeriMol/Proofs/Chosen.lean`
uses this for two renamings: exchanging two atoms that can be exchanged, and
numbering the atoms of a `Mol` differently.

The second half of the file is about the tie-break for items that can be
exchanged, which the program uses to find the chosen form, and about what
does not depend on the names of the items although the tie-break does:
whether the search gives up (`Twins.exists_renaming`,
`Renames.searchWithin_isSome`).

Throughout, the comparison of entries is a total order (`IsOrder`), and no
item stands twice among the items.
-/

namespace VeriMol
namespace Search

variable {α κ : Type}

/-! ## Keys and the search -/

theorem keysFrom_append (k : List α → α → κ) (done p : List α) (a : α) :
    keysFrom k done (p ++ [a]) = keysFrom k done p ++ [k (done ++ p) a] := by
  induction p generalizing done with
  | nil => simp [keysFrom]
  | cons x xs ih => simp [keysFrom, ih]

theorem keys_append (k : List α → α → κ) (p : List α) (a : α) :
    keys k (p ++ [a]) = keys k p ++ [k p a] := by
  simpa [keys] using keysFrom_append k [] p a

theorem length_keysFrom (k : List α → α → κ) (done p : List α) :
    (keysFrom k done p).length = p.length := by
  induction p generalizing done with
  | nil => rfl
  | cons x xs ih => simp [keysFrom, ih]

theorem length_keys (k : List α → α → κ) (p : List α) : (keys k p).length = p.length :=
  length_keysFrom k [] p

/-- One key comes strictly before another: at the first place where they
differ, its entry is the smaller one. -/
def Before (lt : κ → κ → Prop) (xs ys : List κ) : Prop :=
  ∃ common x y r₁ r₂, xs = common ++ x :: r₁ ∧ ys = common ++ y :: r₂ ∧ lt x y

/-- No later: equal, or strictly before. -/
def NoLater (lt : κ → κ → Prop) (xs ys : List κ) : Prop :=
  xs = ys ∨ Before lt xs ys

theorem Before.append_right {lt : κ → κ → Prop} {xs ys : List κ} (h : Before lt xs ys)
    (u v : List κ) : Before lt (xs ++ u) (ys ++ v) := by
  obtain ⟨c, x, y, r₁, r₂, h₁, h₂, hlt⟩ := h
  exact ⟨c, x, y, r₁ ++ u, r₂ ++ v, by simp [h₁], by simp [h₂], hlt⟩

theorem Before.last {lt : κ → κ → Prop} (xs : List κ) {x y : κ} (h : lt x y) :
    Before lt (xs ++ [x]) (xs ++ [y]) :=
  ⟨xs, x, y, [], [], rfl, rfl, h⟩

/-- An order of some of the items: no item twice, and nothing but items. -/
def IsBeginning (items p : List α) : Prop :=
  p.Nodup ∧ ∀ a ∈ p, a ∈ items

/-- The comparison of entries is a total order. -/
structure IsOrder (le : κ → κ → Bool) : Prop where
  total : ∀ x y, le x y = true ∨ le y x = true
  trans : ∀ x y z, le x y = true → le y z = true → le x z = true
  antisymm : ∀ x y, le x y = true → le y x = true → x = y

/-- Strictly smaller. -/
def Lt (le : κ → κ → Bool) (x y : κ) : Prop := le y x = false

/-! ## The least entry -/

/-- One step of looking for the least entry. -/
def better (le : κ → κ → Bool) (best : Option κ) (x : κ) : Option κ :=
  match best with
  | none => some x
  | some y => if le y x then some y else some x

/-- `leastEntry` is a fold over the entries with `better`. -/
theorem leastEntry_eq (k : List α → α → κ) (le : κ → κ → Bool) (pairs : List (List α × α)) :
    leastEntry k le pairs = (pairs.map fun e => k e.1 e.2).foldl (better le) none := by
  unfold leastEntry
  rw [List.foldl_map]
  rfl

/-- Starting from an entry, the fold ends with an entry that is the start or
one of the list, and that is no larger than the start and than every entry of
the list. -/
theorem foldl_better {le : κ → κ → Bool} (ho : IsOrder le) :
    ∀ (l : List κ) (y : κ), ∃ b, l.foldl (better le) (some y) = some b ∧ (b = y ∨ b ∈ l) ∧
      le b y = true ∧ ∀ x ∈ l, le b x = true
  | [], y => ⟨y, rfl, Or.inl rfl, by rcases ho.total y y with h | h <;> exact h, by simp⟩
  | x :: xs, y => by
    by_cases hle : le y x = true
    · obtain ⟨b, hb, hfrom, hby, hall⟩ := foldl_better ho xs y
      refine ⟨b, by simp [better, hle, hb], ?_, hby, ?_⟩
      · rcases hfrom with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ho.trans _ _ _ hby hle
        · exact hall z hz
    · have hxy : le x y = true := by
        rcases ho.total y x with h | h
        · exact absurd h hle
        · exact h
      obtain ⟨b, hb, hfrom, hbx, hall⟩ := foldl_better ho xs x
      refine ⟨b, by simp [better, hle, hb], Or.inr ?_, ho.trans _ _ _ hbx hxy, ?_⟩
      · rcases hfrom with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ h
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hbx
        · exact hall z hz

/-- The least entry is the entry of one of the extensions. -/
theorem leastEntry_mem (k : List α → α → κ) {le : κ → κ → Bool} (ho : IsOrder le)
    {pairs : List (List α × α)} {best : κ} (h : leastEntry k le pairs = some best) :
    ∃ e ∈ pairs, k e.1 e.2 = best := by
  rw [leastEntry_eq] at h
  cases pairs with
  | nil => simp at h
  | cons e rest =>
    simp only [List.map_cons, List.foldl_cons, better] at h
    obtain ⟨b, hb, hfrom, _, _⟩ := foldl_better ho (rest.map fun e => k e.1 e.2) (k e.1 e.2)
    rw [hb] at h
    cases h
    rcases hfrom with h | h
    · exact ⟨e, List.mem_cons_self .., h.symm⟩
    · obtain ⟨e', he', hk⟩ := List.mem_map.1 h
      exact ⟨e', List.mem_cons_of_mem _ he', hk⟩

/-- No extension has a smaller entry. -/
theorem leastEntry_le (k : List α → α → κ) {le : κ → κ → Bool} (ho : IsOrder le)
    {pairs : List (List α × α)} {best : κ} (h : leastEntry k le pairs = some best) :
    ∀ e ∈ pairs, le best (k e.1 e.2) = true := by
  rw [leastEntry_eq] at h
  cases pairs with
  | nil => simp at h
  | cons e rest =>
    simp only [List.map_cons, List.foldl_cons, better] at h
    obtain ⟨b, hb, _, hbe, hall⟩ := foldl_better ho (rest.map fun e => k e.1 e.2) (k e.1 e.2)
    rw [hb] at h
    cases h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hbe
    · exact hall _ (List.mem_map.2 ⟨e', he', rfl⟩)

/-- There is a least entry as soon as there is an extension. -/
theorem leastEntry_some_of_ne_nil (k : List α → α → κ) {le : κ → κ → Bool} (ho : IsOrder le)
    {pairs : List (List α × α)} (h : pairs ≠ []) :
    ∃ best, leastEntry k le pairs = some best := by
  rw [leastEntry_eq]
  cases pairs with
  | nil => exact absurd rfl h
  | cons e rest =>
    simp only [List.map_cons, List.foldl_cons, better]
    obtain ⟨b, hb, _⟩ := foldl_better ho (rest.map fun e => k e.1 e.2) (k e.1 e.2)
    exact ⟨b, hb⟩

/-! ## The extensions of a round -/

variable [DecidableEq α]

theorem mem_extensions {items : List α} {held : List (List α)} {p : List α} {a : α} :
    (p, a) ∈ extensions items held ↔ p ∈ held ∧ a ∈ items ∧ a ∉ p := by
  simp only [extensions, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p', hp', a', ⟨ha', hnot⟩, heq⟩
    cases heq
    exact ⟨hp', ha', by simpa using hnot⟩
  · rintro ⟨hp, ha, hnot⟩
    exact ⟨p, hp, a, ⟨ha, by simpa using hnot⟩, rfl⟩

/-- No extension stands twice in the list. -/
theorem extensions_nodup {items : List α} {held : List (List α)} (hitems : items.Nodup)
    (hheld : held.Nodup) : (extensions items held).Nodup := by
  unfold extensions
  show List.Pairwise (· ≠ ·) _
  rw [List.pairwise_flatMap]
  constructor
  · intro p _
    rw [List.pairwise_map]
    exact (List.Pairwise.filter _ hitems).imp fun h heq => h (Prod.mk.inj heq).2
  · exact List.Pairwise.imp (fun {p q} hpq x hx y hy heq => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
      exact hpq (Prod.mk.inj heq).1) hheld

/-! ## Beginnings that are alike

The search may hold one beginning for all that have the same outline. What is
needed of the outlines for that is said by `Merges`, further down. -/

section alike

variable {μ : Type} [DecidableEq μ] {β : Type}

/-- What `unseen` takes is an item of the list whose outline was not seen. -/
theorem mem_unseen {outline : β → μ} : ∀ {l : List β} {seen : List μ} {x : β},
    x ∈ unseen outline seen l → x ∈ l ∧ outline x ∉ seen
  | [], _, _, h => by simp [unseen] at h
  | y :: rest, seen, x, h => by
    unfold unseen at h
    split at h
    · obtain ⟨h1, h2⟩ := mem_unseen h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rename_i hnot
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨List.mem_cons_self .., by simpa using hnot⟩
      · obtain ⟨h1, h2⟩ := mem_unseen h
        exact ⟨List.mem_cons_of_mem _ h1, fun hmem => h2 (List.mem_cons_of_mem _ hmem)⟩

/-- For every item of the list whose outline was not seen, `unseen` takes an
item with the same outline. -/
theorem exists_unseen {outline : β → μ} : ∀ {l : List β} {seen : List μ} {x : β},
    x ∈ l → outline x ∉ seen → ∃ y ∈ unseen outline seen l, outline y = outline x
  | [], _, _, hx, _ => by simp at hx
  | y :: rest, seen, x, hx, hnot => by
    unfold unseen
    by_cases hy : seen.contains (outline y) = true
    · simp only [hy, ↓reduceIte]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd (by simpa using hy) hnot
      · exact exists_unseen hx hnot
    · simp only [hy]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨x, List.mem_cons_self .., rfl⟩
      · by_cases hm : outline x = outline y
        · exact ⟨y, List.mem_cons_self .., hm.symm⟩
        · obtain ⟨z, hz, hmz⟩ := exists_unseen (seen := outline y :: seen) hx (by
            intro hmem
            rcases List.mem_cons.1 hmem with e | e
            · exact hm e
            · exact hnot e)
          exact ⟨z, List.mem_cons_of_mem _ hz, hmz⟩

/-- No two items that `unseen` takes have the same outline. -/
theorem unseen_pairwise {outline : β → μ} : ∀ (l : List β) (seen : List μ),
    (unseen outline seen l).Pairwise fun a b => outline a ≠ outline b
  | [], _ => by simp [unseen]
  | y :: rest, seen => by
    unfold unseen
    split
    · exact unseen_pairwise rest seen
    · refine List.Pairwise.cons ?_ (unseen_pairwise rest _)
      intro z hz hm
      exact (mem_unseen hz).2 (by rw [← hm]; exact List.mem_cons_self ..)

theorem unseen_cons_of_mem {outline : β → μ} {seen : List μ} {x : β} (rest : List β)
    (h : outline x ∈ seen) : unseen outline seen (x :: rest) = unseen outline seen rest := by
  simp [unseen, h]

theorem unseen_cons_of_not_mem {outline : β → μ} {seen : List μ} {x : β} (rest : List β)
    (h : outline x ∉ seen) :
    unseen outline seen (x :: rest) = x :: unseen outline (outline x :: seen) rest := by
  simp [unseen, h]

/-- `unseenWithin` gives what `unseen` gives, if that is not too much. -/
theorem unseenWithin_eq (limit : Nat) (outline : β → μ) :
    ∀ (l : List β) (seen : List μ) (taken : List β), taken.length ≤ limit →
      unseenWithin limit outline l seen taken =
        if taken.length + (unseen outline seen l).length ≤ limit
        then some (taken.reverse ++ unseen outline seen l) else none
  | [], seen, taken, h => by
    simp [unseenWithin, unseen, h]
  | x :: rest, seen, taken, h => by
    by_cases hx : outline x ∈ seen
    · rw [unseen_cons_of_mem rest hx]
      have : unseenWithin limit outline (x :: rest) seen taken
          = unseenWithin limit outline rest seen taken := by
        simp [unseenWithin, hx]
      rw [this]
      exact unseenWithin_eq limit outline rest seen taken h
    · rw [unseen_cons_of_not_mem rest hx]
      by_cases hlt : taken.length < limit
      · have : unseenWithin limit outline (x :: rest) seen taken
            = unseenWithin limit outline rest (outline x :: seen) (x :: taken) := by
          simp [unseenWithin, hx, hlt]
        rw [this, unseenWithin_eq limit outline rest (outline x :: seen) (x :: taken)
          (by simp only [List.length_cons]; omega)]
        simp only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        by_cases hc : taken.length + 1 + (unseen outline (outline x :: seen) rest).length ≤ limit
        · have hc' : taken.length + ((unseen outline (outline x :: seen) rest).length + 1)
              ≤ limit := by omega
          simp only [hc, hc', ↓reduceIte]
        · have hc' : ¬ taken.length + ((unseen outline (outline x :: seen) rest).length + 1)
              ≤ limit := by omega
          simp only [hc, hc', ↓reduceIte]
      · have : unseenWithin limit outline (x :: rest) seen taken = none := by
          simp [unseenWithin, hx, hlt]
        rw [this]
        have hc' : ¬ taken.length + (x :: unseen outline (outline x :: seen) rest).length
            ≤ limit := by
          simp only [List.length_cons]; omega
        simp only [hc', ↓reduceIte]

end alike

variable {μ : Type} [DecidableEq μ]

/-- Two beginnings count as the same for the search: with outlines, when they
have the same outline; without outlines, when they are equal. -/
def Same (outline : Option (List α → μ)) (p q : List α) : Prop :=
  match outline with
  | none => p = q
  | some f => f p = f q

omit [DecidableEq α] [DecidableEq μ] in
theorem Same.refl (outline : Option (List α → μ)) (p : List α) : Same outline p p := by
  cases outline <;> rfl

omit [DecidableEq α] [DecidableEq μ] in
theorem Same.symm {outline : Option (List α → μ)} {p q : List α} (h : Same outline p q) :
    Same outline q p := by
  cases outline with
  | none => exact Eq.symm h
  | some f => exact Eq.symm h

omit [DecidableEq α] [DecidableEq μ] in
theorem Same.trans {outline : Option (List α → μ)} {p q r : List α} (h₁ : Same outline p q)
    (h₂ : Same outline q r) : Same outline p r := by
  cases outline with
  | none => exact Eq.trans h₁ h₂
  | some f => exact Eq.trans h₁ h₂

omit [DecidableEq μ] in
/-- No beginning stands twice among the extensions that a round keeps. -/
theorem kept_extended_nodup (k : List α → α → κ) (le : κ → κ → Bool) {items : List α}
    {held : List (List α)} (hitems : items.Nodup) (hheld : held.Nodup) :
    ((kept k le items held).map extended).Nodup := by
  unfold kept
  split
  · exact List.nodup_nil
  · show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_map]
    exact (List.Pairwise.filter _ (extensions_nodup hitems hheld)).imp fun {e e'} hne heq => by
      have h := List.append_inj' heq rfl
      exact hne (Prod.ext h.1 (by simpa using h.2))

omit [DecidableEq α] in
/-- What `merged` gives is one of the extensions, as a beginning. -/
theorem mem_merged {outline : Option (List α → μ)} {es : List (List α × α)} {p' : List α}
    (h : p' ∈ merged outline es) : ∃ e ∈ es, p' = extended e := by
  cases outline with
  | none =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact ⟨e, he, rfl⟩
  | some f =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact ⟨e, (mem_unseen he).1, rfl⟩

omit [DecidableEq α] in
/-- Every extension has one that counts as the same among what `merged`
gives. -/
theorem exists_merged {outline : Option (List α → μ)} {es : List (List α × α)} {e : List α × α}
    (he : e ∈ es) : ∃ r ∈ merged outline es, Same outline r (extended e) := by
  cases outline with
  | none => exact ⟨extended e, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩
  | some f =>
    obtain ⟨y, hy, hm⟩ :=
      exists_unseen (outline := fun e => f (extended e)) (seen := []) he (by simp)
    exact ⟨extended y, List.mem_map.2 ⟨y, hy, rfl⟩, hm⟩

omit [DecidableEq α] in
/-- No two of the beginnings that `merged` gives count as the same. -/
theorem merged_pairwise {outline : Option (List α → μ)} {es : List (List α × α)}
    (hnd : (es.map extended).Nodup) :
    (merged outline es).Pairwise fun p q => ¬ Same outline p q := by
  cases outline with
  | none => exact hnd
  | some f =>
    show List.Pairwise _ ((unseen (fun e => f (extended e)) [] es).map extended)
    rw [List.pairwise_map]
    exact unseen_pairwise es []

omit [DecidableEq α] in
/-- `mergedWithin` gives what `merged` gives if those are no more than `limit`
beginnings, and `none` otherwise. -/
theorem mergedWithin_eq (limit : Nat) (outline : Option (List α → μ)) (es : List (List α × α)) :
    mergedWithin limit outline es =
      if (merged outline es).length ≤ limit then some (merged outline es) else none := by
  cases outline with
  | none => simp [mergedWithin, merged]
  | some f =>
    have general : (unseenWithin limit (fun e => f (extended e)) es [] []).map
          (fun taken => taken.map extended)
        = if (merged (some f) es).length ≤ limit then some (merged (some f) es) else none := by
      rw [unseenWithin_eq limit _ es [] [] (by simp)]
      simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append, merged,
        List.length_map]
      split <;> rfl
    cases es with
    | nil => exact general
    | cons e rest =>
      cases rest with
      | nil =>
        simp only [mergedWithin]
        simp [merged, unseen]
      | cons e' rest' => exact general

/-! ## One round keeps what was true -/

/-- What is true of the beginnings that the search holds after `j` rounds:
there is one; no two of them count as the same; each is a beginning of `j`
items; and each has the least key among all beginnings of `j` items, and every
beginning with that key counts as the same as one that is held. -/
structure Holds (k : List α → α → κ) (le : κ → κ → Bool) (outline : Option (List α → μ))
    (items : List α) (j : Nat) (held : List (List α)) : Prop where
  some : held ≠ []
  distinct : held.Pairwise fun p q => ¬ Same outline p q
  beginning : ∀ p ∈ held, IsBeginning items p ∧ p.length = j
  least : ∀ p ∈ held, ∀ q, IsBeginning items q → q.length = j →
    (keys k q = keys k p ∧ ∃ p' ∈ held, Same outline p' q) ∨ Before (Lt le) (keys k p) (keys k q)

omit [DecidableEq α] [DecidableEq μ] in
/-- No beginning is held twice. -/
theorem Holds.nodup {k : List α → α → κ} {le : κ → κ → Bool} {outline : Option (List α → μ)}
    {items : List α} {j : Nat} {held : List (List α)} (h : Holds k le outline items j held) :
    held.Nodup :=
  h.distinct.imp fun {p q} hns heq => hns (by subst heq; exact Same.refl outline p)

/-- What the outlines must do: two beginnings of the same length that count as
the same can be extended by the same items, the two extensions get the same
entry, and they count as the same again. -/
structure Merges (items : List α) (k : List α → α → κ) (outline : Option (List α → μ)) : Prop where
  step : ∀ p q a, IsBeginning items p → IsBeginning items q → p.length = q.length →
    Same outline p q → a ∈ items → a ∉ p →
    a ∉ q ∧ k q a = k p a ∧ Same outline (p ++ [a]) (q ++ [a])

omit [DecidableEq α] [DecidableEq μ] in
/-- Without outlines nothing is asked. -/
theorem Merges.none (items : List α) (k : List α → α → κ) :
    Merges items k (none : Option (List α → μ)) :=
  ⟨fun p q a _ _ _ h _ hnot => by
    have : p = q := h
    subst this
    exact ⟨hnot, rfl, rfl⟩⟩

omit [DecidableEq α] [DecidableEq μ] in
theorem Holds.start (k : List α → α → κ) (le : κ → κ → Bool) (outline : Option (List α → μ))
    (items : List α) : Holds k le outline items 0 [[]] := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro p hp
    have : p = [] := by simpa using hp
    subst this
    exact ⟨⟨List.nodup_nil, by simp⟩, rfl⟩
  · intro p hp q _ hq
    have hp' : p = [] := by simpa using hp
    have hq' : q = [] := List.length_eq_zero_iff.1 hq
    subst hp' hq'
    exact Or.inl ⟨rfl, [], by simp, Same.refl outline _⟩

theorem Holds.round {k : List α → α → κ} {le : κ → κ → Bool} (ho : IsOrder le)
    {outline : Option (List α → μ)} {items : List α} (hM : Merges items k outline)
    (hitems : items.Nodup) {j : Nat} {held : List (List α)} (hj : j < items.length)
    (h : Holds k le outline items j held) :
    Holds k le outline items (j + 1) (VeriMol.Search.round k le outline items held) := by
  -- there is something to extend, and some item to extend it by
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil held h.some
  obtain ⟨⟨hnd₀, hsub₀⟩, hlen₀⟩ := h.beginning p₀ hp₀
  have hfree : ∃ a, a ∈ items ∧ a ∉ p₀ := by
    apply Classical.byContradiction
    intro hno
    have hall : items ⊆ p₀ := by
      intro a ha
      apply Classical.byContradiction
      intro hnot
      exact hno ⟨a, ha, hnot⟩
    have := hitems.length_le_of_subset hall
    omega
  obtain ⟨a₀, ha₀, hnot₀⟩ := hfree
  have hext : (p₀, a₀) ∈ extensions items held := mem_extensions.2 ⟨hp₀, ha₀, hnot₀⟩
  have hne : extensions items held ≠ [] := List.ne_nil_of_mem hext
  obtain ⟨best, hbest⟩ := leastEntry_some_of_ne_nil k ho hne
  have hkeptdef : kept k le items held =
      (extensions items held).filter fun e => le (k e.1 e.2) best := by
    simp [kept, hbest]
  have hleast := leastEntry_le k ho hbest
  -- what it means to be kept
  have hkept : ∀ p a, p ∈ held → a ∈ items → a ∉ p → le (k p a) best = true →
      ∃ r ∈ VeriMol.Search.round k le outline items held, Same outline r (p ++ [a]) := by
    intro p a hp ha hnot hle
    have hmem : (p, a) ∈ kept k le items held := by
      rw [hkeptdef]
      exact List.mem_filter.2 ⟨mem_extensions.2 ⟨hp, ha, hnot⟩, hle⟩
    exact exists_merged hmem
  have hfrom : ∀ p', p' ∈ VeriMol.Search.round k le outline items held →
      ∃ p a, p' = p ++ [a] ∧ p ∈ held ∧ a ∈ items ∧ a ∉ p ∧ le (k p a) best = true := by
    intro p' hp'
    obtain ⟨⟨p, a⟩, hmem, rfl⟩ := mem_merged hp'
    rw [hkeptdef] at hmem
    obtain ⟨hmem, hle⟩ := List.mem_filter.1 hmem
    obtain ⟨hp, ha, hnot⟩ := mem_extensions.1 hmem
    exact ⟨p, a, rfl, hp, ha, hnot, hle⟩
  refine ⟨?_, merged_pairwise (kept_extended_nodup k le hitems h.nodup), ?_, ?_⟩
  · -- the extension with the least entry is kept
    obtain ⟨⟨p, a⟩, hmem, hka⟩ := leastEntry_mem k ho hbest
    obtain ⟨hp, ha, hnot⟩ := mem_extensions.1 hmem
    have hle : le (k p a) best = true := by
      simp only at hka
      rw [hka]
      rcases ho.total best best with h' | h' <;> exact h'
    obtain ⟨r, hr, _⟩ := hkept p a hp ha hnot hle
    exact List.ne_nil_of_mem hr
  · intro p' hp'
    obtain ⟨p, a, rfl, hp, ha, hnot, _⟩ := hfrom p' hp'
    obtain ⟨⟨hnd, hsub⟩, hlen⟩ := h.beginning p hp
    refine ⟨⟨?_, ?_⟩, by simp [hlen]⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro x hx y hy
      have : y = a := by simpa using hy
      subst this
      intro hxy
      subst hxy
      exact hnot hx
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsub x hx
      · have : x = a := by simpa using hx
        subst this
        exact ha
  · intro p' hp' q' hq' hlen'
    obtain ⟨p, a, rfl, hp, ha, hnot, hle⟩ := hfrom p' hp'
    -- q' is a beginning of length j, and one item more
    have hq'ne : q' ≠ [] := by
      intro hnil
      subst hnil
      simp at hlen'
    obtain ⟨q, b, rfl⟩ : ∃ q b, q' = q ++ [b] :=
      ⟨q'.dropLast, q'.getLast hq'ne, (List.dropLast_concat_getLast hq'ne).symm⟩
    obtain ⟨hndq', hsubq'⟩ := hq'
    rw [List.nodup_append] at hndq'
    obtain ⟨hndq, _, hdisj⟩ := hndq'
    have hbq : b ∉ q := fun hb => hdisj b hb b (by simp) rfl
    have hbitems : b ∈ items := hsubq' b (by simp)
    have hqbeg : IsBeginning items q := ⟨hndq, fun x hx => hsubq' x (List.mem_append_left _ hx)⟩
    have hqlen : q.length = j := by simpa using hlen'
    rw [keys_append, keys_append]
    rcases h.least p hp q hqbeg hqlen with ⟨hkeys, p₂, hp₂, hsame⟩ | hbefore
    · -- the same key so far, and `p₂`, which is held, counts as the same as `q`:
      -- the new entries decide
      obtain ⟨hbeg₂, hlen₂⟩ := h.beginning p₂ hp₂
      obtain ⟨hbp₂, hk, hsame'⟩ :=
        hM.step q p₂ b hqbeg hbeg₂ (by omega) hsame.symm hbitems hbq
      have hbestb : le best (k q b) = true := by
        rw [← hk]
        exact hleast (p₂, b) (mem_extensions.2 ⟨hp₂, hbitems, hbp₂⟩)
      have hab : le (k p a) (k q b) = true := ho.trans _ _ _ hle hbestb
      by_cases hba : le (k q b) (k p a) = true
      · left
        have heq : k q b = k p a := ho.antisymm _ _ hba hab
        refine ⟨by rw [hkeys, heq], ?_⟩
        obtain ⟨r, hr, hrs⟩ := hkept p₂ b hp₂ hbitems hbp₂
          (by rw [hk]; exact ho.trans _ _ _ hba hle)
        exact ⟨r, hr, hrs.trans hsame'.symm⟩
      · right
        rw [hkeys]
        exact Before.last _ (by simpa [Lt] using hba)
    · right
      exact hbefore.append_right _ _

/-! ## What the search ends with -/

/-- After every round, what the search holds is as `Holds` says. -/
theorem search_holds (k : List α → α → κ) {le : κ → κ → Bool} (ho : IsOrder le)
    {outline : Option (List α → μ)} {items : List α} (hM : Merges items k outline)
    (hitems : items.Nodup) :
    ∀ j, j ≤ items.length → Holds k le outline items j (search k le outline items j)
  | 0, _ => Holds.start k le outline items
  | j + 1, hj => (search_holds k ho hM hitems j (by omega)).round ho hM hitems (by omega)

/-- Where the search with a limit does not give up, it holds what the search
without a limit holds. -/
theorem searchWithin_eq (limit : Nat) (k : List α → α → κ) (le : κ → κ → Bool)
    (outline : Option (List α → μ)) (items : List α) :
    ∀ (j : Nat) (held : List (List α)),
      searchWithin limit k le outline items j = some held → held = search k le outline items j
  | 0, held, h => by
    simp only [searchWithin, Option.some.injEq] at h
    exact h.symm
  | j + 1, held, h => by
    simp only [searchWithin] at h
    cases hprev : searchWithin limit k le outline items j with
    | none => simp [hprev] at h
    | some prev =>
      rw [hprev] at h
      simp only [mergedWithin_eq] at h
      split at h
      · cases h
        rw [search, ← searchWithin_eq limit k le outline items j prev hprev]
        rfl
      · cases h

/-- After as many rounds as there are items, the search holds at least one
order. Each order it holds puts every item at one place, and its key is no
later than the key of any order of the items. -/
theorem search_least (k : List α → α → κ) {le : κ → κ → Bool} (ho : IsOrder le)
    {outline : Option (List α → μ)} {items : List α} (hM : Merges items k outline)
    (hitems : items.Nodup) :
    search k le outline items items.length ≠ [] ∧
    ∀ p ∈ search k le outline items items.length,
      (IsBeginning items p ∧ p.length = items.length) ∧
      ∀ q, IsBeginning items q → q.length = items.length →
        NoLater (Lt le) (keys k p) (keys k q) := by
  have h := search_holds k ho hM hitems items.length (Nat.le_refl _)
  refine ⟨h.some, fun p hp => ⟨h.beginning p hp, fun q hq hlen => ?_⟩⟩
  rcases h.least p hp q hq hlen with ⟨hkeys, _⟩ | hbefore
  · exact Or.inl hkeys.symm
  · exact Or.inr hbefore

/-! ## Two keys cannot each come before the other -/

omit [DecidableEq α] in
/-- The entry at one place of a key. -/
theorem getElem?_keysFrom (k : List α → α → κ) :
    ∀ (l done : List α) (j : Nat),
      (keysFrom k done l)[j]? = l[j]?.map fun a => k (done ++ l.take j) a
  | [], _, j => by simp [keysFrom]
  | a :: l, done, 0 => by simp [keysFrom]
  | a :: l, done, j + 1 => by
    simp [keysFrom, getElem?_keysFrom k l (done ++ [a]) j]

omit [DecidableEq α] in
theorem getElem?_keys (k : List α → α → κ) (l : List α) (j : Nat) :
    (keys k l)[j]? = l[j]?.map fun a => k (l.take j) a := by
  simpa [keys] using getElem?_keysFrom k l [] j

omit [DecidableEq α] in
theorem Before.asymm {lt : κ → κ → Prop} (irrefl : ∀ x, ¬ lt x x)
    (asymm : ∀ x y, lt x y → ¬ lt y x) {xs ys : List κ}
    (h₁ : Before lt xs ys) (h₂ : Before lt ys xs) : False := by
  obtain ⟨c, x, y, r₁, r₂, hx, hy, hlt⟩ := h₁
  obtain ⟨c', y', x', r₁', r₂', hy', hx', hlt'⟩ := h₂
  have ex : xs[c.length]? = some x := by simp [hx]
  have ey : ys[c.length]? = some y := by simp [hy]
  have ex' : xs[c'.length]? = some x' := by simp [hx']
  have ey' : ys[c'.length]? = some y' := by simp [hy']
  rcases Nat.lt_trichotomy c.length c'.length with hlt₀ | heq | hgt
  · have a : xs[c.length]? = c'[c.length]? := by rw [hx', List.getElem?_append_left hlt₀]
    have b : ys[c.length]? = c'[c.length]? := by rw [hy', List.getElem?_append_left hlt₀]
    have : x = y := by
      rw [ex] at a; rw [ey] at b
      exact Option.some.inj (a.trans b.symm)
    exact irrefl x (this ▸ hlt)
  · rw [heq] at ex ey
    have e1 : x = x' := Option.some.inj (ex.symm.trans ex')
    have e2 : y = y' := Option.some.inj (ey.symm.trans ey')
    exact asymm x y hlt (e1 ▸ e2 ▸ hlt')
  · have a : xs[c'.length]? = c[c'.length]? := by rw [hx, List.getElem?_append_left hgt]
    have b : ys[c'.length]? = c[c'.length]? := by rw [hy, List.getElem?_append_left hgt]
    have : x' = y' := by
      rw [ex'] at a; rw [ey'] at b
      exact Option.some.inj (a.trans b.symm)
    exact irrefl y' (this ▸ hlt')

omit [DecidableEq α] in
theorem Lt.irrefl {le : κ → κ → Bool} (ho : IsOrder le) (x : κ) : ¬ Lt le x x := by
  intro hx
  rcases ho.total x x with h | h <;> simp [Lt, h] at hx

omit [DecidableEq α] in
theorem Lt.asymm {le : κ → κ → Bool} (ho : IsOrder le) (x y : κ) : Lt le x y → ¬ Lt le y x := by
  intro hxy hyx
  rcases ho.total x y with h | h
  · simp [Lt, h] at hyx
  · simp [Lt, h] at hxy

/-! ## The same search under other names for the items

Two searches are linked when the items of the first can be renamed into the
items of the second, one to one, so that the entries agree. Then a renamed
beginning is a beginning, with the same key. -/

/-- `f` renames the items of the first search into those of the second, `g`
leads back, and the entries agree. -/
structure Renames (f g : α → α) (items₁ items₂ : List α) (k₁ k₂ : List α → α → κ) : Prop where
  forth : ∀ a ∈ items₁, f a ∈ items₂ ∧ g (f a) = a
  back : ∀ b ∈ items₂, g b ∈ items₁ ∧ f (g b) = b
  entry : ∀ p a, IsBeginning items₁ p → a ∈ items₁ → a ∉ p → k₂ (p.map f) (f a) = k₁ p a

omit [DecidableEq α] in
/-- A renamed beginning is a beginning. -/
theorem Renames.isBeginning {f g : α → α} {items₁ items₂ : List α} {k₁ k₂ : List α → α → κ}
    (h : Renames f g items₁ items₂ k₁ k₂) {p : List α} (hp : IsBeginning items₁ p) :
    IsBeginning items₂ (p.map f) := by
  obtain ⟨hnd, hsub⟩ := hp
  refine ⟨?_, ?_⟩
  · show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab heq => hab ?_) hnd
    rw [← (h.forth a (hsub a ha)).2, ← (h.forth b (hsub b hb)).2, heq]
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact (h.forth a (hsub a ha)).1

omit [DecidableEq α] in
/-- A renamed beginning has the same key. -/
theorem Renames.keys_map {f g : α → α} {items₁ items₂ : List α} {k₁ k₂ : List α → α → κ}
    (h : Renames f g items₁ items₂ k₁ k₂) :
    ∀ (n : Nat) (p : List α), p.length = n → IsBeginning items₁ p →
      keys k₂ (p.map f) = keys k₁ p
  | 0, p, hlen, _ => by
    have : p = [] := List.length_eq_zero_iff.1 hlen
    subst this
    rfl
  | n + 1, p, hlen, hp => by
    have hne : p ≠ [] := by
      intro hnil
      subst hnil
      simp at hlen
    obtain ⟨q, a, rfl⟩ : ∃ q a, p = q ++ [a] :=
      ⟨p.dropLast, p.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨hnd, hsub⟩ := hp
    rw [List.nodup_append] at hnd
    obtain ⟨hndq, _, hdisj⟩ := hnd
    have haq : a ∉ q := fun ha => hdisj a ha a (by simp) rfl
    have hq : IsBeginning items₁ q := ⟨hndq, fun x hx => hsub x (List.mem_append_left _ hx)⟩
    have ha : a ∈ items₁ := hsub a (by simp)
    rw [List.map_append, List.map_singleton, keys_append, keys_append,
      h.keys_map n q (by simpa using hlen) hq, h.entry q a hq ha haq]

omit [DecidableEq α] in
/-- The link can be read the other way round. -/
theorem Renames.symm {f g : α → α} {items₁ items₂ : List α} {k₁ k₂ : List α → α → κ}
    (h : Renames f g items₁ items₂ k₁ k₂) : Renames g f items₂ items₁ k₂ k₁ := by
  refine ⟨h.back, h.forth, ?_⟩
  intro q b hq hb hbq
  -- rename `q` and `b` into the first search, and use the link there
  have hq' : IsBeginning items₁ (q.map g) := by
    obtain ⟨hnd, hsub⟩ := hq
    refine ⟨?_, ?_⟩
    · show List.Pairwise (· ≠ ·) _
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy heq => hxy ?_) hnd
      rw [← (h.back x (hsub x hx)).2, ← (h.back y (hsub y hy)).2, heq]
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact (h.back x (hsub x hx)).1
  have hb' : g b ∈ items₁ := (h.back b hb).1
  have hbq' : g b ∉ q.map g := by
    intro hmem
    obtain ⟨x, hx, hgx⟩ := List.mem_map.1 hmem
    have : x = b := by
      rw [← (h.back x (hq.2 x hx)).2, ← (h.back b hb).2, hgx]
    exact hbq (this ▸ hx)
  have hentry := h.entry (q.map g) (g b) hq' hb' hbq'
  have hback : (q.map g).map f = q := by
    rw [List.map_map]
    have : List.map (f ∘ g) q = List.map id q :=
      List.map_inj_left.2 fun x hx => (h.back x (hq.2 x hx)).2
    rw [this, List.map_id]
  rw [hback, (h.back b hb).2] at hentry
  exact hentry.symm

/-! ## A tie-break for items that can be exchanged

For the tie-break the items are numbers. Some of them are twins: exchanging
two twins changes no entry of any key. So an order of the items has a copy
with the same key for every way of exchanging its twins. The tie-break makes
the search hold one of them: the one in which twins stand in the order of
their numbers.

What the search with the tie-break holds still has the least key among all
beginnings (`Holds.least_of_tieBreak`). -/

/-- Exchange `a` and `b`. -/
def swapOf (a b x : Nat) : Nat := if x = a then b else if x = b then a else x

/-- Whether a twin of `a` with a smaller number is not placed yet: 1 if so,
0 if not. -/
def waiting (T : Nat → Nat → Bool) (done : List Nat) (a : Nat) : Nat :=
  if (List.range a).any (fun b => T a b && !done.contains b) then 1 else 0

/-- The entry with the tie-break behind it. -/
def tieBreak (k : List Nat → Nat → κ) (T : Nat → Nat → Bool) (done : List Nat) (a : Nat) :
    κ × Nat :=
  (k done a, waiting T done a)

theorem lePair_isOrder [DecidableEq κ] {le : κ → κ → Bool} (ho : IsOrder le) :
    IsOrder (lePair le) where
  total := by
    intro x y
    unfold lePair
    by_cases h : x.1 = y.1
    · have h' : y.1 = x.1 := h.symm
      simp only [h, ↓reduceIte, decide_eq_true_eq]
      omega
    · have h' : ¬ y.1 = x.1 := fun e => h e.symm
      simp only [h, h', ↓reduceIte]
      exact ho.total _ _
  trans := by
    intro x y z hxy hyz
    unfold lePair at *
    by_cases h1 : x.1 = y.1
    · by_cases h2 : y.1 = z.1
      · have h3 : x.1 = z.1 := h1.trans h2
        simp only [h1, h2, ↓reduceIte, decide_eq_true_eq] at *
        omega
      · have h3 : ¬ x.1 = z.1 := fun e => h2 (h1.symm.trans e)
        simp only [h2, h3, ↓reduceIte] at *
        rw [h1]
        exact hyz
    · by_cases h2 : y.1 = z.1
      · have h3 : ¬ x.1 = z.1 := fun e => h1 (e.trans h2.symm)
        simp only [h1, h3, ↓reduceIte] at *
        rw [← h2]
        exact hxy
      · simp only [h1, h2, ↓reduceIte] at hxy hyz
        have hxz := ho.trans _ _ _ hxy hyz
        by_cases h3 : x.1 = z.1
        · exfalso
          rw [h3] at hxy
          exact h2 (ho.antisymm _ _ hyz hxy)
        · simp only [h3, ↓reduceIte]
          exact hxz
  antisymm := by
    intro x y hxy hyx
    unfold lePair at *
    by_cases h : x.1 = y.1
    · have h' : y.1 = x.1 := h.symm
      simp only [h, ↓reduceIte, decide_eq_true_eq] at hxy hyx
      have : x.2 = y.2 := by omega
      exact Prod.ext h this
    · have h' : ¬ y.1 = x.1 := fun e => h e.symm
      simp only [h, h', ↓reduceIte] at hxy hyx
      exact absurd (ho.antisymm _ _ hxy hyx) h

theorem lt_of_lt_pair [DecidableEq κ] {le : κ → κ → Bool} {x y : κ}
    (h : Lt (lePair le) (x, 0) (y, 0)) : Lt le x y := by
  unfold Lt lePair at h
  unfold Lt
  by_cases e : y = x
  · simp [e] at h
  · simpa [e] using h

theorem lt_pair_same [DecidableEq κ] (le : κ → κ → Bool) (x : κ) {n : Nat} (h : n ≠ 0) :
    Lt (lePair le) (x, 0) (x, n) := by
  simp only [Lt, lePair, ↓reduceIte, decide_eq_false_iff_not]
  omega

/-- A statement that holds for some number holds for a least one. -/
theorem exists_least (P : Nat → Prop) : ∀ n, P n → ∃ m, P m ∧ ∀ l, l < m → ¬ P l := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ l, l < n ∧ P l
    · obtain ⟨l, hl, hpl⟩ := h
      exact ih l hl hpl
    · exact ⟨n, hn, fun l hl hpl => h ⟨l, hl, hpl⟩⟩

theorem waiting_eq_zero_iff {T : Nat → Nat → Bool} {done : List Nat} {a : Nat} :
    waiting T done a = 0 ↔ ∀ b, b < a → T a b = true → b ∈ done := by
  simp [waiting]

theorem map_swapOf_of_not_mem {a b : Nat} : ∀ {l : List Nat}, a ∉ l → b ∉ l →
    l.map (swapOf a b) = l
  | [], _, _ => rfl
  | x :: l, ha, hb => by
    have hxa : x ≠ a := fun e => ha (by simp [e])
    have hxb : x ≠ b := fun e => hb (by simp [e])
    have ih := map_swapOf_of_not_mem (l := l) (fun h => ha (List.mem_cons_of_mem _ h))
      (fun h => hb (List.mem_cons_of_mem _ h))
    simp [swapOf, hxa, hxb, ih]

theorem swapOf_left (a b : Nat) : swapOf a b a = b := by simp [swapOf]

theorem split_at : ∀ {q : List Nat} {i a : Nat}, q[i]? = some a →
    q = q.take i ++ a :: q.drop (i + 1)
  | [], i, a, h => by simp at h
  | x :: q, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    simp [h]
  | x :: q, i + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    have := split_at h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [← this]

theorem keysFrom_append' (k : List Nat → Nat → κ) : ∀ (l₁ done l₂ : List Nat),
    keysFrom k done (l₁ ++ l₂) = keysFrom k done l₁ ++ keysFrom k (done ++ l₁) l₂
  | [], done, l₂ => by simp [keysFrom]
  | x :: l₁, done, l₂ => by
    simp [keysFrom, keysFrom_append' k l₁ (done ++ [x]) l₂]

theorem keys_append_cons (k : List Nat → Nat → κ) (u : List Nat) (a : Nat) (v : List Nat) :
    keys k (u ++ a :: v) = keys k u ++ k u a :: keysFrom k (u ++ [a]) v := by
  simp [keys, keysFrom_append', keysFrom]

/-- What makes `T` a relation between items that can be exchanged: it holds
both ways round and through a third item, and exchanging two twins leaves
every entry of every key as it is. -/
structure Twins (items : List Nat) (k : List Nat → Nat → κ) (T : Nat → Nat → Bool) : Prop where
  symm : ∀ a b, T a b = true → T b a = true
  trans : ∀ a b c, T a b = true → T b c = true → a ≠ c → T a c = true
  swap : ∀ a b, a ∈ items → T a b = true → Renames (swapOf a b) (swapOf a b) items items k k

/-- If a smaller twin of `a` is waiting, then the smallest of them has no
smaller twin waiting itself. -/
theorem Twins.exists_ready {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool}
    (hT : Twins items k T) {done : List Nat} {a : Nat} (h : waiting T done a ≠ 0) :
    ∃ b, b < a ∧ T a b = true ∧ b ∉ done ∧ waiting T done b = 0 := by
  have hex : ∃ b, b < a ∧ T a b = true ∧ b ∉ done := by
    apply Classical.byContradiction
    intro hno
    apply h
    rw [waiting_eq_zero_iff]
    intro b hb hTb
    apply Classical.byContradiction
    intro hnot
    exact hno ⟨b, hb, hTb, hnot⟩
  obtain ⟨b₀, hb₀⟩ := hex
  obtain ⟨b, ⟨hb, hTb, hnb⟩, hmin⟩ :=
    exists_least (fun y => y < a ∧ T a y = true ∧ y ∉ done) b₀ hb₀
  refine ⟨b, hb, hTb, hnb, ?_⟩
  rw [waiting_eq_zero_iff]
  intro y hy hTy
  apply Classical.byContradiction
  intro hny
  exact hmin y hy ⟨by omega, hT.trans a b y hTb hTy (by omega), hny⟩

/-- Every item was placed when no twin of it with a smaller number was
waiting. -/
def Respects (T : Nat → Nat → Bool) (p : List Nat) : Prop :=
  ∀ i a, p[i]? = some a → waiting T (p.take i) a = 0

/-- Two lists are the same but for twins: at every place the same item, or two
twins. -/
def SameButTwins (T : Nat → Nat → Bool) (q q' : List Nat) : Prop :=
  q.length = q'.length ∧
    ∀ (l a a' : Nat), q[l]? = some a → q'[l]? = some a' → a = a' ∨ T a a' = true

theorem SameButTwins.refl (T : Nat → Nat → Bool) (q : List Nat) : SameButTwins T q q :=
  ⟨rfl, fun l a a' h1 h2 => by rw [h1] at h2; exact Or.inl (Option.some.inj h2)⟩

theorem Twins.sameButTwins_trans {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool}
    (hT : Twins items k T) {q₁ q₂ q₃ : List Nat} (h₁ : SameButTwins T q₁ q₂)
    (h₂ : SameButTwins T q₂ q₃) : SameButTwins T q₁ q₃ := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  intro l a c ha hc
  have hl : l < q₂.length := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rw [← h₁.1]
    exact this
  have hb : q₂[l]? = some q₂[l] := List.getElem?_eq_getElem hl
  rcases h₁.2 l a _ ha hb with e₁ | t₁
  · rw [← e₁] at hb
    exact h₂.2 l a c hb hc
  · rcases h₂.2 l _ c hb hc with e₂ | t₂
    · rw [← e₂]
      exact Or.inr t₁
    · by_cases hac : a = c
      · exact Or.inl hac
      · exact Or.inr (hT.trans _ _ _ t₁ t₂ hac)

/-- Exchanging two twins in a list gives a list that is the same but for
twins. -/
theorem Twins.sameButTwins_map_swapOf {items : List Nat} {k : List Nat → Nat → κ}
    {T : Nat → Nat → Bool} (hT : Twins items k T) {a b : Nat} (hab : T a b = true)
    (q : List Nat) : SameButTwins T q (q.map (swapOf a b)) := by
  refine ⟨by simp, ?_⟩
  intro l x x' hx hx'
  rw [List.getElem?_map, hx] at hx'
  simp only [Option.map_some, Option.some.injEq] at hx'
  subst hx'
  unfold swapOf
  by_cases h1 : x = a
  · subst h1
    simp [hab]
  · by_cases h2 : x = b
    · subst h2
      simp [h1, hT.symm _ _ hab]
    · simp [h1, h2]

omit [DecidableEq μ] in
/-- A beginning that the search with the tie-break holds respects the twins:
otherwise exchanging an item with its smallest waiting twin would give a
beginning with a smaller key. -/
theorem Holds.respects [DecidableEq κ] {le : κ → κ → Bool} (ho : IsOrder le) {items : List Nat}
    {k : List Nat → Nat → κ} {T : Nat → Nat → Bool} (hT : Twins items k T)
    {outline : Option (List Nat → μ)} {j : Nat} {held : List (List Nat)}
    (h : Holds (tieBreak k T) (lePair le) outline items j held) :
    ∀ p ∈ held, Respects T p := by
  intro p hp i a hia
  apply Classical.byContradiction
  intro hw
  obtain ⟨b, hba, hTab, hbu, hready⟩ := hT.exists_ready hw
  obtain ⟨hbeg, hlen⟩ := h.beginning p hp
  have hbeg' : IsBeginning items (p.map (swapOf a b)) :=
    (hT.swap a b (hbeg.2 a (List.mem_of_getElem? hia)) hTab).isBeginning hbeg
  have hsplit := split_at hia
  generalize p.take i = u at hsplit hw hready hbu
  generalize p.drop (i + 1) = v at hsplit
  subst hsplit
  obtain ⟨hnd, hsub⟩ := hbeg
  have ha_items : a ∈ items := hsub a (by simp)
  have hnd' := hnd
  rw [List.nodup_append] at hnd'
  obtain ⟨hndu, _, hdisj⟩ := hnd'
  have hau : a ∉ u := fun hmem => hdisj a hmem a (by simp) rfl
  have hR := hT.swap a b ha_items hTab
  have hubeg : IsBeginning items u := ⟨hndu, fun x hx => hsub x (List.mem_append_left _ hx)⟩
  have hk : k u b = k u a := by
    have := hR.entry u a hubeg ha_items hau
    rw [map_swapOf_of_not_mem hau hbu, swapOf_left] at this
    exact this
  have hp' : (u ++ a :: v).map (swapOf a b) = u ++ b :: v.map (swapOf a b) := by
    rw [List.map_append, List.map_cons, map_swapOf_of_not_mem hau hbu, swapOf_left]
  have hB : Before (Lt (lePair le)) (keys (tieBreak k T) ((u ++ a :: v).map (swapOf a b)))
      (keys (tieBreak k T) (u ++ a :: v)) := by
    rw [hp']
    refine ⟨_, _, _, _, _, keys_append_cons _ u b _, keys_append_cons _ u a _, ?_⟩
    show Lt (lePair le) (k u b, waiting T u b) (k u a, waiting T u a)
    rw [hk, hready]
    exact lt_pair_same le _ hw
  have ho' := lePair_isOrder ho
  rcases h.least _ hp _ hbeg' (by simpa using hlen) with ⟨heq, _⟩ | hB2
  · rw [heq] at hB
    exact Before.asymm (Lt.irrefl ho') (Lt.asymm ho') hB hB
  · exact Before.asymm (Lt.irrefl ho') (Lt.asymm ho') hB hB2

/-- Every beginning can be brought into a form that respects the twins, by
exchanging twins: the key stays, and the new list is the same but for twins.
The proof goes through the places from the front. Where an item has a smaller
twin waiting, it is exchanged with the smallest one that waits. -/
theorem Twins.normal {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool}
    (hT : Twins items k T) :
    ∀ (d : Nat) (q : List Nat) (i : Nat), i + d = q.length → IsBeginning items q →
      (∀ l a, l < i → q[l]? = some a → waiting T (q.take l) a = 0) →
      ∃ q', IsBeginning items q' ∧ q'.length = q.length ∧ keys k q' = keys k q ∧
        Respects T q' ∧ SameButTwins T q q'
  | 0, q, i, hi, hq, hfine => by
    refine ⟨q, hq, rfl, rfl, ?_, SameButTwins.refl T q⟩
    intro l a hla
    have : l < q.length := (List.getElem?_eq_some_iff.1 hla).1
    exact hfine l a (by omega) hla
  | d + 1, q, i, hi, hq, hfine => by
    have hilt : i < q.length := by omega
    obtain ⟨a, hia⟩ : ∃ a, q[i]? = some a := ⟨q[i], List.getElem?_eq_getElem hilt⟩
    by_cases hw : waiting T (q.take i) a = 0
    · refine hT.normal d q (i + 1) (by omega) hq ?_
      intro l x hl hlx
      by_cases hli : l = i
      · subst hli
        rw [hia] at hlx
        cases hlx
        exact hw
      · exact hfine l x (by omega) hlx
    · obtain ⟨b, hba, hTab, hbu, hready⟩ := hT.exists_ready hw
      have ha_items : a ∈ items := hq.2 a (List.mem_of_getElem? hia)
      have hR := hT.swap a b ha_items hTab
      have hq₁ : IsBeginning items (q.map (swapOf a b)) := hR.isBeginning hq
      have hkeys : keys k (q.map (swapOf a b)) = keys k q := hR.keys_map _ q rfl hq
      have halike : SameButTwins T q (q.map (swapOf a b)) := hT.sameButTwins_map_swapOf hTab q
      -- the first `i + 1` places of the new list are fine
      have hfine₁ : ∀ l x, l < i + 1 → (q.map (swapOf a b))[l]? = some x →
          waiting T ((q.map (swapOf a b)).take l) x = 0 := by
        have hsplit := split_at hia
        have hlen_u : (q.take i).length = i := by
          rw [List.length_take]
          omega
        generalize q.take i = u at hsplit hw hready hbu hlen_u
        generalize q.drop (i + 1) = v at hsplit
        subst hsplit
        have hnd := hq.1
        rw [List.nodup_append] at hnd
        obtain ⟨_, _, hdisj⟩ := hnd
        have hau : a ∉ u := fun hmem => hdisj a hmem a (by simp) rfl
        have hmap : (u ++ a :: v).map (swapOf a b) = u ++ b :: v.map (swapOf a b) := by
          rw [List.map_append, List.map_cons, map_swapOf_of_not_mem hau hbu, swapOf_left]
        rw [hmap]
        intro l x hl hlx
        by_cases hli : l = i
        · subst hli
          rw [List.getElem?_append_right (by omega)] at hlx
          simp only [hlen_u, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hlx
          subst hlx
          rw [← hlen_u, List.take_left']
          · exact hready
          · rfl
        · have hl' : l < u.length := by omega
          rw [List.getElem?_append_left hl'] at hlx
          rw [List.take_append_of_le_length (by omega)]
          have := hfine l x (by omega) (by rw [List.getElem?_append_left hl']; exact hlx)
          rw [List.take_append_of_le_length (by omega)] at this
          exact this
      obtain ⟨q', hq', hlen', hkeys', hresp, halike'⟩ :=
        hT.normal d (q.map (swapOf a b)) (i + 1) (by simp; omega) hq₁ hfine₁
      exact ⟨q', hq', by simpa using hlen', hkeys'.trans hkeys, hresp,
        hT.sameButTwins_trans halike halike'⟩

/-- The key with the tie-break of a list that respects the twins is its key,
with a 0 behind every entry. -/
theorem keys_tieBreak_of_respects (k : List Nat → Nat → κ) {T : Nat → Nat → Bool} {p : List Nat}
    (h : Respects T p) : keys (tieBreak k T) p = (keys k p).map fun x => (x, 0) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_keys, List.getElem?_map, getElem?_keys]
  cases hpi : p[i]? with
  | none => rfl
  | some a => simp [tieBreak, h i a hpi]

/-- With a 0 behind every entry, the pairs come in the order of the entries. -/
theorem Before.of_pairs [DecidableEq κ] {le : κ → κ → Bool} {xs ys : List κ}
    (h : Before (Lt (lePair le)) (xs.map fun x => (x, 0)) (ys.map fun y => (y, 0))) :
    Before (Lt le) xs ys := by
  obtain ⟨c, x, y, r₁, r₂, h₁, h₂, hlt⟩ := h
  obtain ⟨c₁, t₁, rfl, hc₁, ht₁⟩ := List.map_eq_append_iff.1 h₁
  obtain ⟨x₀, r₁', rfl, hx₀, _⟩ := List.map_eq_cons_iff.1 ht₁
  obtain ⟨c₂, t₂, rfl, hc₂, ht₂⟩ := List.map_eq_append_iff.1 h₂
  obtain ⟨y₀, r₂', rfl, hy₀, _⟩ := List.map_eq_cons_iff.1 ht₂
  have hc : c₁ = c₂ := by
    have : c₁.map (fun x => (x, 0)) = c₂.map (fun x => (x, 0)) := hc₁.trans hc₂.symm
    exact (List.map_inj_right (fun a b hab => by simpa using hab)).1 this
  subst hc
  subst hx₀
  subst hy₀
  exact ⟨c₁, x₀, y₀, r₁', r₂', rfl, rfl, lt_of_lt_pair hlt⟩

omit [DecidableEq μ] in
/-- What the search with the tie-break holds has the least key, without the
tie-break, among all beginnings of its length. -/
theorem Holds.least_of_tieBreak [DecidableEq κ] {le : κ → κ → Bool} (ho : IsOrder le)
    {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool} (hT : Twins items k T)
    {outline : Option (List Nat → μ)} {j : Nat} {held : List (List Nat)}
    (h : Holds (tieBreak k T) (lePair le) outline items j held) :
    ∀ p ∈ held, ∀ q, IsBeginning items q → q.length = j →
      NoLater (Lt le) (keys k p) (keys k q) := by
  intro p hp q hq hqlen
  have hrp := h.respects ho hT p hp
  obtain ⟨q', hq', hlen', hkeys', hrq', _⟩ :=
    hT.normal q.length q 0 (by simp) hq (by intro l a hl; omega)
  rcases h.least p hp q' hq' (by omega) with ⟨heq, _⟩ | hB
  · left
    rw [keys_tieBreak_of_respects k hrq', keys_tieBreak_of_respects k hrp] at heq
    have := (List.map_inj_right (fun a b hab => by simpa using hab)).1 heq
    rw [← hkeys', this]
  · right
    rw [keys_tieBreak_of_respects k hrq', keys_tieBreak_of_respects k hrp] at hB
    rw [← hkeys']
    exact Before.of_pairs hB

/-- Counting: if every entry of one list without repeats is related to an
entry of another list, and no two of them to the same one, the first list is
no longer than the second. -/
theorem length_le_of_related {α β : Type} [Inhabited β] (R : α → β → Prop) {l₁ : List α}
    {l₂ : List β} (hnd : l₁.Nodup) (hex : ∀ a ∈ l₁, ∃ b, b ∈ l₂ ∧ R a b)
    (hinj : ∀ a ∈ l₁, ∀ a' ∈ l₁, ∀ b, R a b → R a' b → a = a') : l₁.length ≤ l₂.length := by
  classical
  let pick : α → β := fun a => if h : ∃ b, b ∈ l₂ ∧ R a b then Classical.choose h else default
  have hpick : ∀ a ∈ l₁, pick a ∈ l₂ ∧ R a (pick a) := by
    intro a ha
    have h := hex a ha
    simp only [pick, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hnd' : (l₁.map pick).Nodup := by
    show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a a'} ha ha' hne heq => hne ?_) hnd
    exact hinj a ha a' ha' (pick a) (hpick a ha).2 (heq ▸ (hpick a' ha').2)
  have hsub : l₁.map pick ⊆ l₂ := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact (hpick a ha).1
  simpa using hnd'.length_le_of_subset hsub

theorem SameButTwins.symm {T : Nat → Nat → Bool} (hsymm : ∀ a b, T a b = true → T b a = true)
    {q q' : List Nat} (h : SameButTwins T q q') : SameButTwins T q' q :=
  ⟨h.1.symm, fun l a a' h1 h2 => by
    rcases h.2 l a' a h2 h1 with e | t
    · exact Or.inl e.symm
    · exact Or.inr (hsymm _ _ t)⟩

/-- Two lists without repeats that respect the twins and are the same but for
twins are equal. -/
theorem Respects.eq_of_sameButTwins {T : Nat → Nat → Bool}
    (hsymm : ∀ a b, T a b = true → T b a = true)
    {p p' : List Nat} (hnd : p.Nodup) (hnd' : p'.Nodup) (h : Respects T p) (h' : Respects T p')
    (ha : SameButTwins T p p') : p = p' := by
  have key : ∀ i, p.take i = p'.take i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [List.take_add_one, List.take_add_one, ih]
      congr 1
      by_cases hi : i < p.length
      · have hi' : i < p'.length := by rw [← ha.1]; exact hi
        have hp : p[i]? = some p[i] := List.getElem?_eq_getElem hi
        have hp' : p'[i]? = some p'[i] := List.getElem?_eq_getElem hi'
        rw [hp, hp']
        congr 2
        -- an item cannot stand at place `i` and before it
        have twice : ∀ {l : List Nat} {x : Nat}, l.Nodup → l[i]? = some x → x ∉ l.take i := by
          intro l x hl hx hmem
          have hs := split_at hx
          rw [hs, List.nodup_append] at hl
          exact hl.2.2 x hmem x (by simp) rfl
        rcases ha.2 i _ _ hp hp' with e | t
        · exact e
        · rcases Nat.lt_trichotomy p[i] p'[i] with hlt | heq | hgt
          · -- the smaller one must stand before place `i` in `p'`, where it also stands in `p`
            have := (waiting_eq_zero_iff.1 (h' i _ hp')) _ hlt (hsymm _ _ t)
            rw [← ih] at this
            exact absurd this (twice hnd hp)
          · exact heq
          · have := (waiting_eq_zero_iff.1 (h i _ hp)) _ hgt t
            rw [ih] at this
            exact absurd this (twice hnd' hp')
      · have hi' : ¬ i < p'.length := by rw [← ha.1]; exact hi
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have := key p.length
  rw [List.take_length, ha.1, List.take_length] at this
  exact this

/-! ## The same search under other names, with the tie-break

The tie-break places twins in the order of their numbers, so it depends on
the names of the items. Still, the searches with the tie-break of two
renamings of the same items are the same search under other names: the items
can be renamed so that twins keep the order of their numbers
(`Twins.exists_renaming`). Then both hold as many beginnings after every
round, also when beginnings that count as the same are merged
(`Renames.searchWithin_isSome`). So whether the search gives up does not
depend on how the items are named. -/

omit [DecidableEq α] in
/-- A beginning with one item more, which is not in it, is a beginning. -/
theorem IsBeginning.concat {items p : List α} {a : α} (hp : IsBeginning items p) (ha : a ∈ items)
    (hnot : a ∉ p) : IsBeginning items (p ++ [a]) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, by simp, ?_⟩
    intro x hx y hy
    have : y = a := by simpa using hy
    subst this
    intro hxy
    subst hxy
    exact hnot hx
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hp.2 x hx
    · have : x = a := by simpa using hx
      subst this
      exact ha

omit [DecidableEq α] in
/-- Renaming a beginning and renaming it back gives the beginning. -/
theorem Renames.map_map {f g : α → α} {items₁ items₂ : List α} {k₁ k₂ : List α → α → κ}
    (h : Renames f g items₁ items₂ k₁ k₂) {p : List α} (hp : IsBeginning items₁ p) :
    (p.map f).map g = p := by
  rw [List.map_map]
  have : List.map (g ∘ f) p = List.map id p :=
    List.map_inj_left.2 fun x hx => (h.forth x (hp.2 x hx)).2
  rw [this, List.map_id]

/-- Two beginnings that are the same but for twins have the same key. -/
theorem Twins.keys_eq_of_sameButTwins {items : List Nat} {k : List Nat → Nat → κ}
    {T : Nat → Nat → Bool} (hT : Twins items k T) {q q' : List Nat} (hq : IsBeginning items q)
    (hq' : IsBeginning items q') (h : SameButTwins T q q') : keys k q = keys k q' := by
  obtain ⟨n, hn, _, hkeys, hresp, halike⟩ :=
    hT.normal q.length q 0 (by simp) hq (by intro l a hl; omega)
  obtain ⟨n', hn', _, hkeys', hresp', halike'⟩ :=
    hT.normal q'.length q' 0 (by simp) hq' (by intro l a hl; omega)
  have hmid : SameButTwins T n n' :=
    hT.sameButTwins_trans (hT.sameButTwins_trans (halike.symm hT.symm) h) halike'
  have heq : n = n' := Respects.eq_of_sameButTwins hT.symm hn.1 hn'.1 hresp hresp' hmid
  rw [← hkeys, ← hkeys', heq]

/-- Equal, or twins. -/
def Near (T : Nat → Nat → Bool) (x y : Nat) : Prop := x = y ∨ T x y = true

theorem Twins.near_symm {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool}
    (hT : Twins items k T) {x y : Nat} (h : Near T x y) : Near T y x := by
  rcases h with e | t
  · exact Or.inl e.symm
  · exact Or.inr (hT.symm _ _ t)

theorem Twins.near_trans {items : List Nat} {k : List Nat → Nat → κ} {T : Nat → Nat → Bool}
    (hT : Twins items k T) {x y z : Nat} (h₁ : Near T x y) (h₂ : Near T y z) : Near T x z := by
  rcases h₁ with e₁ | t₁
  · rw [e₁]
    exact h₂
  · rcases h₂ with e₂ | t₂
    · rw [← e₂]
      exact Or.inr t₁
    · by_cases e : x = z
      · exact Or.inl e
      · exact Or.inr (hT.trans _ _ _ t₁ t₂ e)

theorem Near.of_ne {T : Nat → Nat → Bool} {x y : Nat} (h : Near T x y) (hne : x ≠ y) :
    T x y = true := by
  rcases h with e | t
  · exact absurd e hne
  · exact t

theorem waiting_eq_zero_or_one (T : Nat → Nat → Bool) (done : List Nat) (a : Nat) :
    waiting T done a = 0 ∨ waiting T done a = 1 := by
  unfold waiting
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Two tie-breaks are equal when they are 0 together. -/
theorem waiting_congr {T T' : Nat → Nat → Bool} {done done' : List Nat} {a a' : Nat}
    (h : waiting T done a = 0 ↔ waiting T' done' a' = 0) :
    waiting T done a = waiting T' done' a' := by
  rcases waiting_eq_zero_or_one T done a with h₁ | h₁ <;>
    rcases waiting_eq_zero_or_one T' done' a' with h₂ | h₂
  · rw [h₁, h₂]
  · have := h.1 h₁
    omega
  · have := h.2 h₂
    omega
  · rw [h₁, h₂]

/-- A list without repeats of `n` numbers below `n` holds every number below
`n`. -/
theorem mem_of_nodup_below {n : Nat} {s : List Nat} (hnd : s.Nodup)
    (hsub : ∀ a ∈ s, a ∈ List.range n) (hlen : s.length = n) {b : Nat} (hb : b < n) : b ∈ s := by
  apply Classical.byContradiction
  intro hnot
  have hsub' : s ⊆ (List.range n).erase b := by
    intro a ha
    have hne : a ≠ b := fun e => hnot (e ▸ ha)
    exact (List.mem_erase_of_ne hne).2 (hsub a ha)
  have := hnd.length_le_of_subset hsub'
  rw [List.length_erase_of_mem (List.mem_range.2 hb), List.length_range, hlen] at this
  omega

/-- The items of two searches are the numbers below `n`, the second search is
the first under other names (`f`), and the twins of the first are the twins of
the second. Then the items can also be renamed so that twins keep the order
of their numbers. With such a renaming the entries with the tie-break agree
as well: the two searches with the tie-break are the same search under other
names. -/
theorem Twins.exists_renaming {n : Nat} {k₁ k₂ : List Nat → Nat → κ} {T₁ T₂ : Nat → Nat → Bool}
    {f g : Nat → Nat} (hT₂ : Twins (List.range n) k₂ T₂)
    (hR : Renames f g (List.range n) (List.range n) k₁ k₂)
    (hTf : ∀ a b, a < n → b < n → T₂ (f a) (f b) = T₁ a b) :
    ∃ F G : Nat → Nat, Renames F G (List.range n) (List.range n) k₁ k₂ ∧
      Renames F G (List.range n) (List.range n) (tieBreak k₁ T₁) (tieBreak k₂ T₂) := by
  -- the numbers 0, 1, 2, ... under their new names, and that order with its twins put right
  have hrange : IsBeginning (List.range n) (List.range n) := ⟨List.nodup_range, fun a ha => ha⟩
  have hr : IsBeginning (List.range n) ((List.range n).map f) := hR.isBeginning hrange
  obtain ⟨s, hs, hslen, _, hsresp, hsalike⟩ :=
    hT₂.normal ((List.range n).map f).length ((List.range n).map f) 0 (by simp) hr
      (by intro l a hl; omega)
  have hslen' : s.length = n := by simpa using hslen
  -- `F a` is the item at place `a` of that order
  obtain ⟨F, hF⟩ : ∃ F : Nat → Nat, ∀ a, a < n → s[a]? = some (F a) :=
    ⟨fun a => s[a]?.getD 0, fun a ha => by
      have hlt : a < s.length := by omega
      simp [List.getElem?_eq_getElem hlt]⟩
  have hFmem : ∀ a, a < n → F a ∈ s := fun a ha => List.mem_of_getElem? (hF a ha)
  have hFlt : ∀ a, a < n → F a < n := fun a ha => List.mem_range.1 (hs.2 _ (hFmem a ha))
  have hGF : ∀ a, a < n → s.idxOf (F a) = a := by
    intro a ha
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 (hF a ha)
    rw [← e]
    exact hs.1.idxOf_getElem a h
  have hFG : ∀ b, b < n → s.idxOf b < n ∧ F (s.idxOf b) = b := by
    intro b hb
    have hmem : b ∈ s := mem_of_nodup_below hs.1 hs.2 hslen' hb
    have hlt : s.idxOf b < s.length := List.idxOf_lt_length_iff.2 hmem
    refine ⟨by omega, ?_⟩
    have h1 := hF (s.idxOf b) (by omega)
    rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt] at h1
    exact (Option.some.inj h1).symm
  have hFinj : ∀ a b, a < n → b < n → F a = F b → a = b := by
    intro a b ha hb e
    have h1 := hGF a ha
    have h2 := hGF b hb
    rw [e] at h1
    omega
  have hnear : ∀ a, a < n → Near T₂ (f a) (F a) := by
    intro a ha
    exact hsalike.2 a (f a) (F a) (by simp [List.getElem?_range ha]) (hF a ha)
  -- twins of the first search are renamed into twins of the second
  have htwins : ∀ a b, a < n → b < n → a ≠ b → T₂ (F a) (F b) = T₁ a b := by
    intro a b ha hb hab
    rw [← hTf a b ha hb]
    have hFne : F a ≠ F b := fun e => hab (hFinj a b ha hb e)
    have hfne : f a ≠ f b := fun e => hab (by
      rw [← (hR.forth a (List.mem_range.2 ha)).2, e, (hR.forth b (List.mem_range.2 hb)).2])
    apply Bool.eq_iff_iff.2
    constructor
    · intro h
      exact (hT₂.near_trans (hnear a ha)
        (hT₂.near_trans (Or.inr h) (hT₂.near_symm (hnear b hb)))).of_ne hfne
    · intro h
      exact (hT₂.near_trans (hT₂.near_symm (hnear a ha))
        (hT₂.near_trans (Or.inr h) (hnear b hb))).of_ne hFne
  -- and they keep the order of their numbers
  have hmono : ∀ a b, a < b → b < n → T₁ a b = true → F a < F b := by
    intro a b hab hb ht
    have ha : a < n := by omega
    have hne : F a ≠ F b := fun e => by
      have := hFinj a b ha hb e
      omega
    apply Classical.byContradiction
    intro hnot
    have hlt : F b < F a := by omega
    have h2 : T₂ (F a) (F b) = true := by
      rw [htwins a b ha hb (by omega)]
      exact ht
    -- `F a` stands at place `a` of an order that respects the twins: its smaller twin `F b`
    -- stands before place `a`. But it stands at place `b`.
    have hin := (waiting_eq_zero_iff.1 (hsresp a (F a) (hF a ha))) (F b) hlt h2
    obtain ⟨l, hl, hle⟩ := List.mem_take_iff_getElem.1 hin
    have hl' : l < s.length := by omega
    have h3 := hs.1.idxOf_getElem l hl'
    rw [hle, hGF b hb] at h3
    omega
  -- so `F` renames the items, as `f` does
  have hforth : ∀ a ∈ List.range n, F a ∈ List.range n ∧ s.idxOf (F a) = a := fun a ha =>
    ⟨List.mem_range.2 (hFlt a (List.mem_range.1 ha)), hGF a (List.mem_range.1 ha)⟩
  have hback : ∀ b ∈ List.range n, s.idxOf b ∈ List.range n ∧ F (s.idxOf b) = b := fun b hb =>
    ⟨List.mem_range.2 (hFG b (List.mem_range.1 hb)).1, (hFG b (List.mem_range.1 hb)).2⟩
  have hU : Renames F (fun b => s.idxOf b) (List.range n) (List.range n)
      (fun _ _ => ()) (fun _ _ => ()) := ⟨hforth, hback, fun _ _ _ _ _ => rfl⟩
  have hentry : ∀ p a, IsBeginning (List.range n) p → a ∈ List.range n → a ∉ p →
      k₂ (p.map F) (F a) = k₁ p a := by
    intro p a hp ha hnot
    rw [← hR.entry p a hp ha hnot]
    have hpa : IsBeginning (List.range n) (p ++ [a]) := hp.concat ha hnot
    have h₁ : IsBeginning (List.range n) ((p ++ [a]).map f) := hR.isBeginning hpa
    have h₂ : IsBeginning (List.range n) ((p ++ [a]).map F) := hU.isBeginning hpa
    have hal : SameButTwins T₂ ((p ++ [a]).map f) ((p ++ [a]).map F) := by
      refine ⟨by simp, ?_⟩
      intro l x x' hx hx'
      rw [List.getElem?_map] at hx hx'
      cases hl : (p ++ [a])[l]? with
      | none =>
        rw [hl] at hx
        simp at hx
      | some y =>
        rw [hl] at hx hx'
        simp only [Option.map_some, Option.some.injEq] at hx hx'
        subst hx hx'
        exact hnear y (List.mem_range.1 (hpa.2 y (List.mem_of_getElem? hl)))
    have hkeys := hT₂.keys_eq_of_sameButTwins h₁ h₂ hal
    rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton, keys_append,
      keys_append] at hkeys
    have := (List.append_inj' hkeys rfl).2
    simpa using this.symm
  refine ⟨F, fun b => s.idxOf b, ⟨hforth, hback, hentry⟩, hforth, hback, ?_⟩
  intro p a hp ha hnot
  have ha' := List.mem_range.1 ha
  show (k₂ (p.map F) (F a), waiting T₂ (p.map F) (F a)) = (k₁ p a, waiting T₁ p a)
  rw [hentry p a hp ha hnot]
  congr 1
  apply waiting_congr
  rw [waiting_eq_zero_iff, waiting_eq_zero_iff]
  constructor
  · intro H b hb ht
    have hb' : b < n := by omega
    have ht₂ : T₂ (F a) (F b) = true := by
      rw [htwins a b ha' hb' (by omega)]
      exact ht
    have ht' : T₁ b a = true := by
      rw [← htwins b a hb' ha' (by omega)]
      exact hT₂.symm _ _ ht₂
    have hmem := H (F b) (hmono b a hb ha' ht') ht₂
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
    have : x = b := hFinj x b (List.mem_range.1 (hp.2 x hx)) hb' hxe
    exact this ▸ hx
  · intro H b' hb' ht
    have hFa := hFlt a ha'
    obtain ⟨hGlt, hFGb⟩ := hFG b' (by omega)
    generalize s.idxOf b' = b at hGlt hFGb
    subst hFGb
    have hne : a ≠ b := by
      intro e
      subst e
      omega
    have ht₁ : T₁ a b = true := by
      rw [← htwins a b ha' hGlt hne]
      exact ht
    have hlt : b < a := by
      apply Classical.byContradiction
      intro hnot'
      have := hmono a b (by omega) hGlt ht₁
      omega
    exact List.mem_map.2 ⟨b, H b hlt ht₁, rfl⟩

/-- In a list in which no two entries are related, two entries that are
related are the same entry. -/
theorem eq_of_pairwise_not {β : Type} {R : β → β → Prop} (hsymm : ∀ a b, R a b → R b a) :
    ∀ {l : List β}, l.Pairwise (fun a b => ¬ R a b) → ∀ {a b : β}, a ∈ l → b ∈ l → R a b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, hr => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd hr (h.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hsymm _ _ hr) (h.1 a ha')
      · exact eq_of_pairwise_not hsymm h.2 ha' hb' hr

omit [DecidableEq α] [DecidableEq μ] in
/-- Two beginnings that the search holds and that count as the same are the
same beginning. -/
theorem Holds.eq_of_same {k : List α → α → κ} {le : κ → κ → Bool} {outline : Option (List α → μ)}
    {items : List α} {j : Nat} {held : List (List α)} (h : Holds k le outline items j held)
    {p p' : List α} (hp : p ∈ held) (hp' : p' ∈ held) (hs : Same outline p p') : p = p' :=
  eq_of_pairwise_not (fun _ _ => Same.symm) h.distinct hp hp' hs

omit [DecidableEq α] [DecidableEq μ] in
/-- Two searches that are the same search under other names, after the same
number of rounds. If two beginnings count as the same for the first whenever
their renamed forms count as the same for the second, the first holds no more
beginnings than the second: every beginning that it holds counts, renamed, as
the same as one that the second holds, and two different ones never as the
same as one beginning of the second. -/
theorem Holds.length_le_of_renames {k₁ k₂ : List α → α → κ} {le : κ → κ → Bool} (ho : IsOrder le)
    {outline₁ outline₂ : Option (List α → μ)} {items₁ items₂ : List α} {f g : α → α}
    (hR : Renames f g items₁ items₂ k₁ k₂)
    (houtline : ∀ p p', IsBeginning items₁ p → IsBeginning items₁ p' → p.length = p'.length →
      Same outline₂ (p.map f) (p'.map f) → Same outline₁ p p')
    {j : Nat} {held₁ held₂ : List (List α)} (h₁ : Holds k₁ le outline₁ items₁ j held₁)
    (h₂ : Holds k₂ le outline₂ items₂ j held₂) : held₁.length ≤ held₂.length := by
  apply length_le_of_related (fun p q => Same outline₂ q (p.map f)) h₁.nodup
  · intro p hp
    obtain ⟨hbeg, hlen⟩ := h₁.beginning p hp
    have hbeg₂ : IsBeginning items₂ (p.map f) := hR.isBeginning hbeg
    obtain ⟨p₂, hp₂⟩ := List.exists_mem_of_ne_nil _ h₂.some
    rcases h₂.least p₂ hp₂ (p.map f) hbeg₂ (by simpa using hlen) with ⟨_, q, hq, hsame⟩ | hB
    · exact ⟨q, hq, hsame⟩
    · exfalso
      -- `p` has the least key of the first search, also against `p₂` under its old names
      obtain ⟨hbeg_p₂, hlen_p₂⟩ := h₂.beginning p₂ hp₂
      have hback : IsBeginning items₁ (p₂.map g) := hR.symm.isBeginning hbeg_p₂
      rw [hR.keys_map _ p rfl hbeg, ← hR.symm.keys_map _ p₂ rfl hbeg_p₂] at hB
      rcases h₁.least p hp (p₂.map g) hback (by simpa using hlen_p₂) with ⟨heq, _⟩ | hB'
      · rw [heq] at hB
        exact Before.asymm (Lt.irrefl ho) (Lt.asymm ho) hB hB
      · exact Before.asymm (Lt.irrefl ho) (Lt.asymm ho) hB hB'
  · intro p hp p' hp' q hq hq'
    obtain ⟨hbeg, hlen⟩ := h₁.beginning p hp
    obtain ⟨hbeg', hlen'⟩ := h₁.beginning p' hp'
    exact h₁.eq_of_same hp hp' (houtline p p' hbeg hbeg' (by omega) (hq.symm.trans hq'))

/-- Whether the search gives up is the same for two searches that are the
same search under other names, when the outlines of the one are the outlines of
the other. -/
theorem Renames.searchWithin_isSome {k₁ k₂ : List α → α → κ} {le : κ → κ → Bool} (ho : IsOrder le)
    {outline₁ outline₂ : Option (List α → μ)} {items₁ items₂ : List α} {f g : α → α}
    (hR : Renames f g items₁ items₂ k₁ k₂)
    (hM₁ : Merges items₁ k₁ outline₁) (hM₂ : Merges items₂ k₂ outline₂)
    (houtline₁ : ∀ p p', IsBeginning items₁ p → IsBeginning items₁ p' → p.length = p'.length →
      Same outline₂ (p.map f) (p'.map f) → Same outline₁ p p')
    (houtline₂ : ∀ q q', IsBeginning items₂ q → IsBeginning items₂ q' → q.length = q'.length →
      Same outline₁ (q.map g) (q'.map g) → Same outline₂ q q')
    (hitems₁ : items₁.Nodup) (hitems₂ : items₂.Nodup) (hlen : items₁.length = items₂.length)
    (limit : Nat) :
    ∀ j, j ≤ items₁.length →
      (searchWithin limit k₁ le outline₁ items₁ j).isSome
        = (searchWithin limit k₂ le outline₂ items₂ j).isSome
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := Renames.searchWithin_isSome ho hR hM₁ hM₂ houtline₁ houtline₂ hitems₁ hitems₂ hlen
      limit j (by omega)
    simp only [searchWithin]
    cases h₁ : searchWithin limit k₁ le outline₁ items₁ j with
    | none =>
      rw [h₁] at ih
      cases h₂ : searchWithin limit k₂ le outline₂ items₂ j with
      | none => rfl
      | some held₂ => rw [h₂] at ih; cases ih
    | some held₁ =>
      rw [h₁] at ih
      cases h₂ : searchWithin limit k₂ le outline₂ items₂ j with
      | none => rw [h₂] at ih; cases ih
      | some held₂ =>
        have e₁ := searchWithin_eq limit _ _ _ items₁ j held₁ h₁
        have e₂ := searchWithin_eq limit _ _ _ items₂ j held₂ h₂
        have H₁ := search_holds k₁ ho hM₁ hitems₁ (j + 1) hj
        have H₂ := search_holds k₂ ho hM₂ hitems₂ (j + 1) (by omega)
        have r₁ : merged outline₁ (kept k₁ le items₁ held₁)
            = search k₁ le outline₁ items₁ (j + 1) := by
          rw [e₁]
          rfl
        have r₂ : merged outline₂ (kept k₂ le items₂ held₂)
            = search k₂ le outline₂ items₂ (j + 1) := by
          rw [e₂]
          rfl
        have hl : (merged outline₁ (kept k₁ le items₁ held₁)).length
            = (merged outline₂ (kept k₂ le items₂ held₂)).length := by
          rw [r₁, r₂]
          exact Nat.le_antisymm (H₁.length_le_of_renames ho hR houtline₁ H₂)
            (H₂.length_le_of_renames ho hR.symm houtline₂ H₁)
        simp only [mergedWithin_eq, hl]
        split <;> rfl

/-! ## Entries that agree on the items -/

omit [DecidableEq μ] in
/-- A round keeps the same extensions for two ways of making the entries that
agree on the items. -/
theorem kept_congr {k k' : List α → α → κ} (le : κ → κ → Bool) (items : List α)
    (h : ∀ p a, a ∈ items → k p a = k' p a) (held : List (List α)) :
    kept k le items held = kept k' le items held := by
  have hmem : ∀ e ∈ extensions items held, k e.1 e.2 = k' e.1 e.2 := by
    intro e he
    exact h e.1 e.2 (mem_extensions.1 he).2.1
  have hleast : leastEntry k le (extensions items held)
      = leastEntry k' le (extensions items held) := by
    rw [leastEntry_eq, leastEntry_eq, List.map_congr_left hmem]
  unfold kept
  rw [hleast]
  cases leastEntry k' le (extensions items held) with
  | none => rfl
  | some best =>
    simp only
    apply List.filter_congr
    intro e he
    rw [hmem e he]

/-- So the search with a limit does the same for them. -/
theorem searchWithin_congr {k k' : List α → α → κ} (le : κ → κ → Bool)
    (outline : Option (List α → μ)) (items : List α)
    (h : ∀ p a, a ∈ items → k p a = k' p a) (limit : Nat) :
    ∀ j, searchWithin limit k le outline items j = searchWithin limit k' le outline items j
  | 0 => rfl
  | j + 1 => by
    simp only [searchWithin, searchWithin_congr le outline items h limit j]
    cases searchWithin limit k' le outline items j with
    | none => rfl
    | some held => simp only [kept_congr le items h held]

end Search
end VeriMol
