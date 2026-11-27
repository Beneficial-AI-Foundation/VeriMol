/-!
# A search for the least order

Some items are to be put in an order. Every order has a key: one entry for
every place. The entry of a place depends on the items before it and on the
item at it. This file finds an order whose key is the least, when keys are
compared entry by entry from the front.

The search fills the places one after the other. It holds beginnings whose
key so far is the least. A beginning with a larger key can never become an
order with the least key, so nothing is lost. With a limit, the search gives
up as soon as a round would leave more beginnings than the limit.

Two beginnings can be alike: whatever is put behind the one can be put behind
the other, and gives the same entries. Then one of them is enough. The search
may be given a function that takes an outline of a beginning (`outline`): of
the beginnings with the same outline it holds the first one only. Without
such a function it holds every beginning with the least key. What an outline
must say, so that nothing is lost, is stated with the proofs (`Merges` in
`VeriMol/Proofs/Search.lean`).

The entries may carry a tie-break (`lePair`, at the end of this file).

Nothing here knows what a molecule is. `VeriMol/Core/Chosen.lean` uses the
search for the atoms of a `Mol` (SPEC.md, section 3.2).

The program runs `searchWithin`. `search` is the same search without a limit.
`search`, its parts `round`, `merged` and `unseen`, and `keys` are there for
the theorems, which say with them what `searchWithin` finds.
-/

namespace VeriMol
namespace Search

variable {α κ μ : Type}

/-! Throughout this file, `α` is the type of the items, `κ` of the entries and
`μ` of the outlines. `k done a` is the entry of the item `a` when the items
`done` stand before it, `le` compares two entries, and `held` are the
beginnings that the search holds. An extension is a beginning together with
an item that is not in it: the pair `(p, a)` stands for `p` with `a` behind
it. -/

/-! ## Keys -/

/-- The key of an order, given the items that stand in front of it. -/
def keysFrom (k : List α → α → κ) (done : List α) : List α → List κ
  | [] => []
  | a :: rest => k done a :: keysFrom k (done ++ [a]) rest

/-- The key of an order: one entry for every place. The entry of a place depends
on the items before it and on the item at it. -/
def keys (k : List α → α → κ) (order : List α) : List κ :=
  keysFrom k [] order

/-! ## One round -/

variable [DecidableEq α]

/-- Every beginning that the search holds, extended by every item that is not
in it. -/
def extensions (items : List α) (held : List (List α)) : List (List α × α) :=
  held.flatMap fun p => (items.filter fun a => !p.contains a).map fun a => (p, a)

/-- The least entry among the extensions `pairs`. The entries are worked out
one at a time and not kept. -/
def leastEntry (k : List α → α → κ) (le : κ → κ → Bool) (pairs : List (List α × α)) :
    Option κ :=
  pairs.foldl
    (fun best e =>
      match best with
      | none => some (k e.1 e.2)
      | some y => if le y (k e.1 e.2) then some y else some (k e.1 e.2))
    none

/-- The extensions with the least entry: what a round keeps, each still as a
beginning and the item that extends it. -/
def kept (k : List α → α → κ) (le : κ → κ → Bool) (items : List α) (held : List (List α)) :
    List (List α × α) :=
  match leastEntry k le (extensions items held) with
  | none => []
  | some best => (extensions items held).filter fun e => le (k e.1 e.2) best

/-- An extension as a beginning of its own. -/
def extended (e : List α × α) : List α :=
  e.1 ++ [e.2]

/-! ## Beginnings that are alike -/

variable [DecidableEq μ]

/-- Of the items of a list, the first of every group with the same outline.
An item whose outline is among `seen` is left out. -/
def unseen {β : Type} (outline : β → μ) : List μ → List β → List β
  | _, [] => []
  | seen, x :: rest =>
    if seen.contains (outline x) then unseen outline seen rest
    else x :: unseen outline (outline x :: seen) rest

/-- The same as `unseen`, with a limit: `none` as soon as more than `limit`
items would be taken. The list is gone through once, from its first item on,
and what is taken is counted on the way. `taken` holds what is taken so far,
the last one first. -/
def unseenWithin {β : Type} (limit : Nat) (outline : β → μ) :
    List β → List μ → List β → Option (List β)
  | [], _, taken => some taken.reverse
  | x :: rest, seen, taken =>
    if seen.contains (outline x) then unseenWithin limit outline rest seen taken
    else if taken.length < limit then
      unseenWithin limit outline rest (outline x :: seen) (x :: taken)
    else none

/-- What a round keeps, the extensions `pairs`, as beginnings. With outlines,
of the beginnings with the same outline only the first. -/
def merged (outline : Option (List α → μ)) (pairs : List (List α × α)) : List (List α) :=
  match outline with
  | none => pairs.map extended
  | some f => (unseen (fun e => f (extended e)) [] pairs).map extended

/-- The same with a limit: `none` if these are more than `limit` beginnings.
Without outlines the extensions are counted first, and the beginnings are
made only if they are few enough. With outlines they are counted while those
with a new outline are picked out. Either way no more than `limit` beginnings
are ever kept: where the search gives up, the extensions can be very many,
and each beginning would be a list of its own. Where a round keeps one
extension, no outline is worked out. -/
def mergedWithin (limit : Nat) (outline : Option (List α → μ)) (pairs : List (List α × α)) :
    Option (List (List α)) :=
  match outline with
  | none => if pairs.length ≤ limit then some (pairs.map extended) else none
  | some f =>
    match pairs with
    | [e] => if 1 ≤ limit then some [extended e] else none
    | several =>
      (unseenWithin limit (fun e => f (extended e)) several [] []).map fun taken =>
        taken.map extended

/-! ## The search -/

/-- One round of the search: every beginning is extended by one item, and the
extensions with the least entry are kept. Each becomes a beginning of its own.
With outlines, of the beginnings with the same outline only the first is
kept. -/
def round (k : List α → α → κ) (le : κ → κ → Bool) (outline : Option (List α → μ))
    (items : List α) (held : List (List α)) : List (List α) :=
  merged outline (kept k le items held)

/-- The search: `rounds` rounds, starting from the empty beginning. -/
def search (k : List α → α → κ) (le : κ → κ → Bool) (outline : Option (List α → μ))
    (items : List α) : Nat → List (List α)
  | 0 => [[]]
  | rounds + 1 => round k le outline items (search k le outline items rounds)

/-- The search with a limit: it gives up, with `none`, as soon as a round would
leave more than `limit` beginnings. -/
def searchWithin (limit : Nat) (k : List α → α → κ) (le : κ → κ → Bool)
    (outline : Option (List α → μ)) (items : List α) : Nat → Option (List (List α))
  | 0 => some [[]]
  | rounds + 1 =>
    match searchWithin limit k le outline items rounds with
    | none => none
    | some held => mergedWithin limit outline (kept k le items held)

/-! ## A tie-break -/

omit [DecidableEq α] [DecidableEq μ] in
/-- The search may be given entries with a number behind them: the entry
decides, and where two entries are equal, the smaller number comes first. -/
def lePair [DecidableEq κ] (le : κ → κ → Bool) (x y : κ × Nat) : Bool :=
  if x.1 = y.1 then decide (x.2 ≤ y.2) else le x.1 y.1

end Search
end VeriMol
