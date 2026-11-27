import VeriMol.Core.FluoroGroup
import VeriMol.Core.Read
import VeriMol.Core.Sound

/-!
# The filter (SPEC.md, section 16)

The filter stands between a proposal for a molecule and whoever is to act on
it. A proposal comes as a SMILES text. The filter hands on a `Mol`, the very
object that the reader gave for the text, and it does so only if the `Mol` is
sound and a rule holds for it. Anything else it refuses, with the reason.

It asks three questions, in this order:

1. Is the text read? If not, the reason is the problem that the reader found.
2. Is the `Mol` sound (`VeriMol/Core/Sound.lean`)? This is asked once, before
   any rule. If not, the reason is the first one that the checker finds.
3. Does the checker of the rule say yes? If not, the reason is the one that
   goes with the rule.

`VeriMol/Proofs/Filter.lean` proves what this gives: the filter hands on a `Mol`
exactly when the text is read as that `Mol`, the `Mol` is sound, and the rule
holds for it.
-/

namespace VeriMol

/-- The filter, for any rule. `allows` is the checker of the rule: it says yes
or no for a `Mol`. `refusal` gives the reason that goes with a no.

Several rules together are one rule again: its checker says yes when each of
theirs does. -/
def filter (allows : Mol → Bool) (refusal : Mol → List Char) (text : List Char) :
    Except (List Char) Mol :=
  match read text with
  | .error problem => .error problem.text
  | .ok mol =>
    match mol.soundProblem with
    | some reason => .error reason
    | none => if allows mol then .ok mol else .error (refusal mol)

/-- The filter with the rule `perfluoro`: no perfluorinated group of `n` or
more carbon atoms (`VeriMol/Core/FluoroGroup.lean`). A refusal by the rule
names the size of the largest group. -/
def filterPerfluoro (n : Nat) (text : List Char) : Except (List Char) Mol :=
  filter (fun mol => mol.hasNoFluoroGroup n)
    (fun mol => Message.fluoroGroup mol.largestFluoroGroup n) text

end VeriMol
