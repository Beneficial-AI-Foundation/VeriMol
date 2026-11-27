import VeriMol.Core.Read
import VeriMol.Proofs.FluoroGroup
import VeriMol.Proofs.Sound

/-!
# Known compounds: the two definitions held against known answers

A proof cannot show that a definition says what was meant. So `Mol.Sound`
and the rule `Mol.NoFluoroGroup` are held against six compounds whose
answers are known. Each theorem below says for one SMILES: the reader reads
it, its `Mol` is sound, and the largest perfluorinated group of the `Mol`
has exactly so many carbon atoms. "Exactly `k`" is said in two parts: there
is a group of at least `k`, and none of `k + 1` or more.

Where the numbers come from: the wording behind the rule (Buck and others,
2011; `VeriMol/Proofs/Predicates/FluoroGroup.lean` has the reference) counts
carboxylic acids "with 7 or more perfluorinated carbons" as long-chain, and
PFOA, C7F15COOH, is the smallest of them; the paper sets PFHxS, C6F13SO3H,
beside PFHxA, C5F11COOH. The two isomers of PFOA follow from its formula for
a perfluoroalkyl group, which takes branched groups in.

Each proof is `decide +kernel`: Lean's kernel runs the reader on the SMILES,
and then the two checkers, which are proven right (theorems 46 and 48 of
CLAIMS.md). That a `Mol` has no group of eight or more carbon atoms is a
statement about every set of its atoms; the kernel settles it by running a
search of which it is proven that it leaves no atom out.

These are statements about single SMILES. A statement about one SMILES says
nothing about another way of writing the same compound. They have no line
in the ledger (CLAIMS.md, "Known compounds"). A further compound is one
more theorem of this form.
-/

namespace VeriMol

/-- The SMILES is read as a `Mol`, and that `Mol` has the property `P`. A
SMILES that the reader does not read has no property. -/
def SmilesHas (smiles : String) (P : Mol → Prop) : Prop :=
  ∃ m, read smiles.toList = .ok m ∧ P m

/-- Whether a SMILES has a property can be worked out when the property can:
the reader is run on the SMILES, and the property is asked of the `Mol` that
it gives. -/
instance (smiles : String) (P : Mol → Prop) [DecidablePred P] : Decidable (SmilesHas smiles P) :=
  match answer : read smiles.toList with
  | .ok m =>
    if has : P m then isTrue ⟨m, answer, has⟩
    else isFalse fun ⟨_, reads, has'⟩ => by
      rw [answer] at reads
      cases reads
      exact has has'
  | .error _ => isFalse fun ⟨_, reads, _⟩ => by
      rw [answer] at reads
      cases reads

/-- Ibuprofen: sound, and without any perfluorinated group. -/
theorem ibuprofen_noFluoroGroup :
    SmilesHas "CC(C)Cc1ccc(cc1)C(C)C(=O)O"
      (fun m => m.Sound ∧ m.NoFluoroGroup 1) := by
  decide +kernel

/-- PFOA, perfluorooctanoic acid: sound, and its largest perfluorinated
group has exactly seven carbon atoms: its chain without the acid group. -/
theorem pfoa_largestGroup :
    SmilesHas "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F"
      (fun m => m.Sound ∧ m.HasFluoroGroup 7 ∧ m.NoFluoroGroup 8) := by
  decide +kernel

/-- PFHxS, perfluorohexanesulfonic acid: sound, and exactly six. -/
theorem pfhxs_largestGroup :
    SmilesHas "OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F"
      (fun m => m.Sound ∧ m.HasFluoroGroup 6 ∧ m.NoFluoroGroup 7) := by
  decide +kernel

/-- PFHxA, perfluorohexanoic acid: sound, and exactly five. It has six carbon
atoms as PFHxS has, and one of them belongs to the acid group. -/
theorem pfhxa_largestGroup :
    SmilesHas "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F"
      (fun m => m.Sound ∧ m.HasFluoroGroup 5 ∧ m.NoFluoroGroup 6) := by
  decide +kernel

/-- An isomer of PFOA with a branch, perfluoro-6-methylheptanoic acid: sound,
and exactly seven, although no chain in it has more than six fluorinated
carbon atoms. The rule is about groups, and not about chains. -/
theorem isoPFOA_largestGroup :
    SmilesHas "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(C(F)(F)F)C(F)(F)F"
      (fun m => m.Sound ∧ m.HasFluoroGroup 7 ∧ m.NoFluoroGroup 8) := by
  decide +kernel

/-- An isomer of PFOA whose branch point carries no fluorine,
perfluoro-5,5-dimethylhexanoic acid: sound, and exactly seven. The carbon
atom at the branch is a branch carbon atom: its three –CF3 hold it, and it
joins them to the chain. -/
theorem tertButylPFOA_largestGroup :
    SmilesHas "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F"
      (fun m => m.Sound ∧ m.HasFluoroGroup 7 ∧ m.NoFluoroGroup 8) := by
  decide +kernel

end VeriMol
