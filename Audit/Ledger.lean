/-!
# The ledger: the theorems this project claims

One line per statement of the numbered theorems of `CLAIMS.md`, each a theorem
in Lean: its name, its fingerprint, and whether it is proven or still open. The
tables under "Proven" in `CLAIMS.md` say in plain words what each of them says.
A row there, which `CLAIMS.md` numbers and calls a theorem, can stand for
several lines here. The lines stand in the order of the rows, and the
comments in the list give the numbers of the rows.

The six theorems about known compounds, in `VeriMol/Proofs/Compounds.lean`,
have no line here: `CLAIMS.md`, "Known compounds", says what that means.

The fingerprint is a number that Lean computes from two things:

* the statement of the theorem, and
* the definitions that give the statement its meaning: every type, and every
  definition that produces a statement or a type (such as "is well formed"),
  of Core and Proofs that the statement relies on, together with whatever
  they are defined with, and the helper that Lean generates for a `match` in
  the statement (`Audit.givesMeaning` in `Audit.lean` has the exact rule).

If either changes, the number changes, unless the change was made in order to
keep the number. The fingerprint does not cover the functions the theorem is
about (such as the reader): those may change freely, and the theorem must then
still be proven.

The build fails whenever a line here disagrees with the files under
`VeriMol/Proofs/`: the theorem was deleted or renamed, its statement or one of
those definitions changed, or its status is not the recorded one. So every
such event shows up as a changed line in this file, and
`git diff Audit/Ledger.lean` is the place to review them. Every build prints,
for each theorem, the definitions that its fingerprint covers and that
somebody wrote; a helper that Lean generates, such as the one of a `match`, is
covered and not listed.

A line is added, changed or removed only with the author's approval (rule 9).
Proven helper lemmas do not need a line. A theorem that contains `sorry` does.

To add a theorem, write its line with fingerprint 0 and run `lake build`: the
error message shows the real fingerprint.
-/

namespace Audit

/-- Whether a theorem is proven, or stated but still containing `sorry`. -/
inductive Status where
  | proven
  | stillOpen
  deriving DecidableEq

/-- One line of the ledger. -/
structure Entry where
  name : Lean.Name
  fingerprint : UInt64
  status : Status

def ledger : List Entry := [
  -- The program (theorems 1 to 5)
  ⟨`VeriMol.run_succeeds_or_reports_error, 8709657316596974025, .proven⟩,
  ⟨`VeriMol.run_read, 16237290473024440099, .proven⟩,
  ⟨`VeriMol.Mol.printed_injective, 4828216362648658072, .proven⟩,
  ⟨`VeriMol.run_eq_iff, 696492136957898101, .proven⟩,
  ⟨`VeriMol.read_of_run, 2318377100695712035, .proven⟩,
  ⟨`VeriMol.run_of_read_error, 348093535723041624, .proven⟩,
  ⟨`VeriMol.run_usage, 1776942214050565305, .proven⟩,
  ⟨`VeriMol.run_word_of_read_error, 7918798502306123904, .proven⟩,
  ⟨`VeriMol.run_rewrite, 2661132405416190704, .proven⟩,
  ⟨`VeriMol.run_plain, 15312399645415506523, .proven⟩,
  ⟨`VeriMol.run_canonical, 18287156911793485873, .proven⟩,
  -- The reader (theorems 6 to 10)
  ⟨`VeriMol.Element.ofSymbol?_symbol, 2332838883026629126, .proven⟩,
  ⟨`VeriMol.cut_spell, 11259751033730735333, .proven⟩,
  ⟨`VeriMol.read_wellFormed, 479500194833907660, .proven⟩,
  ⟨`VeriMol.read_atoms, 1364157211769518387, .proven⟩,
  ⟨`VeriMol.read_no_refusal, 5743857248419092838, .proven⟩,
  -- Reading undoes writing (theorems 11 to 16)
  ⟨`VeriMol.read_write, 1719498206827764186, .proven⟩,
  ⟨`VeriMol.read_writePlain, 12672130402832051817, .proven⟩,
  ⟨`VeriMol.run_rewrite_same_mol, 2852342678656836848, .proven⟩,
  ⟨`VeriMol.run_rewrite_again, 4719945735595656231, .proven⟩,
  ⟨`VeriMol.write_injective, 7892640352675886765, .proven⟩,
  ⟨`VeriMol.run_rewrite_eq_iff, 13358332741474506676, .proven⟩,
  -- When the writer gives a text (theorems 17 to 19)
  ⟨`VeriMol.Spelling.write_isOk_iff, 18291633011730188773, .proven⟩,
  ⟨`VeriMol.Spelling.write_of_read, 17781718729498226211, .proven⟩,
  ⟨`VeriMol.run_rewrite_of_read, 8884926860713325864, .proven⟩,
  ⟨`VeriMol.Spelling.write_isOk_iff_ringNumbers, 1663132784976319700, .proven⟩,
  ⟨`VeriMol.Spelling.write_tooManyRingNumbers_iff, 13464318136137717212, .proven⟩,
  ⟨`VeriMol.Spelling.write_tooManyRingNumbers_sound, 10791539626148474435, .proven⟩,
  ⟨`VeriMol.run_rewrite_tooManyRingNumbers_iff, 9153594023164535808, .proven⟩,
  ⟨`VeriMol.writePlain_isOk_iff_ringNumbers, 6065966272993460455, .proven⟩,
  ⟨`VeriMol.writePlain_tooManyRingNumbers_iff, 12406541486777023761, .proven⟩,
  ⟨`VeriMol.run_plain_tooManyRingNumbers_iff, 5644851282013965781, .proven⟩,
  -- The same molecule, numbered differently (theorems 20 to 22)
  ⟨`VeriMol.Mol.Renumbered.refl, 12089704946753044126, .proven⟩,
  ⟨`VeriMol.Mol.Renumbered.symm, 16241103565769163630, .proven⟩,
  ⟨`VeriMol.Mol.Renumbered.trans, 9719501303878829484, .proven⟩,
  ⟨`VeriMol.Mol.renumbered_iff_arrange, 4734519078727988576, .proven⟩,
  ⟨`VeriMol.Mol.eq_of_renumberedBy_id, 5389060148238562288, .proven⟩,
  ⟨`VeriMol.Mol.eq_of_sameFacts, 6386469465168107549, .proven⟩,
  -- The chosen form (theorems 23 to 28)
  ⟨`VeriMol.Mol.renumbered_chosenForm, 15291750470137679336, .proven⟩,
  ⟨`VeriMol.Mol.chosenForm_wellFormed, 5469287803444480240, .proven⟩,
  ⟨`VeriMol.Mol.chosenForm_least, 3459550509178717436, .proven⟩,
  ⟨`VeriMol.Mol.eq_of_key_eq, 14742901304962439179, .proven⟩,
  ⟨`VeriMol.Mol.chosenForm_eq_of_renumbered, 12985760787668725408, .proven⟩,
  ⟨`VeriMol.Mol.renumbered_iff_chosenForm_eq, 6133535794110718260, .proven⟩,
  ⟨`VeriMol.Mol.chosenForm_chosenForm, 6068623431816293360, .proven⟩,
  -- The command `canonical` (theorems 29 to 35)
  ⟨`VeriMol.run_canonical_is_chosenForm, 10138577383654274918, .proven⟩,
  ⟨`VeriMol.run_canonical_same_molecule, 2912092019744879662, .proven⟩,
  ⟨`VeriMol.run_canonical_eq_iff, 17271148536161924623, .proven⟩,
  ⟨`VeriMol.run_canonical_of_renumbered, 7541755850943954755, .proven⟩,
  ⟨`VeriMol.run_canonical_again, 15684855247910714737, .proven⟩,
  ⟨`VeriMol.run_rewrite_of_canonical, 11084031954895591985, .proven⟩,
  ⟨`VeriMol.run_canonical_of_read, 14053237739763446567, .proven⟩,
  -- Single examples (theorems 36 to 44)
  ⟨`VeriMol.read_ethane, 3974991681432604405, .proven⟩,
  ⟨`VeriMol.read_acrylonitrile, 7708450068167771036, .proven⟩,
  ⟨`VeriMol.read_benzene, 11067692841987092348, .proven⟩,
  ⟨`VeriMol.read_salt, 1214867552444108547, .proven⟩,
  ⟨`VeriMol.read_heavyWater, 4116124607444724273, .proven⟩,
  ⟨`VeriMol.read_ammonium, 17055394608389401278, .proven⟩,
  ⟨`VeriMol.read_quadrupleBond, 11573400701897516361, .proven⟩,
  ⟨`VeriMol.read_writtenOutSymbols, 7202943358745428352, .proven⟩,
  ⟨`VeriMol.read_alanine, 2595879681484174442, .proven⟩,
  ⟨`VeriMol.read_transDifluoroethene, 4846641053975727284, .proven⟩,
  ⟨`VeriMol.read_cisDifluoroethene, 16040462986498859921, .proven⟩,
  ⟨`VeriMol.read_aceticAcid, 5485760265876117072, .proven⟩,
  ⟨`VeriMol.run_aceticAcid, 10439051841589373090, .proven⟩,
  ⟨`VeriMol.writePlain_aceticAcid, 9543460597615239176, .proven⟩,
  ⟨`VeriMol.write_aceticAcid, 3482530919947575496, .proven⟩,
  ⟨`VeriMol.run_rewrite_aceticAcid, 7667356988517039820, .proven⟩,
  ⟨`VeriMol.run_plain_aceticAcid, 17243051065005646657, .proven⟩,
  ⟨`VeriMol.run_refusal_ringNeverClosed, 4525172487454547457, .proven⟩,
  ⟨`VeriMol.run_refusal_twoProblems, 10578098086980900158, .proven⟩,
  ⟨`VeriMol.ethanol_renumbered, 9820793597971947258, .proven⟩,
  ⟨`VeriMol.cyclohexane_not_renumbered, 18300565136325885708, .proven⟩,
  ⟨`VeriMol.alanine_renumbered, 296248533041836245, .proven⟩,
  ⟨`VeriMol.alanine_not_mirrored, 4707395415701095744, .proven⟩,
  ⟨`VeriMol.run_canonical_ethanol, 17199670732244906541, .proven⟩,
  -- Molecules and canonical texts (theorem 45)
  ⟨`VeriMol.Molecule.canonicalText_eq_some_iff, 12308945278244627940, .proven⟩,
  ⟨`VeriMol.CanonicalText.molecule_injective, 6059168593706498891, .proven⟩,
  ⟨`VeriMol.Molecule.of_eq_of_iff, 5051634623777541487, .proven⟩,
  ⟨`VeriMol.isCanonicalText_iff_run, 16514248995331740923, .proven⟩,
  ⟨`VeriMol.Molecule.canonicalText_of, 8909458420349464893, .proven⟩,
  ⟨`VeriMol.CanonicalText.molecule_of, 11512168572848697105, .proven⟩,
  -- Which `Mol`s a rule is asked of: sound, and its checker (theorem 46)
  ⟨`VeriMol.Mol.isSound_iff, 7132483978751901530, .proven⟩,
  ⟨`VeriMol.Mol.Renumbered.sound_iff, 2117421705661935818, .proven⟩,
  -- The rule "no long perfluorinated group" (theorem 47)
  ⟨`VeriMol.Mol.FluoroLinked.symm, 17832047062248873546, .proven⟩,
  ⟨`VeriMol.Mol.FluoroLinked.trans, 16682768411108443170, .proven⟩,
  ⟨`VeriMol.Mol.HasFluoroGroup.of_le, 17906792057528277132, .proven⟩,
  ⟨`VeriMol.Mol.Renumbered.noFluoroGroup_iff, 14830635905292051147, .proven⟩,
  -- The checker of the rule: the search is right (theorem 48)
  ⟨`VeriMol.Mol.mem_fluoroGroupOf, 2492676872060230534, .proven⟩,
  ⟨`VeriMol.Mol.le_largestFluoroGroup_iff, 7176721815790148154, .proven⟩,
  ⟨`VeriMol.Mol.hasNoFluoroGroup_iff, 4305955494460845142, .proven⟩,
  -- The filter (theorem 49)
  ⟨`VeriMol.filter_eq_ok_iff, 16868790363758809705, .proven⟩,
  ⟨`VeriMol.filterPerfluoro_eq_ok_iff, 3796078680422931196, .proven⟩,
  ⟨`VeriMol.run_filter, 5514124967209595497, .proven⟩,
  ⟨`VeriMol.groupSize?_eq_some_iff, 1619940896, .proven⟩,
  ⟨`VeriMol.run_filter_eq_iff, 18265331011300753014, .proven⟩,
  ⟨`VeriMol.run_filter_exitCode_iff, 12485801636566998122, .proven⟩
]

end Audit
