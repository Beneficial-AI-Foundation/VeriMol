import VeriMol.Core.Mol

/-!
# The rule: no long perfluorinated group (SPEC.md, section 16.3)

`Mol.NoFluoroGroup m n` says that the `Mol` `m` has no perfluorinated group
of `n` or more carbon atoms. It is the rule of the one filter that is built.
This file says what is meant and not how it is found: it is written to be
read, and no program runs it. The checker that the program runs is a search,
in `VeriMol/Core/FluoroGroup.lean`, and `VeriMol/Proofs/FluoroGroup.lean`
proves that the search finds exactly what this file defines, for every `Mol`
and every `n` (theorem 48 of CLAIMS.md; theorem 47 is about the rule
itself).

## Where the rule comes from

Among the PFAS, the per- and polyfluoroalkyl substances that are often
called "forever chemicals", those with a long perfluorinated chain have
drawn the most attention. Buck and co-authors give the definition of the
OECD in these words: "long-chain" refers to perfluoroalkyl carboxylic acids
"with eight carbons and greater (i.e., with 7 or more perfluorinated
carbons)" and to perfluoroalkane sulfonates "with six carbons and greater
(i.e., with 6 or more perfluorinated carbons)" (R. C. Buck and others,
*Perfluoroalkyl and Polyfluoroalkyl Substances in the Environment:
Terminology, Classification, and Origins*, Integrated Environmental
Assessment and Management 7 (2011), pages 513 to 541,
doi:10.1002/ieam.258, under "Chain length terminology"). The paper writes a
perfluoroalkyl group as CnF2n+1–, "thereby including both linear and branched
structures".

The rule states the pattern behind these numbers for any compound, whatever
the group is attached to: a perfluorinated group of at least `n` carbon
atoms, as a chain, branched or in a ring. The number `n` is not fixed here.

## The definitions, in five steps

1. `Mol.SkeletonCarbon`: the five conditions that every carbon atom of a
   perfluorinated group meets.
2. `Mol.FluoroCarbon`: a fluorinated carbon atom meets them, and carries
   fluorine.
3. `Mol.GroupCarbon`: a carbon atom of a group is a fluorinated carbon atom,
   or a branch carbon atom, which meets the five conditions, need not carry
   fluorine, and is bonded to three carbon atoms of a group.
4. `Mol.FluoroLinked`: such atoms are linked when one can be reached from
   the other along bonds, through such atoms only.
5. `Mol.HasFluoroGroup`, and the rule, `Mol.NoFluoroGroup`.

## A reading, with choices

The rule is a reading of the wording above. It is not the rule of a law or
of a standard, and no theorem says that it is the right reading. Its main
choices:

* One fluorine atom on a carbon atom without hydrogen is enough.
* Only bonds between carbon atoms hold a group together: an oxygen atom
  between two groups parts them. So the number is the size of the largest
  single group, and not the number of fluorinated carbon atoms.
* A carbon atom without fluorine belongs to a group only where three carbon
  atoms of the group hold it.
* Chlorine, bromine and iodine on a carbon atom are not looked at. So
  C6F13–I has a group of six, as the formula of the paper counts it, and a
  chain of a chlorofluorocarbon is counted as well. The definition of PFAS
  that the OECD recommended in 2021 answers another question, which
  compounds are PFAS, and reads such an atom the other way: it asks for "at
  least one fully fluorinated methyl or methylene carbon atom (without any
  H/Cl/Br/I atom attached to it)" (OECD, *Reconciling Terminology of the
  Universe of Per- and Polyfluoroalkyl Substances: Recommendations and
  Practical Guidance*, OECD Series on Risk Management, No. 61, 2021, in its
  section 2.3).
* An aromatic bond counts as a single bond, so that the spelling of a bond
  cannot hide a group.

SPEC.md, section 16.3, has an example for each of these, and section 16.4
says what the rule does not say.
-/

namespace VeriMol

/-! ## The elements of an atom and of its neighbours -/

/-- The element of atom number `i`, or `none` if the `Mol` has no atom with
that number. -/
def Mol.elementOf (m : Mol) (i : Nat) : Option Element :=
  m.atoms[i]?.map (·.element)

/-- The elements of the atoms that atom number `c` is bonded to: one entry
for every bond of the atom, in the order of `Mol.neighbours`. -/
def Mol.neighbourElements (m : Mol) (c : Nat) : List (Option Element) :=
  (m.neighbours c).map m.elementOf

/-! ## The rule -/

/-- Whether no bond of atom number `c` is a double, triple or quadruple bond:
each of its bonds is a single bond or an aromatic bond. A `Mol` holds a bond
as aromatic when the text writes it with `:`, or with no symbol between two
atoms in lowercase (SPEC.md, section 5, rule 5). -/
def Mol.hasNoMultipleBond (m : Mol) (c : Nat) : Bool :=
  m.bonds.all fun bond =>
    !(bond.a == c || bond.b == c) || bond.order == .single || bond.order == .aromatic

/-- Atom number `c` of `m` meets the five conditions that every carbon atom of
a perfluorinated group must meet:

* it is a carbon atom;
* its count of hydrogens is 0;
* none of its bonds is a double, triple or quadruple bond;
* it has exactly four bonds;
* none of the four goes to a hydrogen atom. -/
def Mol.SkeletonCarbon (m : Mol) (c : Nat) : Prop :=
  m.elementOf c = some .C ∧
  m.atoms[c]?.map (·.hydrogens) = some 0 ∧
  m.hasNoMultipleBond c = true ∧
  (m.neighbourElements c).length = 4 ∧
  some Element.H ∉ m.neighbourElements c

/-- Atom number `c` of `m` is a fluorinated carbon atom:

* it meets the five conditions of `Mol.SkeletonCarbon`;
* at least one of its four bonds goes to a fluorine atom. -/
def Mol.FluoroCarbon (m : Mol) (c : Nat) : Prop :=
  m.SkeletonCarbon c ∧
  some Element.F ∈ m.neighbourElements c

/-- Atom number `c` of `m` is a carbon atom of a perfluorinated group. There
are two ways to be one:

* `fluoro`: `c` is a fluorinated carbon atom;
* `branch`: `c` meets the five conditions of `Mol.SkeletonCarbon`, and it is
  bonded to three different atoms `x`, `y` and `z` that are carbon atoms of a
  perfluorinated group themselves.

An atom of the second kind is a branch carbon atom. It stands where a group
branches, and it need not carry fluorine itself. The atom in the middle of
(CF3)3C– is one: the three –CF3 are fluorinated carbon atoms. -/
inductive Mol.GroupCarbon (m : Mol) : Nat → Prop
  | fluoro (c : Nat) : m.FluoroCarbon c → Mol.GroupCarbon m c
  | branch (c x y z : Nat) : m.SkeletonCarbon c →
      x ≠ y → x ≠ z → y ≠ z →
      x ∈ m.neighbours c → y ∈ m.neighbours c → z ∈ m.neighbours c →
      Mol.GroupCarbon m x → Mol.GroupCarbon m y → Mol.GroupCarbon m z →
      Mol.GroupCarbon m c

/-- Atom `c` is linked to atom `a`: it can be reached from `a` by going along
bonds, through carbon atoms of a perfluorinated group only.

* `start`: a carbon atom of a perfluorinated group is linked to itself.
* `step`: if `b` is linked to `a`, and `c` is a carbon atom of a
  perfluorinated group that is bonded to `b`, then `c` is linked to `a`. -/
inductive Mol.FluoroLinked (m : Mol) (a : Nat) : Nat → Prop
  | start : m.GroupCarbon a → Mol.FluoroLinked m a a
  | step (b c : Nat) : Mol.FluoroLinked m a b → c ∈ m.neighbours b → m.GroupCarbon c →
      Mol.FluoroLinked m a c

/-- `m` has a perfluorinated group of at least `n` carbon atoms: there is a
list `group` of `n` or more different atoms that are all linked to one atom
`a`. The group may be a chain, branched or a ring. -/
def Mol.HasFluoroGroup (m : Mol) (n : Nat) : Prop :=
  ∃ a group, List.Nodup group ∧ n ≤ group.length ∧ ∀ c ∈ group, m.FluoroLinked a c

/-- The rule: `m` has no perfluorinated group of `n` or more carbon atoms.
For `n = 0` it holds for no `Mol`, because every `Mol` has the group of no
atoms; the command of the program takes no 0. -/
def Mol.NoFluoroGroup (m : Mol) (n : Nat) : Prop :=
  ¬ m.HasFluoroGroup n

end VeriMol
