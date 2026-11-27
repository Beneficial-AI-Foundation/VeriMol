import VeriMol.Core
import TestData

/-!
# The tests

`lake test` builds everything, runs the audit, and then runs this file as a
program. The program fails if any test fails. It prints every failing test in
full.

A test is a name, an actual value and an expected value. The expected values
do not come from the Lean program. Most of them stand in `TestData.lean`, which
`reference/check_tests.py` writes from the model (SPEC.md as a Python program);
the lists below turn its entries into tests. A few are written here by hand.

The rest of the file is the machinery that runs the tests, followed by a few
checks of the repository itself.
-/

/-- One test, already evaluated: its name, whether the actual value equalled
the expected one, and both values as text for the failure report. -/
structure Test where
  name : String
  passed : Bool
  actual : String
  expected : String

/-- Builds a test from a name, an actual value and an expected value,
compared with `==`. -/
def test {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) : Test :=
  { name := name
    passed := actual == expected
    actual := reprStr actual
    expected := reprStr expected }

/-! ## Tests of single functions of Core -/

/-- Ethanol with the oxygen as atom 0, as `OCC` is read. -/
def ethanolFromOxygen : VeriMol.Mol :=
  { atoms := [
      { element := .O, isotope := none, charge := 0, hydrogens := 1 },
      { element := .C, isotope := none, charge := 0, hydrogens := 2 },
      { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single } ] }

/-- Ethanol with the oxygen as atom 2, as `CCO` is read. -/
def ethanolFromCarbon : VeriMol.Mol :=
  { atoms := [
      { element := .C, isotope := none, charge := 0, hydrogens := 3 },
      { element := .C, isotope := none, charge := 0, hydrogens := 2 },
      { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single } ] }

/-- Hexafluoroethane, as `FC(F)(F)C(F)(F)F` is read. -/
def hexafluoroethane : VeriMol.Mol :=
  { atoms := [
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 1, b := 3, order := .single },
      { a := 1, b := 4, order := .single },
      { a := 4, b := 5, order := .single },
      { a := 4, b := 6, order := .single },
      { a := 4, b := 7, order := .single } ] }

/-- Perfluoroneopentane, as `FC(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F` is read:
the carbon atom in the middle, atom 4, is bonded to the four other carbon
atoms, 1, 5, 9 and 13, and to no fluorine atom. -/
def perfluoroneopentane : VeriMol.Mol :=
  { atoms := [
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 1, b := 3, order := .single },
      { a := 1, b := 4, order := .single },
      { a := 4, b := 5, order := .single },
      { a := 4, b := 9, order := .single },
      { a := 4, b := 13, order := .single },
      { a := 5, b := 6, order := .single },
      { a := 5, b := 7, order := .single },
      { a := 5, b := 8, order := .single },
      { a := 9, b := 10, order := .single },
      { a := 9, b := 11, order := .single },
      { a := 9, b := 12, order := .single },
      { a := 13, b := 14, order := .single },
      { a := 13, b := 15, order := .single },
      { a := 13, b := 16, order := .single } ] }

/-- The same `Mol` with one hydrogen counted on the carbon atoms 9 and 13:
they are no fluorinated carbon atoms any more. No compound is like this; the
functions are asked all the same. -/
def withTwoHydrogens : VeriMol.Mol :=
  { perfluoroneopentane with
    atoms := (List.range 17).zip perfluoroneopentane.atoms |>.map fun (i, atom) =>
      if i == 9 || i == 13 then { atom with hydrogens := 1 } else atom }

/-- Hexafluoroethane with the fluorine atom number 3, which is bonded to the
carbon atom 1, exchanged for an atom of another element. -/
def pentafluoroethaneWith (element : VeriMol.Element) : VeriMol.Mol :=
  { hexafluoroethane with
    atoms := (List.range 8).zip hexafluoroethane.atoms |>.map fun (i, atom) =>
      if i == 3 then { atom with element := element } else atom }

/-- What the filter gives for a text, with `allows` as the checker of its
rule: whether a `Mol` is handed on, and its printed layout, or else the
reason. -/
def filterAnswer (allows : VeriMol.Mol → Bool) (text : String) : Bool × String :=
  match VeriMol.filter allows (fun _ => "refused by the rule".toList) text.toList with
  | .ok mol => (true, String.ofList mol.printed)
  | .error reason => (false, String.ofList reason)

/-- Carbon dioxide, as `O=C=O` is read. -/
def carbonDioxide : VeriMol.Mol :=
  { atoms := [
      { element := .O, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 0 },
      { element := .O, isotope := none, charge := 0, hydrogens := 0 } ],
    bonds := [
      { a := 0, b := 1, order := .double },
      { a := 1, b := 2, order := .double } ] }

/-- A `Mol` made by hand that has each kind of number of the key (SPEC.md,
section 3.2): every kind of bond and a missing bond, charges of both signs, a
mass number and the mass number 0, and ten hydrogens. It does not have every
charge and every number of hydrogens. No text spells it. -/
def eachKindOfNumber : VeriMol.Mol :=
  { atoms := [
      { element := .C, isotope := some 13, charge := -1, hydrogens := 3 },
      { element := .N, isotope := none, charge := 2, hydrogens := 0 },
      { element := .O, isotope := some 0, charge := 0, hydrogens := 10 },
      { element := .C, isotope := none, charge := -3, hydrogens := 0 },
      { element := .S, isotope := none, charge := 0, hydrogens := 0 } ],
    bonds := [
      { a := 0, b := 1, order := .double },
      { a := 0, b := 2, order := .triple },
      { a := 1, b := 2, order := .aromatic },
      { a := 1, b := 3, order := .quadruple },
      { a := 2, b := 3, order := .single } ] }

/-- L-alanine, as `N[C@@H](C)C(=O)O` is read: the nitrogen is atom 0. The
text writes the places of atom 1 in the order nitrogen, hydrogen, atom 2,
atom 3, and `@@` says clockwise for that order. The fixed order is hydrogen,
atom 0, atom 2, atom 3: one swap away, so the stored orientation is the other
one. -/
def alanineFromNitrogen : VeriMol.Mol :=
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

/-- L-alanine, as `C[C@H](N)C(=O)O` is read: the nitrogen is atom 2. -/
def alanineFromCarbon : VeriMol.Mol :=
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

/-- The mirror image of L-alanine, as `N[C@H](C)C(=O)O` is read. -/
def mirroredAlanine : VeriMol.Mol :=
  { alanineFromNitrogen with orientations := [{ atom := 1, orientation := .clockwise }] }

/-- Difluoroethene with the two fluorine atoms on opposite sides, as
`F/C=C/F` is read. -/
def transDifluoroethene : VeriMol.Mol :=
  { atoms := [
      { element := .F, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 1 },
      { element := .C, isotope := none, charge := 0, hydrogens := 1 },
      { element := .F, isotope := none, charge := 0, hydrogens := 0 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .double },
      { a := 2, b := 3, order := .single } ],
    orientations := [],
    geometries := [
      { a := 1, b := 2, geometry := .oppositeSides } ] }

/-- A carbon atom with two bromine atoms, a methyl group and a hydrogen, with
an orientation, as `Br[C@@H](Br)C` is read: the notation says an orientation,
although the two bromine atoms are bonded alike. -/
def twoBromines : VeriMol.Mol :=
  { atoms := [
      { element := .Br, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 1 },
      { element := .Br, isotope := none, charge := 0, hydrogens := 0 },
      { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 1, b := 3, order := .single } ],
    orientations := [
      { atom := 1, orientation := .anticlockwise } ],
    geometries := [] }

/-- `count` molecules of ethane side by side, as `CC.CC` and so on is read. -/
def ethanes (count : Nat) : VeriMol.Mol :=
  { atoms := List.replicate (2 * count) { element := .C, isotope := none, charge := 0, hydrogens := 3 },
    bonds := (List.range count).map fun j => { a := 2 * j, b := 2 * j + 1, order := .single } }

/-- A ring of six carbon atoms, as `C1CCCCC1` is read. -/
def ringOfSix : VeriMol.Mol :=
  { atoms := List.replicate 6 { element := .C, isotope := none, charge := 0, hydrogens := 2 },
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 0, b := 5, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 2, b := 3, order := .single },
      { a := 3, b := 4, order := .single },
      { a := 4, b := 5, order := .single } ] }

/-- A ring of five atoms with a tail of two, all seven atoms the same, as
`[N][N][N]1[N][N][N][N]1` is read: the atoms 0 and 1 are the tail, and the
atoms 2 to 6 the ring. -/
def ringWithTail : VeriMol.Mol :=
  { atoms := List.replicate 7 { element := .N, isotope := none, charge := 0, hydrogens := 0 },
    bonds := [
      { a := 0, b := 1, order := .single },
      { a := 1, b := 2, order := .single },
      { a := 2, b := 3, order := .single },
      { a := 2, b := 6, order := .single },
      { a := 3, b := 4, order := .single },
      { a := 4, b := 5, order := .single },
      { a := 5, b := 6, order := .single } ] }

/-- How many beginnings the search for the chosen form of a `Mol` holds after
`rounds` rounds, when it may hold `limit` of them; `none` if it gives up. It
is the search that `VeriMol.Mol.chosenOrder` runs, with another limit and
stopped earlier. The call is written out here a second time: the two tests of
`VeriMol.Mol.chosenForm` for molecules of ethane tie it to the program. -/
def heldAfter (limit : Nat) (m : VeriMol.Mol) (rounds : Nat) : Option Nat :=
  (VeriMol.Search.searchWithin limit (m.searchEntry m.smallerTwins)
    (VeriMol.Search.lePair VeriMol.leEntry) m.outline (List.range m.atoms.length) rounds).map
      List.length

/-- Tests written by hand, with expected values worked out by hand. -/
def unitTests : List Test := [
  test "numbers as text: 0, 7, 13 and 1000"
    ([0, 7, 13, 1000].map fun n => String.ofList (VeriMol.natText n)) ["0", "7", "13", "1000"],
  test "whole numbers as text: -100, -1, 0, 1 and 25"
    ([-100, -1, 0, 1, 25].map fun i => String.ofList (VeriMol.intText i)) ["-100", "-1", "0", "1", "25"],
  -- The chosen form (SPEC.md, section 3.2). Ethanol numbered from the oxygen,
  -- as `OCC` is read, and from the carbon, as `CCO` is read. The two keys are
  -- those that SPEC.md writes out.
  test "the key of ethanol numbered from the oxygen"
    (VeriMol.Mol.key ethanolFromOxygen) [[7, 8, 0, 0], [4, 5, 7, 0, 0], [4, 5, 5, 6, 0, 0]],
  test "the key of ethanol numbered from the carbon"
    (VeriMol.Mol.key ethanolFromCarbon) [[5, 6, 0, 0], [4, 5, 7, 0, 0], [4, 5, 7, 8, 0, 0]],
  test "the chosen form of ethanol numbered from the oxygen is ethanol numbered from the carbon"
    (VeriMol.Mol.chosenForm ethanolFromOxygen) (some ethanolFromCarbon),
  test "the chosen form of ethanol numbered from the carbon is itself"
    (VeriMol.Mol.chosenForm ethanolFromCarbon) (some ethanolFromCarbon),
  test "the chosen form of a Mol without atoms is that Mol"
    (VeriMol.Mol.chosenForm { atoms := [], bonds := [] }) (some { atoms := [], bonds := [] }),
  test "the two oxygen atoms of carbon dioxide are twins, and its carbon atom is no twin of them"
    ((VeriMol.Mol.twins carbonDioxide 0 2, VeriMol.Mol.twins carbonDioxide 2 0, VeriMol.Mol.twins carbonDioxide 0 1))
    (true, true, false),
  -- Each kind of number that the key has. By the rules of section 3.2: a
  -- quadruple bond is 0, a triple bond 1, a double bond 2, an aromatic
  -- bond 3, a single bond 4, no bond 5; carbon is 5, nitrogen 6, oxygen 7,
  -- sulfur 15; 3 hydrogens are 6, none are 9, ten are 10; the mass number
  -- 13 is 14, the mass number 0 is 1, none is 0; the charge -1 is 1,
  -- -3 is 5, +2 is 4, none is 0.
  test "the key of a Mol made by hand with every kind of bond, charges of both signs, two mass numbers and ten hydrogens"
    (VeriMol.Mol.key eachKindOfNumber)
    [[5, 6, 14, 1], [2, 6, 9, 0, 4], [3, 1, 7, 10, 1, 0], [4, 0, 5, 5, 9, 0, 5], [5, 5, 5, 5, 15, 9, 0, 0]],
  test "the two carbon atoms of ethane are twins, although they are bonded to each other"
    (VeriMol.Mol.twins
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 3 } ],
        bonds := [
          { a := 0, b := 1, order := .single } ] } 0 1)
    true,
  -- Stereo facts (SPEC.md, section 12.1). The number of pairs in falling
  -- order: in 3, 1, 2 the pairs (3, 1) and (3, 2) fall; a rising list has
  -- none; a falling list of four has all six.
  test "the pairs of a list that stand in falling order"
    ([[3, 1, 2], [1, 2, 3], [4, 3, 2, 1], []].map VeriMol.fallingPairs) [2, 0, 6, 0],
  -- The first statement, for atom 1 of alanine. The fixed order gives the
  -- stored mark. The order in which the text writes the places (nitrogen,
  -- hydrogen, atom 2, atom 3) is one swap away and gives the other mark,
  -- which is what `@@` says. Two swaps give the stored mark again. Three
  -- places are not the four places of the atom, and atom 0 has no
  -- orientation.
  test "the orientation of atom 1 of alanine, for its places in five orders, and of an atom without one"
    [VeriMol.Mol.orientationOf alanineFromNitrogen 1 [none, some 0, some 2, some 3],
     VeriMol.Mol.orientationOf alanineFromNitrogen 1 [some 0, none, some 2, some 3],
     VeriMol.Mol.orientationOf alanineFromNitrogen 1 [some 0, some 2, none, some 3],
     VeriMol.Mol.orientationOf alanineFromNitrogen 1 [some 3, some 2, some 0, none],
     VeriMol.Mol.orientationOf alanineFromNitrogen 1 [some 0, some 2, some 3],
     VeriMol.Mol.orientationOf alanineFromNitrogen 0 [none, some 1]]
    [some .anticlockwise, some .clockwise, some .anticlockwise, some .anticlockwise, none, none],
  -- The second statement, for the double bond of difluoroethene: its two
  -- fluorine atoms lie on opposite sides, whichever atom of the bond is named
  -- first. Atom 2 is no neighbour of atom 1 other than its partner, and the
  -- bond between the atoms 0 and 1 has no geometry.
  test "the geometry of the double bond of F/C=C/F, both ways round, and where there is none"
    [VeriMol.Mol.geometryOf transDifluoroethene 1 2 0 3, VeriMol.Mol.geometryOf transDifluoroethene 2 1 3 0,
     VeriMol.Mol.geometryOf transDifluoroethene 1 2 2 3, VeriMol.Mol.geometryOf transDifluoroethene 0 1 2 2]
    [some .oppositeSides, some .oppositeSides, none, none],
  -- The key of a Mol with a stereo fact (SPEC.md, section 3.2): the entry of
  -- the last atom ends with the stereo facts, for every atom 0,
  -- 1 (anticlockwise) or 2 (clockwise), and then for every bond 0,
  -- 1 (the same side) or 2 (opposite sides). Nitrogen is 6, carbon 5,
  -- oxygen 7; 2 hydrogens are 7, 1 is 8, 3 are 6, none are 9; a single bond
  -- is 4, a double bond 2, no bond 5.
  test "the key of alanine numbered from the nitrogen: its last entry ends with the stereo facts"
    (VeriMol.Mol.key alanineFromNitrogen)
    [[6, 7, 0, 0], [4, 5, 8, 0, 0], [4, 5, 5, 6, 0, 0], [5, 4, 5, 5, 9, 0, 0], [2, 5, 5, 5, 7, 9, 0, 0],
     [5, 4, 5, 5, 5, 7, 8, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  -- Two texts for L-alanine get one chosen form, and the mirror image another
  -- (theorems 26 and 27).
  test "the chosen form of alanine: the same for two numberings, and another for the mirror image"
    ((VeriMol.Mol.chosenForm alanineFromNitrogen).isSome,
     VeriMol.Mol.chosenForm alanineFromNitrogen == VeriMol.Mol.chosenForm alanineFromCarbon,
     VeriMol.Mol.chosenForm alanineFromNitrogen == VeriMol.Mol.chosenForm mirroredAlanine)
    (true, true, false),
  -- The two bromine atoms of `Br[C@@H](Br)C` are bonded alike. They are
  -- neighbours of an atom with an orientation, so they are no twins:
  -- exchanging them turns the orientation round. Without the orientation they
  -- are twins.
  test "two atoms that are bonded alike are no twins where they take part in a stereo fact"
    ((VeriMol.Mol.twins twoBromines 0 2, VeriMol.Mol.inStereoFact twoBromines 0, VeriMol.Mol.inStereoFact twoBromines 3,
      VeriMol.Mol.twins { twoBromines with orientations := [] } 0 2))
    (false, true, true, true),
  -- Beginnings that are alike (SPEC.md, section 3.2). A row says how an atom
  -- is bonded to each place before it, the nearest place first: 4 for a
  -- single bond, 2 for a double bond, 5 for none. Its bonded entries, each
  -- with its place in the row:
  test "the bonded entries of a row, each with its place in the row"
    (VeriMol.placedCodes 0 [5, 4, 5, 2]) [[1, 4], [3, 2]],
  -- Ethanol numbered from the carbon: atom 0 is bonded to atom 1, and atom 1
  -- to atom 2. Behind the beginning 0, atom 1 is bonded to the nearest place
  -- and atom 2 to none. Behind the beginning 1, 0, atom 2 is bonded to the
  -- second nearest place, where atom 1 stands.
  test "the outline of a beginning: nothing for an atom that is placed, and for every other atom its bonds to the places"
    [VeriMol.Mol.outlineOf ethanolFromCarbon [0], VeriMol.Mol.outlineOf ethanolFromCarbon [1, 0]]
    [[none, some [[0, 4]], some []], [none, none, some [[1, 4]]]],
  -- In the ring of six, the beginnings 0, 1, 2, 3, 4 and 4, 3, 2, 1, 0 have
  -- placed the same atoms, and atom 5 is bonded to the first and to the last
  -- place of both: they are alike. The beginnings 0, 1 and 1, 0 are not:
  -- atom 2 is bonded to the last place of the one and to the first of the
  -- other.
  test "two beginnings that are alike have the same outline, and two that are not have two outlines"
    (VeriMol.Mol.outlineOf ringOfSix [0, 1, 2, 3, 4] == VeriMol.Mol.outlineOf ringOfSix [4, 3, 2, 1, 0],
     VeriMol.Mol.outlineOf ringOfSix [0, 1] == VeriMol.Mol.outlineOf ringOfSix [1, 0])
    (true, false),
  test "the search takes no outlines for a Mol with stereo facts, and it takes them for a Mol without"
    ((VeriMol.Mol.outline alanineFromNitrogen).isNone, (VeriMol.Mol.outline ethanolFromCarbon).isSome)
    (true, true),
  -- The beginnings of a round are counted after those with the same outline
  -- are taken out, and of these the first is held. Two extensions:
  -- 1 behind 0, and 0 behind 1. As their outline take their length, which is
  -- 2 for both: one beginning is left, the first, and that is within a limit
  -- of 1. Without outlines two beginnings are left, which is more than 1.
  test "a round counts its beginnings after those with the same outline are taken out, and holds the first of them"
    (VeriMol.Search.mergedWithin 1 (some List.length) [([0], 1), ([1], 0)],
     VeriMol.Search.mergedWithin 1 (none : Option (List Nat → Nat)) [([0], 1), ([1], 0)])
    (some [[0, 1]], none),
  -- The ring of five with a tail (SPEC.md, section 3.2), all atoms the same.
  -- Each of the 7 atoms can be the first. Then a neighbour: 14, one for each
  -- bond and each direction. Then on from the last atom: 2 ways for each of
  -- the 5 atoms with two neighbours, 6 for the atom with three, none for the
  -- end of the tail, 16. Then the paths of four atoms, 9 of them, each in
  -- both directions, are 18; the two directions along the four ring atoms
  -- without the tail are alike, 17. Then the ring closes, in 9 beginnings,
  -- which differ only in the place of the atom that carries the tail: 5.
  -- Then the tail.
  test "how many beginnings the search holds after each round for a ring of five with a tail"
    ((List.range 8).map (heldAfter 1000 ringWithTail))
    [some 1, some 7, some 14, some 16, some 17, some 5, some 1, some 1],
  test "the ring with a tail: the search ends when it may hold 17 beginnings, and gives up when it may hold 16"
    ((heldAfter 17 ringWithTail 7).isSome, (heldAfter 16 ringWithTail 7).isSome)
    (true, false),
  -- Going round the ring of six: one beginning for each of the 6 atoms to
  -- start at; then one for each way round, 12; when five atoms are placed,
  -- the two beginnings that have left out the same atom are alike, 6; and
  -- when the ring is closed, all are alike.
  test "how many beginnings the search holds after each round for a ring of six atoms"
    ((List.range 7).map (heldAfter 1000 ringOfSix))
    [some 1, some 6, some 12, some 12, some 12, some 6, some 1],
  test "the search may hold as many beginnings as its limit says: 12 for the ring of six, and not 11"
    ((heldAfter 12 ringOfSix 6).isSome, (heldAfter 11 ringOfSix 6).isSome)
    (true, false),
  -- Nine molecules of ethane (SPEC.md, section 3.2): after four molecules
  -- there are 126 choices of four, and with the first atom of one of the five
  -- others 630, which is the most. Of ten molecules there are 210 choices of
  -- four, and with the first atom of one of the six others 1,260.
  test "nine molecules of ethane: the search holds 630 beginnings at most, so it ends with a limit of 630 and gives up with 629"
    (heldAfter 630 (ethanes 9) 18, heldAfter 629 (ethanes 9) 18, heldAfter 1000 (ethanes 9) 8, heldAfter 1000 (ethanes 9) 9)
    (some 1, none, some 126, some 630),
  test "ten molecules of ethane: the search would hold 1,260 beginnings, so it gives up with the limit of the program"
    (VeriMol.Mol.chosenForm (ethanes 10), heldAfter 1260 (ethanes 10) 20, heldAfter 1259 (ethanes 10) 20)
    (none, some 1, none),
  test "nine molecules of ethane have a chosen form, which is themselves, and ten have none"
    (VeriMol.Mol.chosenForm (ethanes 9) == some (ethanes 9), (VeriMol.Mol.chosenForm (ethanes 10)).isNone)
    (true, true),
  -- A Mol with stereo facts: the search takes no outlines, so no beginning is
  -- taken out. `F/C=C/F` can be walked from each of its two carbon atoms,
  -- which are no twins (each has a fluorine atom of its own), and both
  -- numberings have the least key: 2 beginnings to the end. Without the
  -- geometry the two beginnings are alike at the end.
  test "the search holds 2 beginnings to the end for F/C=C/F, and 1 at the end without its geometry"
    (heldAfter 2 transDifluoroethene 4, heldAfter 1 transDifluoroethene 4,
     heldAfter 2 { transDifluoroethene with geometries := [] } 4, heldAfter 1 { transDifluoroethene with geometries := [] } 4)
    (some 2, none, some 1, none),
  -- The filter (SPEC.md, section 16). Hexafluoroethane, as `FC(F)(F)C(F)(F)F`
  -- is read: the atoms 1 and 4 are its two carbon atoms, each with three
  -- fluorine atoms and the other carbon atom around it. They are one
  -- perfluorinated group of two. The search lists the atom that it finds
  -- last first.
  test "hexafluoroethane: its two carbon atoms are fluorinated carbon atoms, and no other atom is"
    ((List.range 8).filter hexafluoroethane.isFluoroCarbon) [1, 4],
  test "hexafluoroethane: the search from each carbon atom finds both, and from a fluorine atom, or from a number that is no atom, nothing"
    (hexafluoroethane.fluoroGroupOf 1, hexafluoroethane.fluoroGroupOf 4, hexafluoroethane.fluoroGroupOf 0,
     hexafluoroethane.fluoroGroupOf 8)
    ([4, 1], [1, 4], [], []),
  test "hexafluoroethane: one group, of size 2; so no group of 3 or more, and one of 2 or more"
    (hexafluoroethane.fluoroGroups, hexafluoroethane.largestFluoroGroup,
     hexafluoroethane.hasNoFluoroGroup 3, hexafluoroethane.hasNoFluoroGroup 2)
    ([[4, 1]], 2, true, false),
  -- With too few steps the search stops early: one step finds atom 1 and no
  -- more. The program gives it four steps for every atom and one more,
  -- here 33, which the proof shows to be enough. The search goes through the
  -- atoms of its first list only: with atom 4 left out of it, atom 1 is all
  -- it finds.
  test "hexafluoroethane: the search with 1 step, with 4 steps and with 5 steps"
    (hexafluoroethane.spread [1, 4] 1 [1] [], hexafluoroethane.spread [1, 4] 4 [1] [],
     hexafluoroethane.spread [1, 4] 5 [1] [])
    ([1], [1], [4, 1]),
  test "hexafluoroethane: the carbon atoms of its groups; and the search goes through no other atom"
    (hexafluoroethane.groupCarbons, hexafluoroethane.spread [1] 33 [1] [])
    ([1, 4], [1]),
  -- A branch carbon atom (SPEC.md, section 16.3). In perfluoroneopentane the
  -- atom in the middle, atom 4, carries no fluorine. The four atoms around it
  -- are fluorinated carbon atoms, so the first round adds atom 4, and the
  -- second adds nothing. All five are one group. The search from atom 1
  -- finds atom 4 next, then 5, 9 and 13, and lists the atom that it finds
  -- last first.
  test "perfluoroneopentane: four fluorinated carbon atoms; the atom in the middle is none, and meets the five conditions"
    ((List.range 17).filter perfluoroneopentane.isFluoroCarbon, perfluoroneopentane.isSkeletonCarbon 4,
     perfluoroneopentane.isSkeletonCarbon 0)
    ([1, 5, 9, 13], true, false),
  test "perfluoroneopentane: the first round adds the atom in the middle, and the second adds nothing"
    (perfluoroneopentane.newGroupCarbons [1, 5, 9, 13], perfluoroneopentane.newGroupCarbons [4, 1, 5, 9, 13],
     perfluoroneopentane.groupCarbons)
    ([4], [], [4, 1, 5, 9, 13]),
  test "perfluoroneopentane: one group of five"
    (perfluoroneopentane.fluoroGroups, perfluoroneopentane.fluoroGroupOf 4, perfluoroneopentane.largestFluoroGroup,
     perfluoroneopentane.hasNoFluoroGroup 5, perfluoroneopentane.hasNoFluoroGroup 6)
    ([[13, 9, 5, 4, 1]], [13, 9, 5, 1, 4], 5, false, true),
  -- With a hydrogen counted on two of the outer carbon atoms, only two
  -- fluorinated carbon atoms are left beside the atom in the middle: it is no
  -- branch carbon atom, and there are two groups of one.
  test "a carbon atom with only two fluorinated carbon atoms beside it is no branch carbon atom"
    (withTwoHydrogens.groupCarbons, withTwoHydrogens.fluoroGroups, withTwoHydrogens.largestFluoroGroup)
    ([1, 5], [[1], [5]], 1),
  -- The fifth condition names hydrogen alone (SPEC.md, section 16.3). With a
  -- chlorine or an iodine atom in the place of one fluorine atom, the carbon
  -- atom 1 still meets the five conditions and stays in the group of atom 4.
  -- With a hydrogen atom there, written as an atom of its own, it does not:
  -- atom 4 is a group of one.
  test "a chlorine or an iodine atom on a carbon atom leaves it in its group, and a hydrogen atom takes it out"
    ([VeriMol.Element.Cl, VeriMol.Element.I, VeriMol.Element.H].map fun element =>
      ((pentafluoroethaneWith element).isSkeletonCarbon 1, (pentafluoroethaneWith element).groupCarbons,
       (pentafluoroethaneWith element).largestFluoroGroup))
    [(true, [1, 4], 2), (true, [1, 4], 2), (false, [4], 1)],
  test "whether a list holds three different numbers, and two"
    ([VeriMol.hasThreeDifferent [], VeriMol.hasThreeDifferent [1, 2], VeriMol.hasThreeDifferent [1, 2, 1, 2],
      VeriMol.hasThreeDifferent [1, 2, 3], VeriMol.hasThreeDifferent [5, 5, 7, 5, 9]],
     [VeriMol.hasTwoDifferent [3], VeriMol.hasTwoDifferent [3, 3, 3], VeriMol.hasTwoDifferent [3, 3, 4]])
    ([false, false, false, true, true], [false, false, true]),
  -- The number behind `filter perfluoro` (section 16.1).
  test "which texts are a number behind `filter perfluoro`"
    (["6", "006", "12", "0", "00", "", "6a", "+6", "1000000000000000000000"].map
      fun text => VeriMol.groupSize? text.toList)
    [some 6, some 6, some 12, none, none, none, none, none, some 1000000000000000000000],
  -- The filter asks its three questions in their order (section 16.1),
  -- whatever the rule: a text that is not read gets the reader's problem, a
  -- Mol that is not sound its reason, and only then the rule.
  test "the filter with a rule that refuses everything, and with one that lets everything through"
    ((["C(", "[CH3]", "C"].map fun text => filterAnswer (fun _ => false) text),
     (["C(", "[CH3]", "C"].map fun text => filterAnswer (fun _ => true) text))
    ([(false, "position 1: '(' is never closed"),
      (false, "the Mol is not sound: the bonds and hydrogens of atom 0 add up to no usual valence of its element"),
      (false, "refused by the rule")],
     [(false, "position 1: '(' is never closed"),
      (false, "the Mol is not sound: the bonds and hydrogens of atom 0 add up to no usual valence of its element"),
      (true, "{ atoms := [\n    { element := .C, isotope := none, charge := 0, hydrogens := 4 } ],\n"
        ++ "  bonds := [],\n  orientations := [],\n  geometries := [] }\n")])
]

/-- The elements: their symbols, and which element a text is the symbol of.
The expected values are `TestData.elementSymbols` and `TestData.symbolProbes`. -/
def elementTests : List Test :=
  test "the 118 element symbols, in the order of SPEC.md, section 15"
      (VeriMol.Element.all.map fun e => String.ofList e.symbol) TestData.elementSymbols
    :: TestData.symbolProbes.map fun (text, expected) =>
      test s!"which element has the symbol {text.quote}"
        ((VeriMol.Element.ofSymbol? text.toList).map fun e => String.ofList e.symbol) expected

/-- The `Mol`s of `TestData.mols`: each one is printed as the model prints it,
and it is well formed exactly when the model says so. -/
def molTests : List Test :=
  TestData.mols.flatMap fun (name, _, mol, lines, wellFormed) => [
    test s!"printed: {name}" (String.ofList mol.printed) (String.join (lines.map (· ++ "\n"))),
    test s!"well formed or not: {name}" (decide mol.WellFormed) wellFormed]

/-- Cutting a text into tokens, for every test text. The tokens are those of
the model. So is the problem in the characters that stopped the cutting. The
expected values are `TestData.cuts`. -/
def cutTests : List Test :=
  TestData.cuts.flatMap fun (text, tokens, toTheEnd, problem) =>
    let cut := VeriMol.cut text.toList
    [test s!"the tokens of {text.quote}" (cut.tokens, cut.problem.isNone) (tokens, toTheEnd),
     test s!"the problem in the characters of {text.quote}"
       (cut.problem.map fun p => (p.position, String.ofList p.message)) problem]

/-- Spelling tokens as text. For the tokens of every test text: spelling them
and cutting the result gives the same tokens. For every text that the model
writes: spelling its tokens gives the text back, character for character. The
expected values are `TestData.cuts` and `TestData.spellings`. -/
def spellTests : List Test :=
  (TestData.cuts.map fun (text, tokens, _, _) =>
    let plain := tokens.map (·.token)
    test s!"spelling the tokens of {text.quote} and cutting again"
      ((VeriMol.spell plain).map fun spelled =>
        ((VeriMol.cut spelled).tokens.map (·.token), (VeriMol.cut spelled).problem))
      (some (plain, none)))
  ++ TestData.spellings.map fun written =>
    test s!"the tokens of {written.quote}, spelled"
      ((VeriMol.spell ((VeriMol.cut written.toList).tokens.map (·.token))).map String.ofList)
      (some written)

/-- Reading a text gives exactly the `Mol` that the model reads from it, as a
Lean object. The expected values are the entries of `TestData.mols` that
belong to a text. -/
def readTests : List Test :=
  TestData.mols.filterMap fun (name, ofAText, mol, _, _) =>
    if ofAText then
      some (test s!"the Mol of {name.quote}" (VeriMol.read name.toList).toOption (some mol))
    else none

/-- What the writer gives for a `Mol`, in the form of `TestData.lean`: whether
a text comes out, and the text, or else the reason why the `Mol` is refused. -/
def written : Except (List Char) (List Char) → Bool × String
  | .ok text => (true, String.ofList text)
  | .error reason => (false, String.ofList reason)

/-- The answers of the writer for one `Mol`, each against what the model
gives: what the program writes for `plain` and for `rewrite`, which are the
plain spelling and the spelling with round brackets, with the stereo marks of
the `Mol` (SPEC.md, sections 9 and 12.3); and what it writes for `canonical`,
which is the chosen form of the `Mol` in the spelling of `rewrite` (section
3.2). -/
def writerTestsOf (name : String) (mol : VeriMol.Mol) (plain brackets chosen : Bool × String) :
    List Test :=
  [test s!"what plain writes for: {name}" (written (VeriMol.writePlain mol)) plain,
   test s!"what rewrite writes for: {name}" (written (VeriMol.write mol)) brackets,
   test s!"what canonical writes for: {name}" (written (VeriMol.writeChosen mol)) chosen]

/-- Writing a `Mol`. The `Mol`s are those of `TestData.mols`, whose answers
stand in `TestData.writings` in the same order, and those of
`TestData.renumbered`: the `Mol`s of 121 test texts, with their atoms numbered
in another order. -/
def writeTests : List Test :=
  test "TestData.writings names the Mols of TestData.mols, in the same order"
      (TestData.writings.map (·.1)) (TestData.mols.map (·.1))
    :: ((TestData.mols.zip TestData.writings).flatMap
        fun ((name, _, mol, _, _), (_, plain, brackets, chosen)) =>
          writerTestsOf name mol plain brackets chosen)
    ++ TestData.renumbered.flatMap fun (name, mol, plain, brackets, chosen) =>
      writerTestsOf name mol plain brackets chosen

/-- The lists of atom numbers `groups`, each with its atoms in increasing
order: the form in which `TestData.filters` holds the groups of the model. -/
def inIncreasingOrder (atoms : Nat) (groups : List (List Nat)) : List (List Nat) :=
  groups.map fun group => (List.range atoms).filter group.contains

/-- What the filter asks of a `Mol` (SPEC.md, section 16), for the `Mol`s of
`TestData.mols`. The answers of the model stand in `TestData.filters`, in the
same order. For every `Mol`: the first reason why it is not sound, or none,
and whether the checker of soundness says yes. For every well formed `Mol`:
its perfluorinated groups, and the size of the largest. -/
def filterTests : List Test :=
  test "TestData.filters names the Mols of TestData.mols, in the same order"
      (TestData.filters.map (·.1)) (TestData.mols.map (·.1))
    :: (TestData.mols.zip TestData.filters).flatMap
      fun ((name, _, mol, _, _), (_, problem, groups)) =>
        [test s!"why not sound, if so: {name}" (mol.soundProblem.map String.ofList) problem,
         test s!"sound or not: {name}" mol.isSound problem.isNone]
        ++ match groups with
          | none => []
          | some groups =>
            [test s!"the perfluorinated groups of: {name}"
               (inIncreasingOrder mol.atoms.length mol.fluoroGroups) groups,
             test s!"the size of the largest perfluorinated group of: {name}"
               mol.largestFluoroGroup ((groups.map List.length).foldl max 0)]

/-! ## Tests of the whole program -/

/-- Each line is a name, the command-line arguments, and the expected
(standard output, standard error, exit code). Each one is checked three
times: against `VeriMol.run`, against the built program, and against the second
program, `answers`, which the long check of the program asks for its answers
(`reference/check_app.py`). So on these lists of arguments the three cannot
drift apart unnoticed.

The lines are `TestData.programs`: what the model prints. -/
def programTests : List (String × List String × (String × String × Nat)) :=
  TestData.programs.map fun (args, lines, stderr, exitCode) =>
    (s!"app {" ".intercalate (args.map (·.quote))}", args,
      (String.join (lines.map (· ++ "\n")), stderr, exitCode))

/-! ## How the program tests are run -/

/-- What `VeriMol.run` answers for the given command-line arguments, as
(standard output, standard error, exit code). -/
def viaCore (args : List String) : String × String × Nat :=
  let output := VeriMol.run (args.map String.toList)
  (String.ofList output.stdout, String.ofList output.stderr, output.exitCode)

/-- What a built program really does for the given command-line arguments, as
(standard output, standard error, exit code). It starts the file of that name
that sits next to this test program: `.lake/build/bin/app` or
`.lake/build/bin/answers`. Lake builds both before the tests (see
lakefile.toml). -/
def viaBuilt (program : String) (args : List String) : IO (String × String × Nat) := do
  let folder := (← IO.appPath).parent.getD "."
  let result ← IO.Process.output
    { cmd := (folder / program).toString, args := args.toArray, stdin := .null }
  return (result.stdout, result.stderr, result.exitCode.toNat)

/-- What the built program does when its answer cannot be written (SPEC.md,
section 8). It is started through the shell `sh`, which sends its standard
output where nothing can be written: `redirect` is `>&-` for an output that
is closed, and `>/dev/full` for a device that is always full. Returned are
whether standard error begins with the words with which Lean reports an
action that failed, and the exit code. If the shell cannot be started, the
answer is `(false, 0)`: the test then fails, and the other tests still run.

The answer of the program must be short here. A long answer fails while it
is printed, with or without the line of `Main.lean` that writes out what is
still waiting (`flush`). A short one waits until the program ends, and only
that line notices that it cannot be written. These are the only tests that
need a shell. -/
def viaProgramUnableToWrite (redirect : String) (args : List String) : IO (Bool × Nat) := do
  let folder := (← IO.appPath).parent.getD "."
  try
    let result ← IO.Process.output
      { cmd := "sh",
        args := #["-c", "\"$0\" \"$@\" " ++ redirect, (folder / "app").toString] ++ args.toArray,
        stdin := .null }
    return (result.stderr.startsWith "uncaught exception: ", result.exitCode.toNat)
  catch _ =>
    return (false, 0)

/-! ## The second program

`answers` gives what `VeriMol.run` gives for many lists of command-line
arguments in one start (`Answers.lean`). What follows starts it and cuts what
it prints into answers. -/

/-- The first characters of a text that take the given number of bytes when
the text is written out (in UTF-8), and the characters behind them. `none` if
the text ends before that, or if a character lies across the end. -/
def takeBytes : Nat → List Char → Option (List Char × List Char)
  | 0, rest => some ([], rest)
  | _, [] => none
  | bytes, c :: rest =>
    if c.utf8Size ≤ bytes then
      (takeBytes (bytes - c.utf8Size) rest).map fun (taken, left) => (c :: taken, left)
    else none

/-- The answers at the beginning of what the second program printed, each as
(standard output, standard error, exit code), and the text that is left
behind them. The program prints an answer as one line with three numbers,
the exit code and the numbers of bytes of the two texts, and then the two
texts. At most `most` answers are taken, and fewer if the text does not go
on as it must. So if the program printed exactly the answers it was asked
for, they are all here, and nothing is left. -/
def answersIn : Nat → List Char → List (String × String × Nat) × List Char
  | 0, text => ([], text)
  | most + 1, text =>
    match text.span (· != '\n') with
    | (line, _ :: rest) =>
      match ((String.ofList line).splitOn " ").map String.toNat? with
      | [some exitCode, some forOutput, some forError] =>
        match takeBytes forOutput rest with
        | some (stdout, rest) =>
          match takeBytes forError rest with
          | some (stderr, rest) =>
            let (answers, left) := answersIn most rest
            ((String.ofList stdout, String.ofList stderr, exitCode) :: answers, left)
          | none => ([], text)
        | none => ([], text)
      | _ => ([], text)
    | _ => ([], text)

/-- A list cut into pieces of `size` entries each, in their order. The last
piece may be shorter. -/
def inPieces {α : Type} (size : Nat) (list : List α) : List (List α) :=
  (List.range ((list.length + size - 1) / size)).map fun i => (list.drop (i * size)).take size

/-- What the second program gives for some lists of command-line arguments,
in one start. It is the file `answers` that sits next to this test program;
Lake builds it before the tests (see lakefile.toml). Each list is handed to
it as the number of its arguments, followed by the arguments. Returned are
the answers that it printed, and how the start itself ended: its exit code,
what it wrote on its own standard error, and the beginning of what it
printed behind the answers that were asked for. These three must be 0,
nothing and nothing. -/
def viaAnswers (lists : List (List String)) :
    IO (List (String × String × Nat) × Nat × String × String) := do
  let arguments := lists.flatMap fun list => toString list.length :: list
  let (stdout, stderr, exitCode) ← viaBuilt "answers" arguments
  let (answers, left) := answersIn lists.length stdout.toList
  return (answers, exitCode, stderr, String.ofList (left.take 80))

/-! ## Checks of the repository itself

These do not test what the program computes. They make sure that nothing is
silently left out: a Lean file that no other file imports is neither built
nor checked, so a theorem in it would count for nothing.
-/

/-- The folder of this repository. This program is the file
`.lake/build/bin/tests` inside it. -/
def repositoryFolder : IO System.FilePath := do
  let program ← IO.appPath
  let some folder := program.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | throw (IO.userError s!"cannot find the repository folder from {program}")
  return folder

/-- Where a module stands, without its extension: `VeriMol/Core/Run` for the
module `VeriMol.Core.Run`. -/
def placeOf (module : String) : String :=
  module.replace "." "/"

/-- The module names of the files with the given extension that belong to a
library: its root file and everything in the folder of its name. The library
`VeriMol.Core` is the file `VeriMol/Core.lean` and the files under
`VeriMol/Core/`, and the file `VeriMol/Core/Run.lean` has the module name
`VeriMol.Core.Run`. -/
def modulesOf (folder : System.FilePath) (library extension : String) : IO (List String) := do
  let mut modules := []
  if ← (folder / s!"{placeOf library}.{extension}").pathExists then
    modules := [library]
  if ← (folder / placeOf library).isDir then
    for file in ← (folder / placeOf library).walkDir do
      if file.extension == some extension then
        let inside := file.components.drop folder.components.length
        modules := ".".intercalate (inside.dropLast ++ [file.fileStem.getD ""]) :: modules
  return (modules.toArray.qsort (· < ·)).toList

/-- The module that a line imports, if the line is exactly `import` and one
module name, made of letters, digits, `_` and dots, and nothing else. A line
with anything behind the name is no import line here, although Lean takes it
for one: a comment can begin there, which takes the next lines out of the
file, and a declaration can stand there. -/
def importedModule? (characters : List Char) : Option String :=
  let name := characters.drop 7
  if "import ".toList.isPrefixOf characters && !name.isEmpty
      && name.all (fun c => c.isAlphanum || c == '_' || c == '.') then
    some (String.ofList name)
  else none

/-- The root file of a library, `VeriMol/Core.lean` for `VeriMol.Core`: the
modules it imports, and every other line that is not empty. -/
def rootFile (repository : System.FilePath) (library : String) :
    IO (List String × List String) := do
  let text ← IO.FS.readFile (repository / s!"{placeOf library}.lean")
  let mut imports := []
  let mut others := []
  for line in text.splitOn "\n" do
    let characters := line.toList.filter (· ≠ '\r')
    match importedModule? characters with
    | some name => imports := name :: imports
    | none =>
      if characters.any (· ≠ ' ') then
        others := String.ofList characters :: others
  return (imports.reverse, others.reverse)

/-- Does a text hold the word with which an option of Lean is set? The word
is put together here, so that this file does not hold it. No file may hold
it, not even in a comment: an option that is set inside a file wins over the
options of `lakefile.toml`, which turn every warning into an error and refuse
a name that was never introduced, and one option switches Lean's kernel off
for a declaration. (`Audit.lean` holds the word once, on purpose, for a
specimen of its self-test. A macro could set an option without the word; the
audit refuses a macro in Core and Proofs.) -/
def holdsTheOptionWord (text : String) : Bool :=
  (text.splitOn ("set_" ++ "option")).length > 1

/-- Eight words of Lean: of six commands and one tactic that run code while a
file is built, or when a file that imports it is read, and of one command
that ends a file before its end. The first works a term out and prints it,
and the second works one out and asks that it is true. The third ends the
file. The fourth declares code that runs when the file is loaded. The last
four run a piece of Lean's own machinery. Such code can read and write files,
and it leaves no declaration behind that the audit could see. Each word is
put together here, so that this file does not hold it. The list holds what is
known: a command that is not on it is not found by its word. -/
def wordsThatRunCode : List String :=
  ["#" ++ "eval", "#" ++ "guard", "#" ++ "exit", "initial" ++ "ize", "run_" ++ "cmd",
    "run_" ++ "elab", "run_" ++ "meta", "run_" ++ "tac"]

/-- Does a line begin with a command of Lean that starts with `#`? Three of
the words above are such commands. The others of this kind print something,
and nothing here needs them: all are refused at the beginning of a line, as a
second net. A heading inside a comment begins with `#` and a space, or with
`##`, and is no command. -/
def beginsWithAHashCommand (line : String) : Bool :=
  match line.toList.dropWhile (· == ' ') with
  | '#' :: next :: _ => next.isAlpha
  | _ => false

/-- Does a text hold one of the eight words, anywhere, in a comment and inside
a longer name as well? Or a line that begins with a command with `#`? -/
def holdsAWordThatRunsCode (text : String) : Bool :=
  wordsThatRunCode.any (fun word => (text.splitOn word).length > 1)
    || (text.splitOn "\n").any beginsWithAHashCommand

/-- The files of the program, the proofs, the second program, the tests and
their data, and the ledger: what the two checks below read as text.
`Audit.lean` is not among them: it is the checker itself, it holds the option
word once for a specimen, and its last line runs it with one of the eight
words. -/
def filesReadAsText (repository : System.FilePath) : IO (List String) := do
  let mut files := ["Main.lean", "Answers.lean", "Tests.lean", "TestData.lean", "Audit/Ledger.lean"]
  for file in ← modulesOf repository "VeriMol" "lean" do
    files := files ++ [placeOf file ++ ".lean"]
  return files

/-- The files of `filesReadAsText` whose text the given test says yes to. -/
def filesThatHold (holds : String → Bool) (repository : System.FilePath) : IO (List String) := do
  let mut found := []
  for file in ← filesReadAsText repository do
    if holds (← IO.FS.readFile (repository / file)) then
      found := found ++ [file]
  return found

/-- `leanchecker` is part of the Lean installation. It reads the compiled
file of a Lean file and checks every declaration in it again with Lean's
kernel, independently of the build. It prints nothing and ends with exit code 0
when all is well.

It is started once for every file under `VeriMol/Core/` and
`VeriMol/Proofs/`, and the runs go on side by side. Each run gets one file.
For that, two kinds of files are treated specially: `leanchecker` takes a
name to mean the file and everything in the folder of that name. So the
three root files `VeriMol.lean`, `VeriMol/Core.lean` and `VeriMol/Proofs.lean`
are left out. They hold only import lines: the audit makes sure that they
declare nothing (`Audit.rootFileProblems`), and a test here that every line of
them is an import line and nothing else. And a file with a folder of its own
name next to it is reported as a problem. -/
def independentCheck (files : List String) : IO Test := do
  let name := "leanchecker accepts every declaration of Core and Proofs"
  if (← IO.getEnv "LEAN_PATH").isNone then
    return test name ["not run: start the tests with \"lake test\""] []
  try
    let mut problems := []
    let mut runs := []
    for file in files do
      if files.any (·.startsWith (file ++ ".")) then
        problems := problems ++ [s!"{file} has a folder of its own name next to it, so "
          ++ "leanchecker cannot check it alone: give the file or the folder another name"]
      else
        let run ← IO.asTask (IO.Process.output
          { cmd := "leanchecker", args := #[file], stdin := .null })
        runs := runs ++ [(file, run)]
    for (file, run) in runs do
      let result ← IO.ofExcept run.get
      if result.exitCode != 0 || result.stdout ++ result.stderr != "" then
        problems := problems ++ [s!"{file}: exit code {result.exitCode}, "
          ++ s!"output {(result.stdout ++ result.stderr).quote}"]
    return test name problems []
  catch problem =>
    return test name [s!"leanchecker could not be started: {problem}"] []

/-- So that no file of Core or Proofs stays unbuilt and unchecked (rules 3
and 9 of the project, which `CLAIMS.md` lists): `VeriMol/Core.lean` and
`VeriMol/Proofs.lean` contain only import lines, and every file in their
folders is imported there. `VeriMol.lean`, which stands for both libraries,
imports these two and holds nothing else, and no file under `VeriMol/` stands
outside the two folders. No compiled file under `VeriMol/` is left over from
a file that was deleted or renamed. None of the files of `filesReadAsText`
sets an option of Lean, and none holds the word of a command that runs code
while a file is built, nor a line that begins with a command with `#`. Then
the independent check of every file under `VeriMol/Core/` and
`VeriMol/Proofs/`. -/
def repositoryChecks : IO (List Test) := do
  let repository ← repositoryFolder
  let libraries := ["VeriMol.Core", "VeriMol.Proofs"]
  let mut tests := []
  let mut toCheck := []
  for library in libraries do
    let sources ← modulesOf repository library "lean"
    let (imports, others) ← rootFile repository library
    tests := tests ++ [
      test s!"{placeOf library}.lean imports every file under {placeOf library}/"
        (sources.filter fun file => file != library && !imports.contains file) [],
      test s!"{placeOf library}.lean contains only import lines" others []]
    toCheck := toCheck ++ sources.filter (· != library)
  let (imports, others) ← rootFile repository "VeriMol"
  let sources ← modulesOf repository "VeriMol" "lean"
  let compiled ← modulesOf (repository / ".lake" / "build" / "lib" / "lean") "VeriMol" "olean"
  return tests ++ [
    test "VeriMol.lean imports VeriMol.Core and VeriMol.Proofs, and nothing else" imports libraries,
    test "VeriMol.lean contains only import lines" others [],
    test "every file under VeriMol/ belongs to VeriMol/Core/ or VeriMol/Proofs/"
      (sources.filter fun file => file != "VeriMol"
        && !libraries.any fun library => file == library || file.startsWith (library ++ ".")) [],
    test ("no compiled file under VeriMol/ is left over from a deleted or renamed file, and "
        ++ "compiled files are there (if this fails, run \"lake clean\" and then \"lake test\")")
      (compiled.filter (!sources.contains ·), compiled.isEmpty) ([], false),
    test ("no file of Core, Proofs, Main, Answers, Tests, TestData and the ledger sets an option "
        ++ "of Lean")
      (← filesThatHold holdsTheOptionWord repository) [],
    test ("no file of Core, Proofs, Main, Answers, Tests, TestData and the ledger holds the word "
        ++ "of a command that runs code while a file is built, or a line that begins with a "
        ++ "command with # (such as #print or #check)")
      (← filesThatHold holdsAWordThatRunsCode repository) [],
    ← independentCheck toCheck]

/-! ## Running everything -/

/-- How many of these tests failed. -/
def countFailed (tests : List Test) : Nat :=
  (tests.filter (!·.passed)).length

/-- Is a list of tests shorter than the least number that `main` writes down
for it? -/
def isTooShort (length least : Nat) : Bool :=
  length < least

/-- Is this test program itself broken? A test of two equal values must pass,
a test of two different values must fail, and of the two exactly one must be
counted as failed. If the function `test` let every test pass, or if no failed
test were counted, a wrong program would pass every test, and so would every
test of the test program that is made with these two functions. So `main` asks
here directly, and its exit code depends on the answer with nothing in
between.

The last three lines ask the same of two answers of the program, as the
program tests compare them: standard output, standard error and exit code.
The two answers differ in one of the three parts, in each part in turn. A
comparison that called any two answers equal, or that looked at one part
only, would let wrong answers pass their tests. (The audit refuses the one
way to get such a comparison that is known: an instance of `BEq` in Core.
These lines are a second net, and a coarse one: a comparison that is wrong
for other answers than these three is not seen here.) -/
def machineryIsBroken : Bool :=
  !(test "one is one" 1 1).passed || (test "one is two" 1 2).passed
    || countFailed [test "one is one" 1 1, test "one is two" 1 2] != 1
    || (test "two answers" ("CCO\n", "", 0) ("OCC\n", "", 0)).passed
    || (test "two answers" ("CCO\n", "", 0) ("CCO\n", "error: x\n", 0)).passed
    || (test "two answers" ("CCO\n", "", 0) ("CCO\n", "", 1)).passed

/-- Tests of this test program itself. The first three lines show what
`machineryIsBroken` asks; they could not make the run fail on their own, since
they are made with the functions that they try. The others try, on made-up
input, the checks of the repository, the least length of a list of tests, and
how the output of the second program is cut into answers and a list into
pieces. -/
def machineryTests : List Test := [
  test "a test of two equal values passes" (test "one is one" 1 1).passed true,
  test "a test of two different values fails" (test "one is two" 1 2).passed false,
  test "of a test that passes and one that fails, one is counted as failed"
    (countFailed [test "one is one" 1 1, test "one is two" 1 2]) 1,
  test "an import line is the word import and one name"
    (importedModule? "import VeriMol.Core.Mol".toList) (some "VeriMol.Core.Mol"),
  test "a line with anything else in it is no import line"
    (["import VeriMol.Core.Mol -- a comment", "import VeriMol.Core.Mol ", "import VeriMol.Core.Mol theorem x : False := id",
      "import", "import ", " import VeriMol.Core.Mol", "theorem x : True := trivial"].map
        fun line => importedModule? line.toList)
    [none, none, none, none, none, none, none],
  test "the word that sets an option is found in a text, and only where it stands"
    [holdsTheOptionWord ("set_" ++ "option autoImplicit true"),
      holdsTheOptionWord "theorem x : True := trivial"]
    [true, false],
  test "a list with fewer tests than its least number is too short, and one with as many is not"
    [isTooShort 5 10, isTooShort 10 10, isTooShort 0 1]
    [true, false, true],
  test ("the word of a command that runs code is found anywhere in a text, a command with # "
      ++ "at the beginning of a line as well, and nothing else")
    (["#" ++ "eval 1 + 1", "def x : Nat := 1 #" ++ "eval x", "open Nat in #" ++ "eval 1",
      "initial" ++ "ize counter : Nat ← pure 1", "run_" ++ "cmd pure ()",
      "#" ++ "guard x", "example : x := by run_" ++ "tac pure ()",
      "def x : Bool := true #" ++ "guard x", "def x := 1 #" ++ "exit",
      "open Nat in run_" ++ "elab pure ()", "open Nat in run_" ++ "meta pure ()",
      "def x := 1\n  #print axioms x", "def x := 1\n#check x",
      "# A heading", "## Smaller", "#", "def x := 1", "read \"C#N\".toList",
      "-- #print in a comment behind other text"].map holdsAWordThatRunsCode)
    [true, true, true, true, true, true, true, true, true, true, true, true, true,
      false, false, false, false, false, false],
  test ("what the second program prints is cut into its answers: a line with the exit code and "
      ++ "two numbers of bytes, then the two texts; bytes are counted, not characters; and "
      ++ "nothing is left behind them")
    (["0 4 0\nCCO\n1 0 9\nerror: x\n", "0 3 2\né\nü", "0 0 0\n"].map fun printed =>
      let (answers, left) := answersIn 5 printed.toList
      (answers, String.ofList left))
    [([("CCO\n", "", 0), ("", "error: x\n", 1)], ""), ([("é\n", "ü", 0)], ""), ([("", "", 0)], "")],
  test ("no more answers are taken than asked for, and none from where the text does not go on "
      ++ "as it must: it ends too early, a character lies across the end of a text, or the "
      ++ "line of numbers is not three numbers. What is not taken is handed back")
    ([(1, "0 4 0\nCCO\n1 0 9\nerror: x\n"), (5, "0 4 0\nCCO\n1 0 9\nerror"), (5, "0 1 0\né"),
      (5, "0 4\nCCO\n"), (5, "0 4 0 CCO\n"), (5, "zero 4 0\nCCO\n")].map fun (most, printed) =>
        let (answers, left) := answersIn most printed.toList
        (answers, String.ofList left))
    [([("CCO\n", "", 0)], "1 0 9\nerror: x\n"), ([("CCO\n", "", 0)], "1 0 9\nerror"),
      ([], "0 1 0\né"), ([], "0 4\nCCO\n"), ([], "0 4 0 CCO\n"), ([], "zero 4 0\nCCO\n")],
  test "a list is cut into pieces of a given size, and the last piece may be shorter"
    [inPieces 2 [1, 2, 3, 4, 5], inPieces 5 [1, 2, 3, 4, 5], inPieces 2 []]
    [[[1, 2], [3, 4], [5]], [[1, 2, 3, 4, 5]], []]]

/-- Prints how a list of tests went. A failing test is printed with all three
parts. A test that passes gets a line of its own, unless the list has a
title: then all that pass share one line. This only prints: `main` counts the
failed tests itself. -/
def report (tests : List Test) (title : Option String := none) : IO Unit := do
  let failed := countFailed tests
  for t in tests do
    if !t.passed then
      IO.println s!"FAIL  {t.name}"
      IO.println s!"        actual:   {t.actual}"
      IO.println s!"        expected: {t.expected}"
    else if title.isNone then
      IO.println s!"PASS  {t.name}"
  if let some title := title then
    if failed == 0 then
      IO.println s!"PASS  {title}: {tests.length} tests"
    else
      IO.println s!"FAIL  {title}: {failed} of {tests.length} tests failed"

/-- The executable `tests`. Runs every test and exits with code 1 if any test
failed. -/
def main : IO UInt32 := do
  -- The second program is asked for 1,000 lists of arguments in one start,
  -- which is the most that the long check gives it. A test of it also looks
  -- at how that start ended: with exit code 0, with nothing on the program's
  -- own standard error, and with nothing printed behind its answers.
  let mut ofTheProgram := []
  for piece in inPieces 1000 programTests do
    let (answers, ended) ← viaAnswers (piece.map fun (_, args, _) => args)
    for ((name, args, expected), place) in piece.zipIdx do
      ofTheProgram := ofTheProgram ++ [
        test s!"VeriMol.run: {name}" (viaCore args) expected,
        test s!"program:  {name}" (← viaBuilt "app" args) expected,
        test s!"answers:  {name}" (answers[place]?, ended) (some expected, 0, "", "")]
  -- What the second program must refuse. The expected values are worked out
  -- by hand from the comment at the head of `Answers.lean`.
  let refused := ("", "error: expected lists of arguments, each as the number of its arguments "
    ++ "followed by the arguments\n", 1)
  ofTheProgram := ofTheProgram ++ [
    test "answers:  a number with fewer arguments behind it than it says is refused"
      (← viaBuilt "answers" ["2", "CCO"]) refused,
    test "answers:  a text where a number must stand is refused"
      (← viaBuilt "answers" ["CCO"]) refused,
    test "answers:  a number that is not written with digits alone is refused"
      (← viaBuilt "answers" ["1_0", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]) refused]
  -- The expected values of these two are worked out by hand from SPEC.md,
  -- section 8: a line of Lean's own, and exit code 1.
  ofTheProgram := ofTheProgram ++ [
    test ("program:  app CCO with its standard output closed cannot write its answer: "
        ++ "a line of Lean's own, and exit code 1")
      (← viaProgramUnableToWrite ">&-" ["CCO"]) (true, 1)]
  -- A device that is always full exists on Linux. Where there is none, the
  -- test is left out, and a line says so.
  if ← System.FilePath.pathExists "/dev/full" then
    ofTheProgram := ofTheProgram ++ [
      test ("program:  app CCO into a device that is full cannot write its answer: "
          ++ "a line of Lean's own, and exit code 1")
        (← viaProgramUnableToWrite ">/dev/full" ["CCO"]) (true, 1)]
  else
    IO.println "left out: the test with a device that is full (this system has no /dev/full)"
  -- Each list with its name, whether its passing tests share one line, and
  -- the least number of tests it must hold. A list that has become empty, or
  -- much shorter, must not pass unnoticed. When tests are taken out on
  -- purpose, the number is lowered with them.
  let lists : List (List Test × String × Bool × Nat) := [
    (unitTests, "tests of single functions, written by hand", false, 35),
    (machineryTests, "tests of this test program itself", false, 11),
    (elementTests, "the elements and their symbols", true, 28),
    (molTests, "Mols: how they are printed, and whether they are well formed", true, 300),
    (cutTests, "texts cut into tokens", true, 1500),
    (spellTests, "tokens spelled as text", true, 1500),
    (readTests, "texts read as Mols", true, 100),
    (writeTests, "Mols written as text", true, 850),
    (filterTests, "Mols at the filter: sound or not, and their perfluorinated groups", true, 700),
    (ofTheProgram, "the whole program: as a function, as the built program, and through the "
      ++ "second program", true, 8700),
    (← repositoryChecks, "checks of the repository itself", false, 11)]
  let mut count := 0
  let mut failed := 0
  for (tests, name, oneLine, least) in lists do
    report tests (if oneLine then some name else none)
    failed := failed + countFailed tests
    count := count + tests.length
    if isTooShort tests.length least then
      IO.println (s!"FAIL  {name}: the list holds {tests.length} tests, and at least {least} "
        ++ "are expected")
      failed := failed + 1
  if machineryIsBroken then
    IO.println ("FAIL  this test program itself is broken: a test of two different values "
      ++ "passes, or a test of two equal values fails, or a failed test is not counted")
  IO.println s!"{count} tests, {failed} failed"
  return if failed == 0 && !machineryIsBroken then 0 else 1
