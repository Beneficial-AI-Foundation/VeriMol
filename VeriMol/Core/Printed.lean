import VeriMol.Core.Mol
import VeriMol.Core.Text

/-!
# How a `Mol` is printed (SPEC.md, section 7)

One fixed layout, which is also valid Lean:

    { atoms := [
        { element := .C, isotope := none, charge := 0, hydrogens := 3 },
        { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
      bonds := [
        { a := 0, b := 1, order := .single } ],
      orientations := [],
      geometries := [] }

The functions here only build the text. Printing it is the job of `Main`.
-/

namespace VeriMol

/-- The name of a kind of bond, as its Lean case is called. -/
def BondOrder.name : BondOrder → List Char
  | .single    => "single".toList
  | .double    => "double".toList
  | .triple    => "triple".toList
  | .quadruple => "quadruple".toList
  | .aromatic  => "aromatic".toList

/-- One atom with all four fields, on one line. -/
def Atom.printed (x : Atom) : List Char :=
  "{ element := .".toList ++ x.element.symbol
    ++ ", isotope := ".toList ++
      (match x.isotope with
        | none => "none".toList
        | some n => "some ".toList ++ natText n)
    ++ ", charge := ".toList ++ intText x.charge
    ++ ", hydrogens := ".toList ++ natText x.hydrogens
    ++ " }".toList

/-- One bond with all three fields, on one line. -/
def Bond.printed (x : Bond) : List Char :=
  "{ a := ".toList ++ natText x.a
    ++ ", b := ".toList ++ natText x.b
    ++ ", order := .".toList ++ x.order.name
    ++ " }".toList

/-- One atom that has an orientation, on one line. -/
def AtomOrientation.printed (x : AtomOrientation) : List Char :=
  "{ atom := ".toList ++ natText x.atom
    ++ ", orientation := .".toList ++
      (match x.orientation with
        | .anticlockwise => "anticlockwise".toList
        | .clockwise => "clockwise".toList)
    ++ " }".toList

/-- One double bond that has a geometry, on one line. -/
def BondGeometry.printed (x : BondGeometry) : List Char :=
  "{ a := ".toList ++ natText x.a
    ++ ", b := ".toList ++ natText x.b
    ++ ", geometry := .".toList ++
      (match x.geometry with
        | .sameSide => "sameSide".toList
        | .oppositeSides => "oppositeSides".toList)
    ++ " }".toList

/-- A list in the layout. An empty list is `[]`. Otherwise every item stands on
a line of its own, indented by four spaces, with a comma after every line but
the last. -/
def printedList : List (List Char) → List Char
  | [] => "[]".toList
  | items =>
    "[\n".toList ++ ",\n".toList.intercalate (items.map ("    ".toList ++ ·)) ++ " ]".toList

/-- The whole `Mol` in the layout, ending with a line break. -/
def Mol.printed (m : Mol) : List Char :=
  "{ atoms := ".toList ++ printedList (m.atoms.map Atom.printed)
    ++ ",\n  bonds := ".toList ++ printedList (m.bonds.map Bond.printed)
    ++ ",\n  orientations := ".toList ++ printedList (m.orientations.map AtomOrientation.printed)
    ++ ",\n  geometries := ".toList ++ printedList (m.geometries.map BondGeometry.printed)
    ++ " }\n".toList

end VeriMol
