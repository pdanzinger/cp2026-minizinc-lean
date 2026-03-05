
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- These lines work to assume that every Prop is decidable. I.e. if p : Prop, then (decide p) will always work
open Classical
noncomputable section
classical



-- MiniZinc Array Types. Represents MiniZinc arrays of dimensions 1 through 8 in Lean.
-- The array contents are modelled by toFun, dom0 through domN are the array boundaries. Boundaries for accesses are enforced through safety formulas.

universe u

/-- Helper: product of a list of Nats. -/
def listProd : List Nat → Nat := List.foldl (· * ·) 1

/-- Nonempty contiguous finite integer set. -/
def mzIsContiguousIntSet (s : Finset Int) : Prop :=
    0 < s.card ∧ Int.ofNat s.card = (s.max.getD 0 - s.min.getD 0 + 1)

/-- 1D array with element type α. -/
structure Array1d (α : Type u) where
    dom0  : Finset Int
    toFun : Int → α

/-- 2D array with element type α. -/
structure Array2d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    toFun : Int → Int → α

/-- 3D array with element type α. -/
structure Array3d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    toFun : Int → Int → Int → α

/-- 4D array with element type α. -/
structure Array4d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    toFun : Int → Int → Int → Int → α

/-- 5D array with element type α. -/
structure Array5d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    toFun : Int → Int → Int → Int → Int → α

/-- 6D array with element type α. -/
structure Array6d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → α

/-- 7D array with element type α. -/
structure Array7d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → α

/-- 8D array with element type α. -/
structure Array8d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    dom7  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → Int → α

namespace Array1d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array1d α) : Nat :=
    listProd [a.dom0.card]

end Array1d

namespace Array2d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array2d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card]

end Array2d

namespace Array3d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array3d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card]

end Array3d

namespace Array4d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array4d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card]

end Array4d

namespace Array5d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array5d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card]

end Array5d

namespace Array6d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array6d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card]

end Array6d

namespace Array7d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array7d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card]

end Array7d

namespace Array8d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array8d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card, a.dom7.card]

end Array8d

-- Other definitions:

def mz_bool2int (b : Prop) : Int := if b then (1 : Int) else (0 : Int)

-- The compiled MiniZinc model with the constraints to prove:

structure Model where
  var_A : (Array1d Int)
  var_B : (Array2d Int)

def cons₀ (m₀ : Model) : Prop := (m₀.var_A.dom0 = (Finset.Icc 2 4)) ∧ m₀.var_A = (let _i₆ := (({toFun := (fun (_i₇ : Int) => match _i₇ with  | (1 : Int) => 5 | (2 : Int) => 6 | (3 : Int) => 7 | _ => 5), dom0 := (Finset.Icc 1 3)} : (Array1d Int))); ({toFun := fun _i₈ => _i₆.toFun ((_i₈ - 2) + _i₆.dom0.min.getD 0), dom0 := (Finset.Icc 2 4)} : (Array1d Int)))
def cons₁ (m₀ : Model) : Prop := (m₀.var_B.dom0 = (Finset.Icc 1 2)) ∧ (m₀.var_B.dom1 = (Finset.Icc 1 2)) ∧ m₀.var_B = (let _i₁₈ := (({toFun := (fun (_i₁₉ : Int) => match _i₁₉ with  | (1 : Int) => 1 | (2 : Int) => 2 | (3 : Int) => 3 | (4 : Int) => 4 | _ => 1), dom0 := (Finset.Icc 1 4)} : (Array1d Int))); ({toFun := fun _i₂₀ _i₂₁ => _i₁₈.toFun (((_i₂₀ - 1) * (2 - 1 + 1) + (_i₂₁ - 1)) + _i₁₈.dom0.min.getD 0), dom0 := (Finset.Icc 1 2), dom1 := (Finset.Icc 1 2)} : (Array2d Int)))
def cons₂ (m₀ : Model) : Prop := ((Int.ofNat (Array1d.size m₀.var_A)) = 3)

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) : (cons₂ m₀) := by
  
  rcases h₀ with ⟨hA_dom, _⟩
  -- unfold the definition of size and the list product
  have : Int.ofNat (listProd [m₀.var_A.dom0.card]) = 3 := by
    -- replace the domain by the known interval
    simpa [hA_dom, Array1d.size, listProd] using
      (by
        have : (Finset.Icc (2 : Int) 4).card = 3 := by
          simp [Finset.card_Icc]
        simpa [this])
  simpa [Array1d.size] using this
