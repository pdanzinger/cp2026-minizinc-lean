
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
  var_x : (Array1d Int)

def cons₀ (m₀ : Model) : Prop := (m₀.var_x.dom0 = (Finset.Icc 1 3)) ∧ (∀ _i₂ ∈ m₀.var_x.dom0, (m₀.var_x.toFun _i₂) ∈ (Finset.Icc 1 3))
def cons₁ (m₀ : Model) : Prop := ((let _i₇ := m₀.var_x; let _i₈ := (Finset.Icc 1 3); (((∀ _i₉ : Int, _i₉ ∈ _i₈ → (_i₇.toFun _i₉) ∈ _i₈ ∧ ∀ _i₁₀ : Int, _i₁₀ ∈ _i₈ → (_i₇.toFun _i₁₀) ≠ _i₁₀) ∧ ∀ _i₁₁ : Int, ∀ _i₁₂ : Int, _i₁₁ ∈ _i₈ → _i₁₂ ∈ _i₈ → (_i₇.toFun _i₁₁) = (_i₇.toFun _i₁₂) → _i₁₁ = _i₁₂) ∧ ∀ _i₁₃ : Finset Int, _i₁₃ ⊆ _i₈ → _i₁₃.Nonempty → _i₁₃.card < _i₈.card → ∃ _i₁₄ : Int, _i₁₄ ∈ _i₁₃ ∧ (_i₇.toFun _i₁₄) ∉ _i₁₃)) ∧ (let _i₃ := m₀.var_x; let _i₄ := _i₃.dom0; ∀ _i₅ ∈ _i₄, ∀ _i₆ ∈ _i₄, _i₅ ≠ _i₆ → (_i₃.toFun _i₅) ≠ (_i₃.toFun _i₆)))
def cons₂ (m₀ : Model) : Prop := ((((¬(((((m₀.var_x.toFun 1 )) = 1) ∧ (((m₀.var_x.toFun 2 )) = 2)) ∧ (((m₀.var_x.toFun 3 )) = 3))) ∧ (¬(((((m₀.var_x.toFun 1 )) = 1) ∧ (((m₀.var_x.toFun 2 )) = 3)) ∧ (((m₀.var_x.toFun 3 )) = 2)))) ∧ (¬(((((m₀.var_x.toFun 1 )) = 2) ∧ (((m₀.var_x.toFun 2 )) = 1)) ∧ (((m₀.var_x.toFun 3 )) = 3)))) ∧ (¬(((((m₀.var_x.toFun 1 )) = 3) ∧ (((m₀.var_x.toFun 2 )) = 2)) ∧ (((m₀.var_x.toFun 3 )) = 1))))
def safe_cons₂ (m₀ : Model) : Prop := (((((1 ∈ ((Finset.Icc 1 3)) ∧ 2 ∈ ((Finset.Icc 1 3))) ∧ 3 ∈ ((Finset.Icc 1 3))) ∧ ((1 ∈ ((Finset.Icc 1 3)) ∧ 2 ∈ ((Finset.Icc 1 3))) ∧ 3 ∈ ((Finset.Icc 1 3)))) ∧ ((1 ∈ ((Finset.Icc 1 3)) ∧ 2 ∈ ((Finset.Icc 1 3))) ∧ 3 ∈ ((Finset.Icc 1 3)))) ∧ ((1 ∈ ((Finset.Icc 1 3)) ∧ 2 ∈ ((Finset.Icc 1 3))) ∧ 3 ∈ ((Finset.Icc 1 3))))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) : (cons₂ m₀) ∧ (safe_cons₂ m₀) := by
  sorry
