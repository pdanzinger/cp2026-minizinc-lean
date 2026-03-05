
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
  var_C : (Array1d Int)
  var_L : (Array1d Int)
  var_B0 : (Array1d Int)
  var_A3 : (Array3d Int)
  var_S0 : (Array1d Int)
  var_A6 : (Array6d Int)

def cons₀ (m₀ : Model) : Prop := (m₀.var_C.dom0 = (Finset.Icc 1 4)) ∧ m₀.var_C = (({toFun := (fun _i₈ => (let _i₉ := _i₈ - 1; let var_j := 1 + (_i₉ % (2 - 1 + 1)); let _i₁₀ := Int.div _i₉ (2 - 1 + 1); let var_i := 1 + (_i₁₀ % (2 - 1 + 1)); let _i₁₁ := Int.div _i₁₀ (2 - 1 + 1); (var_i + var_j))), dom0 := (Finset.Icc 1 ((2 - 1 + 1)  * (2 - 1 + 1) ))} : (Array1d Int)))
def cons₁ (m₀ : Model) : Prop := (m₀.var_L.dom0 = (Finset.Icc 1 11)) ∧ m₀.var_L = (({toFun := (fun _i₁₇ => let __data : Array Int := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; Option.getD (__data.get? (Int.toNat (_i₁₇ - 1))) (1)), dom0 := (Finset.Icc 1 11)} : (Array1d Int)))
def cons₂ (m₀ : Model) : Prop := (m₀.var_B0.dom0 = (Finset.Icc 1 8)) ∧ m₀.var_B0 = (({toFun := (fun (_i₂₀ : Int) => match _i₂₀ with  | (1 : Int) => 1 | (2 : Int) => 2 | (3 : Int) => 3 | (4 : Int) => 4 | (5 : Int) => 5 | (6 : Int) => 6 | (7 : Int) => 7 | (8 : Int) => 8 | _ => 1), dom0 := (Finset.Icc 1 8)} : (Array1d Int)))
def cons₃ (m₀ : Model) : Prop := (m₀.var_A3.dom0 = (Finset.Icc 1 2)) ∧ (m₀.var_A3.dom1 = (Finset.Icc 1 2)) ∧ (m₀.var_A3.dom2 = (Finset.Icc 1 2)) ∧ m₀.var_A3 = (let _i₂₉ := m₀.var_B0; ({toFun := fun _i₃₀ _i₃₁ _i₃₂ => _i₂₉.toFun ((((_i₃₀ - 1) * (2 - 1 + 1) + (_i₃₁ - 1)) * (2 - 1 + 1) + (_i₃₂ - 1)) + _i₂₉.dom0.min.getD 0), dom0 := (Finset.Icc 1 2), dom1 := (Finset.Icc 1 2), dom2 := (Finset.Icc 1 2)} : (Array3d Int)))
def cons₄ (m₀ : Model) : Prop := (m₀.var_S0.dom0 = (Finset.Icc 1 1)) ∧ m₀.var_S0 = (({toFun := (fun (_i₃₈ : Int) => match _i₃₈ with  | (1 : Int) => 42 | _ => 42), dom0 := (Finset.Icc 1 1)} : (Array1d Int)))
def cons₅ (m₀ : Model) : Prop := (m₀.var_A6.dom0 = (Finset.Icc 1 1)) ∧ (m₀.var_A6.dom1 = (Finset.Icc 1 1)) ∧ (m₀.var_A6.dom2 = (Finset.Icc 1 1)) ∧ (m₀.var_A6.dom3 = (Finset.Icc 1 1)) ∧ (m₀.var_A6.dom4 = (Finset.Icc 1 1)) ∧ (m₀.var_A6.dom5 = (Finset.Icc 1 1)) ∧ m₀.var_A6 = (let _i₅₃ := m₀.var_S0; ({toFun := fun _i₅₄ _i₅₅ _i₅₆ _i₅₇ _i₅₈ _i₅₉ => _i₅₃.toFun (((((((_i₅₄ - 1) * (1 - 1 + 1) + (_i₅₅ - 1)) * (1 - 1 + 1) + (_i₅₆ - 1)) * (1 - 1 + 1) + (_i₅₇ - 1)) * (1 - 1 + 1) + (_i₅₈ - 1)) * (1 - 1 + 1) + (_i₅₉ - 1)) + _i₅₃.dom0.min.getD 0), dom0 := (Finset.Icc 1 1), dom1 := (Finset.Icc 1 1), dom2 := (Finset.Icc 1 1), dom3 := (Finset.Icc 1 1), dom4 := (Finset.Icc 1 1), dom5 := (Finset.Icc 1 1)} : (Array6d Int)))
def cons₆ (m₀ : Model) : Prop := (((m₀.var_A6.toFun 1 1 1 1 1 1 )) = 42)
def safe_cons₆ (m₀ : Model) : Prop := (((((1 ∈ ((Finset.Icc 1 1)) ∧ 1 ∈ ((Finset.Icc 1 1))) ∧ 1 ∈ ((Finset.Icc 1 1))) ∧ 1 ∈ ((Finset.Icc 1 1))) ∧ 1 ∈ ((Finset.Icc 1 1))) ∧ 1 ∈ ((Finset.Icc 1 1)))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) (h₄: cons₄ m₀) (h₅: cons₅ m₀) : (cons₆ m₀) ∧ (safe_cons₆ m₀) := by
  
  constructor
  · unfold cons₆
    rcases h₅ with ⟨_, _, _, _, _, _, h5_eq⟩
    rcases h₄ with ⟨_, h4_eq⟩
    rw [h5_eq, h4_eq]
    simp only [Array1d.toFun, Array6d.toFun]
    have h_min : (Finset.Icc (1 : Int) 1).min = some 1 := by decide
    rw [h_min]
    norm_num
  · unfold safe_cons₆
    simp
