
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- These lines work to assume that every Prop is decidable. I.e. if p : Prop, then (decide p) will always work
open Classical
noncomputable section
classical



-- MiniZinc Array Types. Represents MiniZinc arrays of dimensions 1 through 4 in Lean.
-- The array contents are modelled by toFun, dom0 through domN are the array boundaries. Boundaries for accesses are enforced through safety formulas.

universe u

/-- Helper: product of a list of Nats. -/
def listProd : List Nat → Nat := List.foldl (· * ·) 1

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



-- The compiled MiniZinc model with the constraints to prove:


namespace Mzn

def bool2int (b : Prop) : Int := if b then (1 : Int) else (0 : Int)

def int2float (i : Int) : Float := Float.ofInt i

private def floatIntCast (y : Float) : Int :=
  if y < 0.0 then
    -Int.ofNat ((-y).toUInt64.toNat)
  else
    Int.ofNat (y.toUInt64.toNat)

def floatCeilToInt (x : Float) : Int := floatIntCast (Float.ceil x)
def floatFloorToInt (x : Float) : Int := floatIntCast (Float.floor x)
def floatRoundToInt (x : Float) : Int := floatIntCast (Float.round x)

private def foldFinsetInt {β : Type} (s : Finset Int) (init : β) (f : β → Int → β) : β :=
  (s.sort (· ≤ ·)).foldl f init

private def optMinFloat : Option Float → Option Float → Option Float
  | none, x => x
  | x, none => x
  | some a, some b => some (min a b)

private def optMaxFloat : Option Float → Option Float → Option Float
  | none, x => x
  | x, none => x
  | some a, some b => some (max a b)

def finsetMinOptFloat (s : Finset Int) (f : Int → Option Float) : Option Float :=
  foldFinsetInt s none (fun acc i => optMinFloat acc (f i))

def finsetMaxOptFloat (s : Finset Int) (f : Int → Option Float) : Option Float :=
  foldFinsetInt s none (fun acc i => optMaxFloat acc (f i))

def finsetSumFloat (s : Finset Int) (f : Int → Float) : Float :=
  foldFinsetInt s 0.0 (fun acc i => acc + f i)

end Mzn

structure Model where
  var_n : Int
  var_b : Int
  var_m : Int
  var_MACHINES : (Finset Int)
  var_empty_batch : (Array2d Int)
  var_l : Int
  var_TIMES : (Finset Int)
  var_a : Int
  var_ATTRIBUTES : (Finset Int)
  var_setup_costs : (Array2d Int)
  var_setup_costs_mod : (Array2d Int)
  var_setup_times : (Array2d Int)
  var_setup_times_mod : (Array2d Int)
  var_min_cap : (Array1d Int)
  var_max_cap : (Array1d Int)
  var_initState : (Array1d Int)
  var_s : Int
  var_m_a_s : (Array2d Int)
  var_m_a_e : (Array2d Int)
  var_m_a_s_mod : (Array2d Int)
  var_m_a_e_mod : (Array2d Int)
  var_eligible_machine : (Array1d (Finset Int))
  var_earliest_start : (Array1d Int)
  var_latest_end : (Array1d Int)
  var_min_time : (Array1d Int)
  var_max_time : (Array1d Int)
  var_size : (Array1d Int)
  var_attribute : (Array1d Int)
  var_upper_bound_integer_objective : Int
  var_mult_factor_total_runtime : Int
  var_mult_factor_finished_toolate : Int
  var_mult_factor_total_setuptimes : Int
  var_mult_factor_total_setupcosts : Int
  var_running_time_bound : Int
  var_min_duration : Int
  var_max_duration : Int
  var_max_setup_time : Int
  var_max_setup_cost : Int
  var_start_times : (Array2d Int)
  var_duration : (Array2d Int)
  var_job_in_batch : (Array3d Int)
  var_attribute_for_batch : (Array2d Int)
  var_setup_times_between_batches : (Array2d Int)
  var_setup_costs_between_batches : (Array2d Int)
  var_batch_in_shift : (Array3d Int)
  var_late_job : (Array3d Int)
  var_running_time_oven : Int
  var_finished_too_late : Int
  var_total_setup_costs : Int
  var_objective : Int
  var_batch_for_job : (Array1d Int)
  var_machine_for_job : (Array1d Int)

def cons₀ (m₀ : Model) : Prop := (m₀.var_b ∈ (Finset.Icc 1 m₀.var_n))
def cons₁ (m₀ : Model) : Prop := m₀.var_MACHINES = (Finset.Icc 1 m₀.var_m)
def cons₂ (m₀ : Model) : Prop := (m₀.var_empty_batch.dom0 = m₀.var_MACHINES) ∧ (m₀.var_empty_batch.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₄ _i₅, (m₀.var_empty_batch.toFun _i₄ _i₅) ∈ (Finset.Icc 0 1))
def cons₃ (m₀ : Model) : Prop := (m₀.var_b = (∑ var_ma ∈ m₀.var_MACHINES, ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), (1 - ((m₀.var_empty_batch.toFun var_ma var_ba )))))
def cons₄ (m₀ : Model) : Prop := m₀.var_TIMES = (Finset.Icc 0 m₀.var_l)
def cons₅ (m₀ : Model) : Prop := m₀.var_ATTRIBUTES = (Finset.Icc 0 m₀.var_a)
def cons₆ (m₀ : Model) : Prop := (m₀.var_setup_costs.dom0 = (Finset.Icc 1 (m₀.var_a + 1))) ∧ (m₀.var_setup_costs.dom1 = (Finset.Icc 1 m₀.var_a))
def cons₇ (m₀ : Model) : Prop := (m₀.var_setup_costs_mod.dom0 = (Finset.Icc 0 (m₀.var_a + 1))) ∧ (m₀.var_setup_costs_mod.dom1 = (Finset.Icc 0 m₀.var_a)) ∧ m₀.var_setup_costs_mod = (let _i₂₀ := (({toFun := (fun _i₂₁ => let _i₂₂ := _i₂₁ - 1; let var_j := 0 + (_i₂₂% (m₀.var_a - 0 + 1)); let _i₂₃ := Int.div _i₂₂ (m₀.var_a - 0 + 1); let var_i := 0 + (_i₂₃% ((m₀.var_a + 1) - 0 + 1)); let _i₂₄ := Int.div _i₂₃ ((m₀.var_a + 1) - 0 + 1); (if ((var_i >= 1) ∧ (var_j >= 1)) then ((m₀.var_setup_costs.toFun var_i var_j )) else 0)), dom0 := (Finset.Icc 1 (((m₀.var_a + 1) - 0 + 1)  * (m₀.var_a - 0 + 1) ))} : (Array1d Int))); ({toFun := fun _i₂₅ _i₂₆ => _i₂₀.toFun (((_i₂₅ - 0) * (m₀.var_a - 0 + 1) + (_i₂₆ - 0)) + _i₂₀.dom0.min.getD 0), dom0 := (Finset.Icc 0 (m₀.var_a + 1)), dom1 := (Finset.Icc 0 m₀.var_a)} : (Array2d Int)))
def cons₈ (m₀ : Model) : Prop := (m₀.var_setup_times.dom0 = (Finset.Icc 1 (m₀.var_a + 1))) ∧ (m₀.var_setup_times.dom1 = (Finset.Icc 1 m₀.var_a))
def cons₉ (m₀ : Model) : Prop := (m₀.var_setup_times_mod.dom0 = (Finset.Icc 0 (m₀.var_a + 1))) ∧ (m₀.var_setup_times_mod.dom1 = (Finset.Icc 0 m₀.var_a)) ∧ m₀.var_setup_times_mod = (let _i₄₃ := (({toFun := (fun _i₄₄ => let _i₄₅ := _i₄₄ - 1; let var_j := 0 + (_i₄₅% (m₀.var_a - 0 + 1)); let _i₄₆ := Int.div _i₄₅ (m₀.var_a - 0 + 1); let var_i := 0 + (_i₄₆% ((m₀.var_a + 1) - 0 + 1)); let _i₄₇ := Int.div _i₄₆ ((m₀.var_a + 1) - 0 + 1); (if ((var_i >= 1) ∧ (var_j >= 1)) then ((m₀.var_setup_times.toFun var_i var_j )) else 0)), dom0 := (Finset.Icc 1 (((m₀.var_a + 1) - 0 + 1)  * (m₀.var_a - 0 + 1) ))} : (Array1d Int))); ({toFun := fun _i₄₈ _i₄₉ => _i₄₃.toFun (((_i₄₈ - 0) * (m₀.var_a - 0 + 1) + (_i₄₉ - 0)) + _i₄₃.dom0.min.getD 0), dom0 := (Finset.Icc 0 (m₀.var_a + 1)), dom1 := (Finset.Icc 0 m₀.var_a)} : (Array2d Int)))
def cons₁₀ (m₀ : Model) : Prop := (m₀.var_min_cap.dom0 = (Finset.Icc 1 m₀.var_m))
def cons₁₁ (m₀ : Model) : Prop := (m₀.var_max_cap.dom0 = (Finset.Icc 1 m₀.var_m))
def cons₁₂ (m₀ : Model) : Prop := (m₀.var_initState.dom0 = m₀.var_MACHINES)
def cons₁₃ (m₀ : Model) : Prop := (m₀.var_m_a_s.dom0 = m₀.var_MACHINES) ∧ (m₀.var_m_a_s.dom1 = (Finset.Icc 1 m₀.var_s)) ∧ (∀ _i₅₆ _i₅₇, (m₀.var_m_a_s.toFun _i₅₆ _i₅₇) ∈ m₀.var_TIMES)
def cons₁₄ (m₀ : Model) : Prop := (m₀.var_m_a_e.dom0 = m₀.var_MACHINES) ∧ (m₀.var_m_a_e.dom1 = (Finset.Icc 1 m₀.var_s)) ∧ (∀ _i₆₂ _i₆₃, (m₀.var_m_a_e.toFun _i₆₂ _i₆₃) ∈ m₀.var_TIMES)
def cons₁₅ (m₀ : Model) : Prop := (m₀.var_m_a_s_mod.dom0 = m₀.var_MACHINES) ∧ (m₀.var_m_a_s_mod.dom1 = (Finset.Icc 1 (m₀.var_s + 1))) ∧ (∀ _i₈₂ _i₈₃, (m₀.var_m_a_s_mod.toFun _i₈₂ _i₈₃) ∈ m₀.var_TIMES) ∧ m₀.var_m_a_s_mod = (let _i₈₄ := (({toFun := (fun _i₈₅ => let _i₈₆ := _i₈₅ - 1; let var_j := 1 + (_i₈₆% ((m₀.var_s + 1) - 1 + 1)); let _i₈₇ := Int.div _i₈₆ ((m₀.var_s + 1) - 1 + 1); let var_ma := (m₀.var_MACHINES.min.getD 0) + (_i₈₇% ((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1)); let _i₈₈ := Int.div _i₈₇ ((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1); (if (var_j <= m₀.var_s) then ((m₀.var_m_a_s.toFun var_ma var_j )) else m₀.var_l)), dom0 := (Finset.Icc 1 (((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1)  * ((m₀.var_s + 1) - 1 + 1) ))} : (Array1d Int))); ({toFun := fun _i₈₉ _i₉₀ => _i₈₄.toFun (((_i₈₉ - (m₀.var_MACHINES.min.getD 0)) * ((m₀.var_s + 1) - 1 + 1) + (_i₉₀ - 1)) + _i₈₄.dom0.min.getD 0), dom0 := m₀.var_MACHINES, dom1 := (Finset.Icc 1 (m₀.var_s + 1))} : (Array2d Int)))
def cons₁₆ (m₀ : Model) : Prop := (m₀.var_m_a_e_mod.dom0 = m₀.var_MACHINES) ∧ (m₀.var_m_a_e_mod.dom1 = (Finset.Icc 1 (m₀.var_s + 1))) ∧ (∀ _i₁₁₁ _i₁₁₂, (m₀.var_m_a_e_mod.toFun _i₁₁₁ _i₁₁₂) ∈ m₀.var_TIMES) ∧ m₀.var_m_a_e_mod = (let _i₁₁₃ := (({toFun := (fun _i₁₁₄ => let _i₁₁₅ := _i₁₁₄ - 1; let var_j := 1 + (_i₁₁₅% ((m₀.var_s + 1) - 1 + 1)); let _i₁₁₆ := Int.div _i₁₁₅ ((m₀.var_s + 1) - 1 + 1); let var_ma := (m₀.var_MACHINES.min.getD 0) + (_i₁₁₆% ((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1)); let _i₁₁₇ := Int.div _i₁₁₆ ((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1); (if (var_j <= m₀.var_s) then ((m₀.var_m_a_e.toFun var_ma var_j )) else m₀.var_l)), dom0 := (Finset.Icc 1 (((m₀.var_MACHINES.max.getD 0) - (m₀.var_MACHINES.min.getD 0) + 1)  * ((m₀.var_s + 1) - 1 + 1) ))} : (Array1d Int))); ({toFun := fun _i₁₁₈ _i₁₁₉ => _i₁₁₃.toFun (((_i₁₁₈ - (m₀.var_MACHINES.min.getD 0)) * ((m₀.var_s + 1) - 1 + 1) + (_i₁₁₉ - 1)) + _i₁₁₃.dom0.min.getD 0), dom0 := m₀.var_MACHINES, dom1 := (Finset.Icc 1 (m₀.var_s + 1))} : (Array2d Int)))
def cons₁₇ (m₀ : Model) : Prop := (m₀.var_eligible_machine.dom0 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₂₄, (m₀.var_eligible_machine.toFun _i₁₂₄) ⊆ (Finset.Icc 1 m₀.var_m))
def cons₁₈ (m₀ : Model) : Prop := (m₀.var_earliest_start.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₁₉ (m₀ : Model) : Prop := (m₀.var_latest_end.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₂₀ (m₀ : Model) : Prop := (m₀.var_min_time.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₂₁ (m₀ : Model) : Prop := (m₀.var_max_time.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₂₂ (m₀ : Model) : Prop := (m₀.var_size.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₂₃ (m₀ : Model) : Prop := (m₀.var_attribute.dom0 = (Finset.Icc 1 m₀.var_n))
def cons₂₄ (m₀ : Model) : Prop := (m₀.var_start_times.dom0 = m₀.var_MACHINES) ∧ (m₀.var_start_times.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₂₉ _i₁₃₀, (m₀.var_start_times.toFun _i₁₂₉ _i₁₃₀) ∈ m₀.var_TIMES)
def cons₂₅ (m₀ : Model) : Prop := (m₀.var_duration.dom0 = m₀.var_MACHINES) ∧ (m₀.var_duration.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₃₅ _i₁₃₆, (m₀.var_duration.toFun _i₁₃₅ _i₁₃₆) ∈ (Finset.Icc 0 m₀.var_max_duration))
def cons₂₆ (m₀ : Model) : Prop := (m₀.var_job_in_batch.dom0 = m₀.var_MACHINES) ∧ (m₀.var_job_in_batch.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (m₀.var_job_in_batch.dom2 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₄₃ _i₁₄₄ _i₁₄₅, (m₀.var_job_in_batch.toFun _i₁₄₃ _i₁₄₄ _i₁₄₅) ∈ (Finset.Icc 0 1))
def cons₂₇ (m₀ : Model) : Prop := (m₀.var_attribute_for_batch.dom0 = m₀.var_MACHINES) ∧ (m₀.var_attribute_for_batch.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₅₀ _i₁₅₁, (m₀.var_attribute_for_batch.toFun _i₁₅₀ _i₁₅₁) ∈ m₀.var_ATTRIBUTES)
def cons₂₈ (m₀ : Model) : Prop := (m₀.var_setup_times_between_batches.dom0 = m₀.var_MACHINES) ∧ (m₀.var_setup_times_between_batches.dom1 = (Finset.Icc 1 (m₀.var_n - 1))) ∧ (∀ _i₁₅₆ _i₁₅₇, (m₀.var_setup_times_between_batches.toFun _i₁₅₆ _i₁₅₇) ∈ (Finset.Icc 0 m₀.var_max_setup_time))
def cons₂₉ (m₀ : Model) : Prop := (m₀.var_setup_costs_between_batches.dom0 = m₀.var_MACHINES) ∧ (m₀.var_setup_costs_between_batches.dom1 = (Finset.Icc 1 (m₀.var_n - 1))) ∧ (∀ _i₁₆₂ _i₁₆₃, (m₀.var_setup_costs_between_batches.toFun _i₁₆₂ _i₁₆₃) ∈ (Finset.Icc 0 m₀.var_max_setup_cost))
def cons₃₀ (m₀ : Model) : Prop := (m₀.var_batch_in_shift.dom0 = m₀.var_MACHINES) ∧ (m₀.var_batch_in_shift.dom1 = (Finset.Icc 1 m₀.var_n)) ∧ (m₀.var_batch_in_shift.dom2 = (Finset.Icc 1 (m₀.var_s + 1))) ∧ (∀ _i₁₇₀ _i₁₇₁ _i₁₇₂, (m₀.var_batch_in_shift.toFun _i₁₇₀ _i₁₇₁ _i₁₇₂) ∈ (Finset.Icc 0 1))
def cons₃₁ (m₀ : Model) : Prop := (m₀.var_late_job.dom0 = (Finset.Icc 1 m₀.var_n)) ∧ (m₀.var_late_job.dom1 = m₀.var_MACHINES) ∧ (m₀.var_late_job.dom2 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₇₉ _i₁₈₀ _i₁₈₁, (m₀.var_late_job.toFun _i₁₇₉ _i₁₈₀ _i₁₈₁) ∈ (Finset.Icc 0 1))
def cons₃₂ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ((∑ var_ma ∈ m₀.var_MACHINES, ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) = 1))
def cons₃₃ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ((∑ var_ma ∈ ((m₀.var_eligible_machine.toFun var_j )), ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) = 1))
def cons₃₄ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ((((m₀.var_attribute_for_batch.toFun var_ma var_ba )) <= ((((m₀.var_attribute.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) + (m₀.var_a * (1 - ((m₀.var_job_in_batch.toFun var_ma var_ba var_j )))))) ∧ (((m₀.var_attribute_for_batch.toFun var_ma var_ba )) >= (((m₀.var_attribute.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))))))
def cons₃₅ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((∑ var_j ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) >= (1 - ((m₀.var_empty_batch.toFun var_ma var_ba )))))
def cons₃₆ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_job_in_batch.toFun var_ma var_ba var_j )) <= (1 - ((m₀.var_empty_batch.toFun var_ma var_ba )))))
def cons₃₇ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 (m₀.var_n - 1)), (((m₀.var_empty_batch.toFun var_ma var_ba )) <= ((m₀.var_empty_batch.toFun var_ma (var_ba + 1) ))))
def cons₃₈ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_l * ((m₀.var_empty_batch.toFun var_ma var_ba ))) <= ((m₀.var_start_times.toFun var_ma var_ba ))))
def cons₃₉ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_max_duration * (1 - ((m₀.var_empty_batch.toFun var_ma var_ba )))) >= ((m₀.var_duration.toFun var_ma var_ba ))))
def cons₄₀ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_a * (1 - ((m₀.var_empty_batch.toFun var_ma var_ba )))) >= ((m₀.var_attribute_for_batch.toFun var_ma var_ba ))))
def cons₄₁ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_empty_batch.toFun var_ma var_ba )) <= ((m₀.var_batch_in_shift.toFun var_ma var_ba (m₀.var_s + 1) ))))
def cons₄₂ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_start_times.toFun var_ma var_ba )) >= (((m₀.var_earliest_start.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j )))))
def cons₄₃ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ((((m₀.var_duration.toFun var_ma var_ba )) >= (((m₀.var_min_time.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j )))) ∧ (((m₀.var_duration.toFun var_ma var_ba )) <= ((((m₀.var_max_time.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) + (m₀.var_max_duration * (1 - ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))))))))
def cons₄₄ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((∑ var_j ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_size.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j )))) <= ((m₀.var_max_cap.toFun var_ma ))))
def cons₄₅ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 (m₀.var_n - 1)), (let var_attr1 : Int := ((m₀.var_attribute_for_batch.toFun var_ma var_ba )); let var_attr2 : Int := ((m₀.var_attribute_for_batch.toFun var_ma (var_ba + 1) )); ((((m₀.var_setup_times_between_batches.toFun var_ma var_ba )) = ((m₀.var_setup_times_mod.toFun var_attr1 var_attr2 ))) ∧ (((m₀.var_setup_costs_between_batches.toFun var_ma var_ba )) = ((m₀.var_setup_costs_mod.toFun var_attr1 var_attr2 ))))))
def cons₄₆ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 (m₀.var_n - 1)), (((m₀.var_start_times.toFun var_ma (var_ba + 1) )) >= ((((m₀.var_start_times.toFun var_ma var_ba )) + ((m₀.var_duration.toFun var_ma var_ba ))) + ((m₀.var_setup_times_between_batches.toFun var_ma var_ba )))))
def cons₄₇ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((∑ var_j ∈ (Finset.Icc 1 (m₀.var_s + 1)), ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))) = 1))
def cons₄₈ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 (m₀.var_s + 1)), (((((m₀.var_m_a_s_mod.toFun var_ma var_j )) * ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))) <= ((m₀.var_start_times.toFun var_ma var_ba ))) ∧ (((m₀.var_start_times.toFun var_ma var_ba )) <= ((((m₀.var_m_a_e_mod.toFun var_ma var_j )) * ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))) + (m₀.var_l * (1 - ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))))))))
def cons₄₉ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 2 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 (m₀.var_s + 1)), ((((m₀.var_start_times.toFun var_ma var_ba )) - ((m₀.var_setup_times_between_batches.toFun var_ma (var_ba - 1) ))) >= (((m₀.var_m_a_s_mod.toFun var_ma var_j )) * ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j )))))
def cons₅₀ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_j ∈ (Finset.Icc 1 (m₀.var_s + 1)), ((((m₀.var_start_times.toFun var_ma 1 )) - ((m₀.var_setup_times_mod.toFun ((m₀.var_initState.toFun var_ma )) ((m₀.var_attribute_for_batch.toFun var_ma 1 )) ))) >= (((m₀.var_m_a_s_mod.toFun var_ma var_j )) * ((m₀.var_batch_in_shift.toFun var_ma 1 var_j )))))
def cons₅₁ (m₀ : Model) : Prop := (∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ∀ var_j ∈ (Finset.Icc 1 (m₀.var_s + 1)), ((((m₀.var_start_times.toFun var_ma var_ba )) + ((m₀.var_duration.toFun var_ma var_ba ))) <= (((1 - ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))) * m₀.var_l) + (((m₀.var_m_a_e_mod.toFun var_ma var_j )) * ((m₀.var_batch_in_shift.toFun var_ma var_ba var_j ))))))
def cons₅₂ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_late_job.toFun var_j var_ma var_ba )) <= ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))))
def cons₅₃ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((((((m₀.var_start_times.toFun var_ma var_ba )) + ((m₀.var_duration.toFun var_ma var_ba ))) - (((m₀.var_latest_end.toFun var_j )) * ((m₀.var_job_in_batch.toFun var_ma var_ba var_j )))) + (((m₀.var_late_job.toFun var_j var_ma var_ba )) * (((m₀.var_latest_end.toFun var_j )) - m₀.var_l))) <= ((1 - ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) * m₀.var_l)))
def cons₅₄ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ∀ var_ma ∈ m₀.var_MACHINES, ∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), (((((m₀.var_start_times.toFun var_ma var_ba )) + ((m₀.var_duration.toFun var_ma var_ba ))) - ((m₀.var_latest_end.toFun var_j ))) > ((1 - ((m₀.var_late_job.toFun var_j var_ma var_ba ))) * ((-m₀.var_l) - 1))))
def cons₅₅ (m₀ : Model) : Prop := (m₀.var_running_time_oven ∈ (Finset.Icc (m₀.var_min_duration * m₀.var_a) m₀.var_running_time_bound)) ∧ m₀.var_running_time_oven = (∑ var_ma ∈ m₀.var_MACHINES, ∑ var_i ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_duration.toFun var_ma var_i )))
def cons₅₆ (m₀ : Model) : Prop := (m₀.var_finished_too_late ∈ (Finset.Icc 0 m₀.var_n)) ∧ m₀.var_finished_too_late = (∑ var_j ∈ (Finset.Icc 1 m₀.var_n), ∑ var_ma ∈ m₀.var_MACHINES, ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_late_job.toFun var_j var_ma var_ba )))
def cons₅₇ (m₀ : Model) : Prop := (m₀.var_total_setup_costs ∈ (Finset.Icc 0 (m₀.var_n * m₀.var_max_setup_cost))) ∧ m₀.var_total_setup_costs = ((∑ _i₁₈₆ ∈ m₀.var_MACHINES, ∑ _i₁₈₇ ∈ (Finset.Icc 1 (m₀.var_n - 1)), (m₀.var_setup_costs_between_batches.toFun _i₁₈₆ _i₁₈₇ )) + (∑ var_ma ∈ m₀.var_MACHINES, ((m₀.var_setup_costs_mod.toFun ((m₀.var_initState.toFun var_ma )) ((m₀.var_attribute_for_batch.toFun var_ma 1 )) ))))
def cons₅₈ (m₀ : Model) : Prop := (m₀.var_objective ∈ (Finset.Icc 0 m₀.var_upper_bound_integer_objective)) ∧ m₀.var_objective = (((m₀.var_mult_factor_total_runtime * m₀.var_running_time_oven) + (m₀.var_mult_factor_finished_toolate * m₀.var_finished_too_late)) + (m₀.var_mult_factor_total_setupcosts * m₀.var_total_setup_costs))
def cons₅₉ (m₀ : Model) : Prop := (m₀.var_batch_for_job.dom0 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₁₉₄, (m₀.var_batch_for_job.toFun _i₁₉₄) ∈ (Finset.Icc 1 m₀.var_n)) ∧ m₀.var_batch_for_job = (let _i₁₉₅ := (({toFun := (fun var_j => (∑ var_ma ∈ m₀.var_MACHINES, ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_job_in_batch.toFun var_ma var_ba var_j )) * var_ba))), dom0 := (Finset.Icc 1 m₀.var_n)} : (Array1d Int))); ({toFun := fun _i₁₉₆ => _i₁₉₅.toFun ((_i₁₉₆ - 1) + _i₁₉₅.dom0.min.getD 0), dom0 := (Finset.Icc 1 m₀.var_n)} : (Array1d Int)))
def cons₆₀ (m₀ : Model) : Prop := (m₀.var_machine_for_job.dom0 = (Finset.Icc 1 m₀.var_n)) ∧ (∀ _i₂₀₄, (m₀.var_machine_for_job.toFun _i₂₀₄) ∈ m₀.var_MACHINES) ∧ m₀.var_machine_for_job = (let _i₂₀₅ := (({toFun := (fun var_j => (∑ var_ma ∈ m₀.var_MACHINES, ∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), (((m₀.var_job_in_batch.toFun var_ma var_ba var_j )) * var_ma))), dom0 := (Finset.Icc 1 m₀.var_n)} : (Array1d Int))); ({toFun := fun _i₂₀₆ => _i₂₀₅.toFun ((_i₂₀₆ - 1) + _i₂₀₅.dom0.min.getD 0), dom0 := (Finset.Icc 1 m₀.var_n)} : (Array1d Int)))
def cons₆₁ (m₀ : Model) : Prop := (∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ∀ var_ma ∈ m₀.var_MACHINES, (¬(var_ma ∈ ((m₀.var_eligible_machine.toFun var_j )))) -> ((∑ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((m₀.var_job_in_batch.toFun var_ma var_ba var_j ))) = 0))
def safe_cons₆₁ (m₀ : Model) : Prop := ∀ var_j ∈ (Finset.Icc 1 m₀.var_n), ∀ var_ma ∈ m₀.var_MACHINES, (∀ var_ba ∈ (Finset.Icc 1 m₀.var_n), ((var_ma ∈ (m₀.var_MACHINES) ∧ var_ba ∈ ((Finset.Icc 1 m₀.var_n))) ∧ var_j ∈ ((Finset.Icc 1 m₀.var_n))) ∧ var_j ∈ ((Finset.Icc 1 m₀.var_n)))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) (h₄: cons₄ m₀) (h₅: cons₅ m₀) (h₆: cons₆ m₀) (h₇: cons₇ m₀) (h₈: cons₈ m₀) (h₉: cons₉ m₀) (h₁₀: cons₁₀ m₀) (h₁₁: cons₁₁ m₀) (h₁₂: cons₁₂ m₀) (h₁₃: cons₁₃ m₀) (h₁₄: cons₁₄ m₀) (h₁₅: cons₁₅ m₀) (h₁₆: cons₁₆ m₀) (h₁₇: cons₁₇ m₀) (h₁₈: cons₁₈ m₀) (h₁₉: cons₁₉ m₀) (h₂₀: cons₂₀ m₀) (h₂₁: cons₂₁ m₀) (h₂₂: cons₂₂ m₀) (h₂₃: cons₂₃ m₀) (h₂₄: cons₂₄ m₀) (h₂₅: cons₂₅ m₀) (h₂₆: cons₂₆ m₀) (h₂₇: cons₂₇ m₀) (h₂₈: cons₂₈ m₀) (h₂₉: cons₂₉ m₀) (h₃₀: cons₃₀ m₀) (h₃₁: cons₃₁ m₀) (h₃₂: cons₃₂ m₀) (h₃₃: cons₃₃ m₀) (h₃₄: cons₃₄ m₀) (h₃₅: cons₃₅ m₀) (h₃₆: cons₃₆ m₀) (h₃₇: cons₃₇ m₀) (h₃₈: cons₃₈ m₀) (h₃₉: cons₃₉ m₀) (h₄₀: cons₄₀ m₀) (h₄₁: cons₄₁ m₀) (h₄₂: cons₄₂ m₀) (h₄₃: cons₄₃ m₀) (h₄₄: cons₄₄ m₀) (h₄₅: cons₄₅ m₀) (h₄₆: cons₄₆ m₀) (h₄₇: cons₄₇ m₀) (h₄₈: cons₄₈ m₀) (h₄₉: cons₄₉ m₀) (h₅₀: cons₅₀ m₀) (h₅₁: cons₅₁ m₀) (h₅₂: cons₅₂ m₀) (h₅₃: cons₅₃ m₀) (h₅₄: cons₅₄ m₀) (h₅₅: cons₅₅ m₀) (h₅₆: cons₅₆ m₀) (h₅₇: cons₅₇ m₀) (h₅₈: cons₅₈ m₀) (h₅₉: cons₅₉ m₀) (h₆₀: cons₆₀ m₀) : (cons₆₁ m₀) ∧ (safe_cons₆₁ m₀) := by
  sorry
