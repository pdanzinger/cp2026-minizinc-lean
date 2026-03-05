
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
  var_T : Int
  var_V : Int
  var_Q : Int
  var_L : Int
  var_C : Int
  var_P : Int
  var_TIME : (Finset Int)
  var_VEHICLES : (Finset Int)
  var_LOAD : (Finset Int)
  var_NEGLOAD : (Finset Int)
  var_LOCATIONS : (Finset Int)
  var_R : Int
  var_N : Int
  var_PICKUPS : (Finset Int)
  var_DELIVERIES : (Finset Int)
  var_REQUESTS : (Finset Int)
  var_NODES : (Finset Int)
  var_RSNODES : (Finset Int)
  var_SENODES : (Finset Int)
  var_time : (Array2d Int)
  var_l : (Array1d Int)
  var_a : (Array1d Int)
  var_b : (Array1d Int)
  var_s : (Array1d Int)
  var_q : (Array1d Int)
  var_qq : (Array1d Int)
  var_min_obj : Int
  var_max_obj : Int
  var_objective : Int
  var_veh : (Array1d Int)
  var_succ : (Array1d Int)
  var_load : (Array1d Int)
  var_arr : (Array1d Int)
  var_ser : (Array1d Int)
  var_dep : (Array1d Int)

def cons₀ (m₀ : Model) : Prop := (m₀.var_T >= 0)
def cons₁ (m₀ : Model) : Prop := (m₀.var_V >= 0)
def cons₂ (m₀ : Model) : Prop := (m₀.var_Q >= 0)
def cons₃ (m₀ : Model) : Prop := (m₀.var_L >= 0)
def cons₄ (m₀ : Model) : Prop := (m₀.var_C >= 0)
def cons₅ (m₀ : Model) : Prop := (m₀.var_P >= 0)
def cons₆ (m₀ : Model) : Prop := m₀.var_TIME = (Finset.Icc 0 m₀.var_T)
def cons₇ (m₀ : Model) : Prop := m₀.var_VEHICLES = (Finset.Icc 1 m₀.var_V)
def cons₈ (m₀ : Model) : Prop := m₀.var_LOAD = (Finset.Icc 0 m₀.var_Q)
def cons₉ (m₀ : Model) : Prop := m₀.var_NEGLOAD = (Finset.Icc (-m₀.var_Q) m₀.var_Q)
def cons₁₀ (m₀ : Model) : Prop := m₀.var_LOCATIONS = (Finset.Icc 1 m₀.var_L)
def cons₁₁ (m₀ : Model) : Prop := m₀.var_R = (2 * m₀.var_P)
def cons₁₂ (m₀ : Model) : Prop := m₀.var_N = (m₀.var_R + (2 * m₀.var_V))
def cons₁₃ (m₀ : Model) : Prop := m₀.var_PICKUPS = (Finset.Icc 1 m₀.var_P)
def cons₁₄ (m₀ : Model) : Prop := m₀.var_DELIVERIES = (Finset.Icc (m₀.var_P + 1) m₀.var_R)
def cons₁₅ (m₀ : Model) : Prop := m₀.var_REQUESTS = (Finset.Icc 1 m₀.var_R)
def cons₁₆ (m₀ : Model) : Prop := m₀.var_NODES = (Finset.Icc 1 m₀.var_N)
def cons₁₇ (m₀ : Model) : Prop := m₀.var_RSNODES = (Finset.Icc 1 (m₀.var_R + m₀.var_V))
def cons₁₈ (m₀ : Model) : Prop := m₀.var_SENODES = (Finset.Icc (m₀.var_R + 1) m₀.var_N)
def cons₁₉ (m₀ : Model) : Prop := (m₀.var_time.dom0 = m₀.var_NODES) ∧ (m₀.var_time.dom1 = m₀.var_NODES) ∧ (∀ _i₄ _i₅, (m₀.var_time.toFun _i₄ _i₅) ∈ m₀.var_TIME)
def cons₂₀ (m₀ : Model) : Prop := (m₀.var_l.dom0 = m₀.var_REQUESTS) ∧ (∀ _i₈, (m₀.var_l.toFun _i₈) ∈ m₀.var_LOCATIONS)
def cons₂₁ (m₀ : Model) : Prop := (m₀.var_a.dom0 = m₀.var_REQUESTS) ∧ (∀ _i₁₁, (m₀.var_a.toFun _i₁₁) ∈ m₀.var_TIME)
def cons₂₂ (m₀ : Model) : Prop := (m₀.var_b.dom0 = m₀.var_REQUESTS) ∧ (∀ _i₁₄, (m₀.var_b.toFun _i₁₄) ∈ m₀.var_TIME)
def cons₂₃ (m₀ : Model) : Prop := (m₀.var_s.dom0 = m₀.var_REQUESTS) ∧ (∀ _i₁₇, (m₀.var_s.toFun _i₁₇) ∈ m₀.var_TIME)
def cons₂₄ (m₀ : Model) : Prop := (m₀.var_q.dom0 = m₀.var_REQUESTS) ∧ (∀ _i₂₀, (m₀.var_q.toFun _i₂₀) ∈ m₀.var_NEGLOAD)
def cons₂₅ (m₀ : Model) : Prop := (m₀.var_qq.dom0 = m₀.var_NODES) ∧ (∀ _i₂₃, (m₀.var_qq.toFun _i₂₃) ∈ m₀.var_NEGLOAD) ∧ m₀.var_qq = (({toFun := (fun var_i => (if (var_i ∈ m₀.var_REQUESTS) then ((m₀.var_q.toFun var_i )) else 0)), dom0 := m₀.var_NODES} : (Array1d Int)))
def cons₂₆ (m₀ : Model) : Prop := m₀.var_min_obj = ((Int.ofNat (m₀.var_RSNODES.card)) * ((m₀.var_TIME.min.getD 0)))
def cons₂₇ (m₀ : Model) : Prop := m₀.var_max_obj = ((Int.ofNat (m₀.var_RSNODES.card)) * ((m₀.var_TIME.max.getD 0)))
def cons₂₈ (m₀ : Model) : Prop := (m₀.var_objective ∈ (Finset.Icc m₀.var_min_obj m₀.var_max_obj))
def cons₂₉ (m₀ : Model) : Prop := (m₀.var_veh.dom0 = m₀.var_NODES) ∧ (∀ _i₂₆, (m₀.var_veh.toFun _i₂₆) ∈ m₀.var_VEHICLES)
def cons₃₀ (m₀ : Model) : Prop := (m₀.var_succ.dom0 = m₀.var_NODES) ∧ (∀ _i₂₉, (m₀.var_succ.toFun _i₂₉) ∈ m₀.var_NODES)
def cons₃₁ (m₀ : Model) : Prop := (m₀.var_load.dom0 = m₀.var_NODES) ∧ (∀ _i₃₂, (m₀.var_load.toFun _i₃₂) ∈ m₀.var_LOAD)
def cons₃₂ (m₀ : Model) : Prop := (m₀.var_arr.dom0 = m₀.var_NODES) ∧ (∀ _i₃₅, (m₀.var_arr.toFun _i₃₅) ∈ m₀.var_TIME)
def cons₃₃ (m₀ : Model) : Prop := (m₀.var_ser.dom0 = m₀.var_NODES) ∧ (∀ _i₃₈, (m₀.var_ser.toFun _i₃₈) ∈ m₀.var_TIME)
def cons₃₄ (m₀ : Model) : Prop := (m₀.var_dep.dom0 = m₀.var_NODES) ∧ (∀ _i₄₁, (m₀.var_dep.toFun _i₄₁) ∈ m₀.var_TIME)
def cons₃₅ (m₀ : Model) : Prop := (let _i₄₂ := m₀.var_succ; let _i₄₃ := m₀.var_NODES; (((∀ _i₄₄ : Int, _i₄₄ ∈ _i₄₃ → (_i₄₂.toFun _i₄₄) ∈ _i₄₃ ∧ ∀ _i₄₅ : Int, _i₄₅ ∈ _i₄₃ → (_i₄₂.toFun _i₄₅) ≠ _i₄₅) ∧ ∀ _i₄₆ : Int, ∀ _i₄₇ : Int, _i₄₆ ∈ _i₄₃ → _i₄₇ ∈ _i₄₃ → (_i₄₂.toFun _i₄₆) = (_i₄₂.toFun _i₄₇) → _i₄₆ = _i₄₇) ∧ ∀ _i₄₈ : Finset Int, _i₄₈ ⊆ _i₄₃ → _i₄₈.Nonempty → _i₄₈.card < _i₄₃.card → ∃ _i₄₉ : Int, _i₄₉ ∈ _i₄₈ ∧ (_i₄₂.toFun _i₄₉) ∉ _i₄₈))
def cons₃₆ (m₀ : Model) : Prop := (∀ var_v ∈ (Finset.Icc 1 (m₀.var_V - 1)), (((m₀.var_succ.toFun ((m₀.var_R + m₀.var_V) + var_v) )) = (m₀.var_R + (var_v + 1))))
def cons₃₇ (m₀ : Model) : Prop := (((m₀.var_succ.toFun ((m₀.var_R + m₀.var_V) + m₀.var_V) )) = (m₀.var_R + 1))
def cons₃₈ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_RSNODES, (((m₀.var_veh.toFun var_i )) = ((m₀.var_veh.toFun ((m₀.var_succ.toFun var_i )) ))))
def cons₃₉ (m₀ : Model) : Prop := (∀ var_v ∈ m₀.var_VEHICLES, (((m₀.var_veh.toFun (m₀.var_R + var_v) )) = var_v))
def cons₄₀ (m₀ : Model) : Prop := (∀ var_v ∈ m₀.var_VEHICLES, (((m₀.var_veh.toFun ((m₀.var_R + m₀.var_V) + var_v) )) = var_v))
def cons₄₁ (m₀ : Model) : Prop := (((∀ var_v ∈ (Finset.Icc 1 (m₀.var_V - 1)), ((((m₀.var_succ.toFun (m₀.var_R + var_v) )) = ((m₀.var_R + m₀.var_V) + var_v)) -> (((m₀.var_succ.toFun (m₀.var_R + (var_v + 1)) )) = ((m₀.var_R + m₀.var_V) + (var_v + 1))))) ∧ (((m₀.var_veh.toFun 1 )) = 1)))
def cons₄₂ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_REQUESTS, (((m₀.var_arr.toFun var_i )) <= ((m₀.var_ser.toFun var_i ))))
def cons₄₃ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_REQUESTS, ((((m₀.var_ser.toFun var_i )) + ((m₀.var_s.toFun var_i ))) <= ((m₀.var_dep.toFun var_i ))))
def cons₄₄ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_REQUESTS, ((((m₀.var_a.toFun var_i )) <= ((m₀.var_ser.toFun var_i ))) ∧ (((m₀.var_ser.toFun var_i )) <= ((m₀.var_b.toFun var_i )))))
def cons₄₅ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_SENODES, (((m₀.var_arr.toFun var_i )) = ((m₀.var_ser.toFun var_i ))))
def cons₄₆ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_SENODES, (((m₀.var_ser.toFun var_i )) = ((m₀.var_dep.toFun var_i ))))
def cons₄₇ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_RSNODES, ((((m₀.var_dep.toFun var_i )) + ((m₀.var_time.toFun var_i ((m₀.var_succ.toFun var_i )) ))) = ((m₀.var_arr.toFun ((m₀.var_succ.toFun var_i )) ))))
def cons₄₈ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_RSNODES, ((((m₀.var_load.toFun var_i )) + ((m₀.var_qq.toFun ((m₀.var_succ.toFun var_i )) ))) = ((m₀.var_load.toFun ((m₀.var_succ.toFun var_i )) ))))
def cons₄₉ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_SENODES, (((m₀.var_load.toFun var_i )) = 0))
def cons₅₀ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_PICKUPS, ((((m₀.var_dep.toFun var_i )) + ((m₀.var_time.toFun var_i (m₀.var_P + var_i) ))) <= ((m₀.var_arr.toFun (m₀.var_P + var_i) ))))
def cons₅₁ (m₀ : Model) : Prop := (∀ var_i ∈ m₀.var_PICKUPS, (((m₀.var_veh.toFun var_i )) = ((m₀.var_veh.toFun (m₀.var_P + var_i) ))))
def cons₅₂ (m₀ : Model) : Prop := (∀ var_ll ∈ m₀.var_LOCATIONS, (∀ _i₅₀, (∑ _i₅₁ ∈ m₀.var_REQUESTS, if (let var_i := _i₅₁; ((m₀.var_ser.toFun var_i ))) <= _i₅₀ /\ (let var_i := _i₅₁; ((m₀.var_ser.toFun var_i ))) + (m₀.var_s.toFun _i₅₁ ) > _i₅₀ then (let var_i := _i₅₁; (Mzn.bool2int (((m₀.var_l.toFun var_i )) = var_ll))) else 0) <= m₀.var_C))
def cons₅₃ (m₀ : Model) : Prop := (m₀.var_objective = (∑ var_i ∈ m₀.var_RSNODES, ((m₀.var_time.toFun var_i ((m₀.var_succ.toFun var_i )) ))))
def cons₅₄ (m₀ : Model) : Prop := (m₀.var_objective = (∑ var_i ∈ m₀.var_RSNODES, (((m₀.var_arr.toFun ((m₀.var_succ.toFun var_i )) )) - ((m₀.var_dep.toFun var_i )))))
def safe_cons₅₄ (m₀ : Model) : Prop := ∀ var_i ∈ m₀.var_RSNODES, ((var_i ∈ (m₀.var_NODES) ∧ ((m₀.var_succ.toFun var_i )) ∈ (m₀.var_NODES)) ∧ var_i ∈ (m₀.var_NODES))

theorem theorem_redundant (m₀: Model) (h₀: cons₀ m₀) (h₁: cons₁ m₀) (h₂: cons₂ m₀) (h₃: cons₃ m₀) (h₄: cons₄ m₀) (h₅: cons₅ m₀) (h₆: cons₆ m₀) (h₇: cons₇ m₀) (h₈: cons₈ m₀) (h₉: cons₉ m₀) (h₁₀: cons₁₀ m₀) (h₁₁: cons₁₁ m₀) (h₁₂: cons₁₂ m₀) (h₁₃: cons₁₃ m₀) (h₁₄: cons₁₄ m₀) (h₁₅: cons₁₅ m₀) (h₁₆: cons₁₆ m₀) (h₁₇: cons₁₇ m₀) (h₁₈: cons₁₈ m₀) (h₁₉: cons₁₉ m₀) (h₂₀: cons₂₀ m₀) (h₂₁: cons₂₁ m₀) (h₂₂: cons₂₂ m₀) (h₂₃: cons₂₃ m₀) (h₂₄: cons₂₄ m₀) (h₂₅: cons₂₅ m₀) (h₂₆: cons₂₆ m₀) (h₂₇: cons₂₇ m₀) (h₂₈: cons₂₈ m₀) (h₂₉: cons₂₉ m₀) (h₃₀: cons₃₀ m₀) (h₃₁: cons₃₁ m₀) (h₃₂: cons₃₂ m₀) (h₃₃: cons₃₃ m₀) (h₃₄: cons₃₄ m₀) (h₃₅: cons₃₅ m₀) (h₃₆: cons₃₆ m₀) (h₃₇: cons₃₇ m₀) (h₃₈: cons₃₈ m₀) (h₃₉: cons₃₉ m₀) (h₄₀: cons₄₀ m₀) (h₄₁: cons₄₁ m₀) (h₄₂: cons₄₂ m₀) (h₄₃: cons₄₃ m₀) (h₄₄: cons₄₄ m₀) (h₄₅: cons₄₅ m₀) (h₄₆: cons₄₆ m₀) (h₄₇: cons₄₇ m₀) (h₄₈: cons₄₈ m₀) (h₄₉: cons₄₉ m₀) (h₅₀: cons₅₀ m₀) (h₅₁: cons₅₁ m₀) (h₅₂: cons₅₂ m₀) (h₅₃: cons₅₃ m₀) : (cons₅₄ m₀) ∧ (safe_cons₅₄ m₀) := by
  sorry
