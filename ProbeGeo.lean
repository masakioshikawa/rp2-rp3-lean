import RP2.ActivePaths
open RP2.HighTemperature
noncomputable section
open Finset
open scoped Classical
example {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x y : V) (n : ℕ) (p : H.Walk x y) (hp : p.length = n+1) : True := by
  cases p with
  | nil => trivial
  | cons h q =>
    trace_state
    trivial
