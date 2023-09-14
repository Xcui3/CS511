import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- problem 3
example {p q r : Prop} (h: (p ∧ q) → r) : p → (q → r) := by
intro h_p
obtain <h_p, h_q> := h_1 
apply h_p


example {p q r : Prop} (h: p → (q → r)) : (p → q) → (q → r) := by
intro h_pq
intro h_q
apply h_q

example {p q r : Prop} (h: (p ∧ ¬q) → r) : q := by
apply h
