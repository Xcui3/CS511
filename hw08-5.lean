import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Library.Tactic.Induction
import Mathlib.Data.Nat.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 8 -/

/- 5.a -/
/- By induction
    -- base case
      for n = 1,  we have j = 1
    -- inductive case
        IH: ∑_n (2i -1) = n^2

        We have Σ_n+1  (2i-1) = n^2 + 2n + 1 = (n+1) ^ 2
-/
/- 5.b -/
def A : ℕ → ℕ
  | 0 => 0
  | n+1 => A n + (2*n + 1)
example (n : ℕ): ∀ n, n ≥ 1 → A n = n^2 := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . dsimp [A]
    numbers
  . calc
      A (k+1) = A k + (2*k + 1) := by rw[A]
      _ = k^2 + (2*k + 1) := by rw[IH]
      _ = (k+1) ^ 2 := by ring
