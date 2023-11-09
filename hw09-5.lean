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
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/- # assignment 9 -/

/- 5.a -/
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . -- base case 0
    numbers
    simp
  . -- base case 1
    numbers
    simp
  . -- inductive step
    calc
      q (k + 1 + 1) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw[q]
      _ = 2 * ((k + 1 :ℤ ) ^ 3 + 1) - ((k:ℤ ) ^ 3 + 1) + 6*k + 6 := by rw[IH1, IH2]
      _ = (↑k + 1 + 1) ^ 3 + 1 := by ring

/- 5.b -/
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  . -- base case 0
    numbers
    simp
  . -- base case 1
    numbers
    simp
  . -- inductive step
    calc
      r (k + 1 + 1) = 2 * r (k + 1) + r k := by rw[r]
      _ ≥  2 * ( 2 ^ (k + 1)) + r k := by rel[IH2]
      _ ≥  2 * ( 2 ^ (k + 1)) + 2 ^ k := by rel [IH1]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 2) := by extra

/- 5.c -/
theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain ha | ha := Nat.even_or_odd n
  . -- n Even
    simp [Nat.Even] at *
    obtain ⟨k , hk⟩ := ha
    have IH1 := extract_pow_two k
    have h1 : ∃ a x, Odd x ∧ k = 2 ^ a * x := by
      apply IH1
      have h1: 2 * k > 2*0 := by
        calc
          2 * k = n := by rw[hk]
          _ > 0 := by rel[hn]
      cancel 2 at h1

    obtain ⟨k1 ,x , h2 ⟩ := h1
    use k1 + 1
    use x
    obtain ⟨ h3,h4 ⟩ := h2
    constructor
    . apply h3
    .
      calc
        n = 2 * k := by rw[hk]
        _ = 2 * (2 ^ k1 * x) := by rw[h4]
        _ = 2 ^ (k1 + 1) * x := by ring

  . -- n Odd
    use 0
    use n
    constructor
    . apply ha
    . numbers
      simp
