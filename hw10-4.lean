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

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d

/- # assignment 10 -/

/- 4.a -/
def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  . have IH := T_eq (1-n) -- inductive hypothesis
    calc
      T (1-n) + 2*n - 1 = (1-n)^2 + 2*n - 1 := by rw[IH]
      _ = n ^ 2 := by ring
  .
    have h5:= T_eq (1+n)
    rw [T]
    split_ifs
    .
      calc
        T (1 - -n) + 2 * -n - 1 = T (1 + n) + 2 * -n -1 := by ring
        _ = (1 + n ) ^ 2 + 2 * -n -1 := by rw[h5]
        _ = n ^ 2 := by ring

  . have h3: n = 0 := by
      apply le_antisymm
      apply h1
      simp at h2
      apply h2
    calc
      0 = 0 ^ 2 := by numbers
      _ = n ^ 2 := by rw[h3]

/- 4.b -/

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨ h1, h2,h3 ⟩ := hr
  obtain ⟨ h4, h5,h6 ⟩ := hs
  obtain ⟨ k, hk ⟩ := h3
  obtain ⟨ q , hq ⟩ := h6


  have h7 : r ≡ s [ZMOD b] := by
    use q - k
    calc
      r -s = r + a - s -a := by ring
      _ = (a - s) - (a - r) := by ring
      _ = b*q - b * k := by rw[hq,hk]
      _ = b * (q - k) := by ring

  obtain ⟨ p, hp ⟩ := h7
  have h8 : b* p = b * (q - k) := by
    calc
      b * p = (r - s)  := by rw [hp]
      _= ((a - s) - (a - r)) := by ring
      _ = (b * q - b * k) := by rw[hq, hk ]
      _ = b* (q - k) := by ring
  have h9: p = q - k := by cancel b at h8
  sorry




example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  simp
  sorry
