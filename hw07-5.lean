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
import Mathlib.Data.Nat.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 7 -/

/- 5.a -/
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h
  use k
  constructor
  . apply hk
  . constructor
    . apply hk1
    . apply hkp


/- 5.b -/
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    dsimp [Prime] at hp
    push_neg at hp
    have h := hp hp2
    obtain ⟨m,hm⟩ := h
    have h3 := H m
    obtain ⟨h1,h2⟩ := hm
    have h4 := le_or_succ_le m 0
    obtain h5 | h6 := h4
    . have h7: m=0 := by addarith[h5]

      obtain ⟨k,hk⟩ := h1
      have h8: 2 ≤ 0 := by
        calc
          2 ≤ p := by apply hp2
          _ = m *k := by apply hk
          _= 0 * k := by rw[h7]
          _ = 0 := by ring
      contradiction
    . have h4 := le_or_succ_le m 1
      obtain h5 | h6 := h4
      . have h7: m=1 := by
          apply le_antisymm
          apply h5
          apply h6
        obtain ⟨h8,h9⟩ := h2
        contradiction
      . have h7 := h3 h6
        have h8 : m ≤ p := by
          apply Nat.le_of_dvd
          addarith[hp2]
          apply h1
        obtain h9 | h10  := lt_or_eq_of_le h8
        . have h11:= h7 h9
          contradiction
        . obtain ⟨h12,h13⟩ := h2
          contradiction
  push_neg at H
  apply H
