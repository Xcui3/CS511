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
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- # assignment 5 -/

/- 6.a -/
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  . have h2:= H m 
    have h3 := h2 hm_left
    have h4 : m ≤ p := by
      apply Nat.le_of_dvd
      extra
      exact hmp
    obtain h6 | h7 : m = p ∨ m < p := eq_or_lt_of_le h4
    right
    exact h6
    
    have h5 := h3 h7
    contradiction



  

/- 6.b -/
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
      have ha1 : a ≤ 2 ∨ a ≥ 3 := by apply le_or_succ_le a 2 
      obtain ha2|ha3 := ha1
      . have hb1 : b ≤ 1 ∨ b ≥ 2 := by apply le_or_succ_le b 1
        obtain hb2|hb3 := hb1
        . have hc1 : c^2 < 3^2:= by
            calc 
              c^2 = a^2 + b^2 := by rw[h_pyth]
              _ ≤ 2^2 + b^2  := by rel[ha2]
              _ ≤ 2^2 + 1 ^ 2 := by rel[hb2]
              _ <  3^2 := by numbers
          have hc2: c < 3 := by 
            obtain hc3|hc4 := lt_or_ge c 3
            . apply hc3
            . have hc5: c^2 ≥  3^2 := by
                calc
                  c^2 = c*c := by ring
                  _ ≥ 3 *3 := by rel[hc4]
              have hc6: ¬ c^2 < 3^2 := by
                apply not_lt_of_ge
                addarith[hc5]
              contradiction

          have ha3: a < 2 ∨ a = 2 := by apply Nat.lt_or_eq_of_le ha2 
          obtain ha4|hha5 := ha3
          . have ha4: a ≤ 1 := by addarith[ha4]
            have ha3: a < 1 ∨ a = 1 := by apply Nat.lt_or_eq_of_le ha4
            obtain ha5|ha6 := ha3 
            . have ha7 : a ≤ 0 := by addarith[ha5]
              have ha8: ¬ a ≤  0 := by
                apply not_le_of_gt
                extra
              contradiction
            have hb3: b < 1 ∨ b = 1 := by apply Nat.lt_or_eq_of_le hb2
            obtain hb4|hb5 := hb3
            . have hb6: b ≤ 0:= by addarith[hb4]
              have hb7: ¬ b ≤ 0 := by
                apply not_le_of_gt
                extra
              contradiction

            . have hc3: c ≤ 2 := by addarith[hc2]
              have hc3: c < 2 ∨ c = 2 := by apply Nat.lt_or_eq_of_le hc3
              obtain hc4|hc5 := hc3
              . have hc5: c ≤ 1 := by addarith[hc4]
                have hc6: c < 1 ∨ c = 1 := by apply Nat.lt_or_eq_of_le hc5
                obtain hc7|hc8 := hc6
                . have hc9: c ≤ 0 := by addarith[hc7]
                  have hc10 : ¬ c ≤ 0:= by
                    apply not_le_of_gt
                    extra
                  contradiction
                . have cc: 2 = 1 := by
                    calc 
                      2 = 1 + 1 := by numbers
                      _ = 1^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[ha6,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 1^2 := by rw[hc8]
                      _ = 1 := by numbers
                  contradiction
              . have cc: 2 = 4 := by
                  calc
                    2 = 1 + 1 := by numbers
                      _ = 1^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[ha6,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 2^2 := by rw[hc5]
                      _ = 4 := by numbers
                contradiction
          . have hb3: b < 1 ∨ b = 1 := by apply Nat.lt_or_eq_of_le hb2
            obtain hb4|hb5 := hb3
            . have hb6: b ≤ 0:= by addarith[hb4]
              have hb7: ¬ b ≤ 0 := by
                apply not_le_of_gt
                extra
              contradiction
            . have hc3: c ≤ 2 := by addarith[hc2]
              have hc3: c < 2 ∨ c = 2 := by apply Nat.lt_or_eq_of_le hc3
              obtain hc4|hc5 := hc3
              . have hc5: c ≤ 1 := by addarith[hc4]
                have hc6: c < 1 ∨ c = 1 := by apply Nat.lt_or_eq_of_le hc5
                obtain hc7|hc8 := hc6
                . have hc9: c ≤ 0 := by addarith[hc7]
                  have hc10 : ¬ c ≤ 0:= by
                    apply not_le_of_gt
                    extra
                  contradiction
                . have cc: 5 = 1 := by
                    calc 
                      5 = 4 + 1 := by numbers
                      _ = 2^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[hha5,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 1^2 := by rw[hc8]
                      _ = 1 := by numbers
                  contradiction
              . have cc: 5 = 4 := by
                  calc
                    5 = 4 + 1 := by numbers
                      _ = 2^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[hha5,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 2^2 := by rw[hc5]
                      _ = 4 := by numbers
                contradiction
        . have hb4: b^2 < c^2 := by
            calc
              b^2 < a^2 + b^2  := by extra
              _ = c^2 := by rw [h_pyth]
            
          have hb5:b < c := by 
            have hb6:= lt_or_ge b c 
            obtain hb6|hb7 := hb6
            . apply hb6
            . have hb8 : b^2 ≥ c^2 := by 
                calc 
                  b^2 = b^2 := by ring
                  _ ≥ c^2 := by rel[hb7]
              have hc10 : ¬ b^2 < c^2:= by
                    apply not_lt_of_ge
                    addarith[hb8]
              contradiction              

          have hb5: b + 1 ≤ c := by addarith[hb5]
          have hb6: c^2 < (b+1)^2 := by
            calc 
              c^2 = a^2 + b^ 2 := by rw[h_pyth]
              _ ≤ 2^2 + b^2 := by rel[ha2]
              _ = b^2 + 2*2 := by ring
              _ ≤ b^2 + 2*b := by rel[hb3]
              _ < b^2 + 2*b + 1 := by extra
              _ = (b+1)^2 := by ring
          have hb7: c < b+1 := by 
            have hb6:= lt_or_ge c (b+1) 
            obtain hb8|hb9 := hb6
            . apply hb8
            . have hb9 : c^2 ≥ (b+1)^2  := by 
                calc 
                  c^2 = c^2 := by ring
                  _ ≥ (b+1)^2 := by rel[hb9]
              have hc10 : ¬ c ^ 2 < (b + 1) ^ 2:= by
                  apply not_lt_of_ge
                  addarith[hb9]
              contradiction
          have hb8: ¬ c < b+1 := by
            apply not_lt_of_ge
            addarith[hb5]
          contradiction          
            
        
      . addarith[ha3]



/- 6.c -/
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have h1 := lt_or_ge x y
  obtain h2|h3 := h1
  . have h3: x^n < y^n := by 
      calc 
        x^n = x ^n := by ring
        _  < y^n := by rel[h2]
    have h4: ¬ y^n ≤ x^n := by
      apply not_le_of_gt
      apply h3
    contradiction

  . addarith[h3]


/- 6.d -/
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at *
  obtain ⟨h1,h2⟩ := h
  have h1 : p ≤ 2 ∨ p ≥ 3 := by apply le_or_succ_le p 2
  obtain h3|h4:= h1 
  . left
    apply le_antisymm h3 h1
  . right
    obtain h5|h6 := Nat.even_or_odd p
    . dsimp [Nat.Even] at h5
      obtain ⟨k,hk⟩ := h5
      have h5:= h2 2
      have h6: 2∣ p := by 
        use k
        apply hk
      have h5 := h5 h6
      obtain h7|h8 := h5
      . contradiction
      . have h9: 2 ≥ 3 := by 
          calc
            2 = p := by apply h8
            _ ≥ 3 := by rel[ h4]
        contradiction
    . apply h6
