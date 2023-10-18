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

/- # assignment 6 -/

/- 4.a -/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h1
    obtain ⟨x,hx⟩ := h1
    have h2: P x ↔ Q x := by apply h x
    obtain ⟨h3,h4⟩ := h2
    have h3: Q x := by apply h3 hx
    use x
    apply h3
  . intro h1
    obtain ⟨x,hx⟩ := h1
    have h2: P x ↔ Q x := by apply h x
    obtain ⟨h3,h4⟩ := h2
    have h3: P x := by apply h4 hx
    use x
    apply h3
  

/- 4.b -/
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h
    obtain ⟨x,y,hxy⟩ := h
    use y
    use x
    apply hxy
  . intro h
    obtain ⟨x,y,hxy⟩ := h
    use y
    use x
    apply hxy 


/- 4.c -/
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro h 
    intro x1
    intro y1
    apply h 

/- 4.d -/
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
 constructor 
 . intro h
   obtain ⟨h1,h2⟩ := h
   obtain ⟨x,hx⟩ := h1
   use x
   constructor
   apply hx
   apply h2
   