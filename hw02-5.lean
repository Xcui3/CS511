import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- problem 5.c
example {p q : Prop} : (¬ p ∧ ¬ q) → ¬ (q ∨ p) := by
  intro h
  have hnp : ¬ p := And.left h
  have hnq : ¬ q := And.right h
  assume h1: q ∨ p, 
  have h2 : q → ⊥ by
    intro 
    apply hnq

  have h3 : p → ⊥ by
    intro
    apply hnp
  
  or.elim h1 (h2 h3)
  not.elim



-- priblem 5.d
example {p q : Prop} : (¬ p ∨ ¬ q) → ¬ (q ∧ p) := by
  intro h
  assume h1 : q ∧ p
  have hp : p := And.left h1
  have hq : q := And.right h1
  
  have h2 : ¬ q → ⊥ by
    intro 
    apply hq

  have h3 : ¬ p → ⊥ by
    intro
    apply hp
  
  or.elim h (h2 h3)
  not.elim
