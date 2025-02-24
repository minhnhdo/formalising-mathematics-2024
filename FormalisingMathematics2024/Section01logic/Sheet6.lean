/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq hpr hqr
  cases' hpq with hp hq
  apply hpr at hp
  exact hp
  apply hqr at hq
  exact hq
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with hp hq
  right
  exact hp
  left
  exact hq
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h
  cases' h with hpq hr
  cases' hpq with hp hq
  left
  exact hp
  right
  left
  exact hq
  right
  right
  exact hr
  intro h
  rcases h with (hp | hq | hr)
  left
  left
  exact hp
  left
  right
  exact hq
  right
  exact hr
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hpr hqs hpq
  cases' hpq with hp hq
  apply hpr at hp
  left
  exact hp
  apply hqs at hq
  right
  exact hq
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hpq hpr
  cases' hpr with hp hr
  apply hpq at hp
  left
  exact hp
  right
  exact hr
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hpr hqs
  rw [hpr, hqs]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h
  constructor
  intro hp
  have hpq: P ∨ Q
  left
  exact hp
  exact h hpq
  intro hq
  have hpq: P ∨ Q
  right
  exact hq
  exact h hpq
  intro ha ho
  cases' ha with h_not_p h_not_q
  cases' ho with hp hq
  exact h_not_p hp
  exact h_not_q hq
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro h
  by_cases hp: P
  by_cases hq: Q
  exfalso
  apply h
  constructor
  exact hp
  exact hq
  right
  exact hq
  left
  exact hp
  intro h hpq
  cases' hpq with hp hq
  cases' h with h_not_p h_not_q
  exact h_not_p hp
  exact h_not_q hq
  done
