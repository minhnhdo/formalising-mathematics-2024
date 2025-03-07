/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hpq
  cases' hpq with h
  exact h
  done

example : P ∧ Q → Q := by
  intro hpq
  cases' hpq with _ h
  exact h
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro hpqr
  intro hpq
  cases' hpq with hp hq
  apply hpqr
  exact hp
  exact hq
  done

example : P → Q → P ∧ Q := by
  intro hp
  intro hq
  constructor
  exact hp
  exact hq
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro hpq
  cases' hpq with hp hq
  constructor
  exact hq
  exact hp
  done

example : P → P ∧ True := by
  intro h
  constructor
  exact h
  trivial
  done

example : False → P ∧ False := by
  intro h
  exfalso
  exact h
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq hqr
  cases' hpq with hp
  cases' hqr with _ hr
  constructor
  exact hp
  exact hr
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro hpqr
  intro hp hq
  apply hpqr
  constructor
  exact hp
  exact hq
  done
