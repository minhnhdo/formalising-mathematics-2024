/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hl
  rw [hl]
  intro hr
  rw [hr]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  rw [hpq, hqr]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hl
  cases' hl with hpq hqp
  constructor
  exact hqp
  exact hpq
  intro hr
  cases' hr with hqp hpq
  constructor
  exact hpq
  exact hqp
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hpqr
  cases' hpqr with hpq hr
  cases' hpq with hp hq
  refine ⟨hp, hq, hr⟩
  intro hpqr
  rcases hpqr with ⟨hp, hq, hr⟩
  constructor
  constructor
  exact hp
  exact hq
  exact hr
  done

example : P ↔ P ∧ True := by
  constructor
  intro h
  constructor
  exact h
  trivial
  intro hp_true
  cases' hp_true with hp
  exact hp
  done

example : False ↔ P ∧ False := by
  constructor
  intro hfalse
  exfalso
  exact hfalse
  intro hp_false
  cases' hp_false with _ hfalse
  exact hfalse
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq hrs
  rw [hpq, hrs]
  done

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h_p_notp h_notp_p
  have h: ¬P
  intro h
  apply h_p_notp
  exact h
  exact h
  have hp: P
  apply h_notp_p at h
  exact h
  exact h hp
  done
