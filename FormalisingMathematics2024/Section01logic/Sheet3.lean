/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  triv
  done

example : False → ¬True := by
  intro h
  exfalso
  exact h
  done

example : ¬False → True := by
  intro
  triv
  done

example : True → ¬False := by
  intro
  by_contra h
  exact h
  done

example : False → ¬P := by
  intro h
  by_contra
  exact h
  done

example : P → ¬P → False := by
  intro h hn
  exact hn h
  done

example : P → ¬¬P := by
  intro h
  by_contra hn
  exact hn h
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq
  by_contra h
  apply hpq at h
  exact hnq h
  done

example : ¬¬False → False := by
  intro h
  apply h
  by_contra hf
  exact hf
  done

example : ¬¬P → P := by
  intro hnn
  by_contra hn
  apply hn
  apply hnn at hn
  exfalso
  exact hn
  done

example : (¬Q → ¬P) → P → Q := by
  intro hnqnp h
  by_contra hnq
  apply hnqnp at hnq
  apply hnq at h
  exact h
  done
