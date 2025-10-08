/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

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

  exact h True.intro

  done

example : False → ¬True := by
  exact False.elim
  done

example : ¬False → True := by
  intro h
  exact True.intro

  done

example : True → ¬False := by
  intro h
  exact False.elim
  done

example : False → ¬P := by
  intro false

  exfalso

  exact false

  done

example : P → ¬P → False := by

  intro p notp

  apply notp

  exact p

  done

example : P → ¬¬P := by
  intro p

  by_contra hfalse

  apply hfalse

  exact p

  done

example : (P → Q) → ¬Q → ¬P := by
  intro p_imp_q notq

  by_cases h : P

  · -- case p
    exact fun _hp =>
      notq (p_imp_q h)
  · -- case ¬ p
    exact h

  done

example : ¬¬False → False := by
  intro not_not_false

  by_cases h : False

  exact h

  apply not_not_false at h

  apply h

  done

example : ¬¬P → P := by

  intro not_not_p

  by_cases h : P

  -- P

  exact h

  -- P

  apply not_not_p at h

  exfalso

  exact h

  done

example : (¬Q → ¬P) → P → Q := by
  intro notq_notp p



  apply notq_notp at p

  exfalso
  exact p











  -- by_cases h : Q
  -- exact h
  -- apply notq_notp at h







  done
