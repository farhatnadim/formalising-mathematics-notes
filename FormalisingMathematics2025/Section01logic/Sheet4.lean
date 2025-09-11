/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/



-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases' h with h1 h2
  exact h1
  done

example : P ∧ Q → Q := by
  intro h1
  cases h1 with
  | intro left right
  exact right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  apply h1
  cases h2 with
  | intro left right
  exact left
  cases h2 with
  | intro left right
  exact right
  done

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption
  -- · assumption
  -- · assumption
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases h1 with
  | intro left right
  constructor<;> assumption
  done



example : P → P ∧ True := by
  intro h1
  by_cases h2 : P
  tauto
  by_contra h2
  apply h2
  tauto



example : False → P ∧ False := by
  exact False.elim

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  rintro ⟨h1, h2⟩
  intro h3
  constructor <;>
  cases' h3 with h4 h5
  assumption
  assumption


example : (P ∧ Q → R) → P → Q → R := by
  tauto


  done
