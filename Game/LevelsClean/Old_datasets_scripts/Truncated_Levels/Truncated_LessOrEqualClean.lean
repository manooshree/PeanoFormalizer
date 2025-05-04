import Game.Metadata
import Game.MyNat.LE
import Game.Tactic.Use
import Game.Levels.AdvAddition
import Game.Levels.LessOrEqual

namespace MyNat

/--
`a ≤ b` is *notation* for `∃ c, b = a + c`.

Because this game doesn't have negative numbers, this definition
is mathematically valid.

This means that if you have a goal of the form `a ≤ b` you can
make progress with the `use` tactic, and if you have a hypothesis
`h : a ≤ b`, you can make progress with `cases h with c hc`.
-/
DefinitionDoc LE as "≤"

NewDefinition LE


-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem truncated_le_refl (x : ℕ) : x ≤ x := by
  -- We claim that x is equal to x plus zero.
  use 0
  -- The goal is to prove that x equals x plus zero. By applying the theorem that states that adding zero to any natural number results in the original number, the goal simplifies to proving that x equals x.
  rw [add_zero]

-- Proof Statement: Prove that x ≤ succ x for any natural number x
theorem truncated_zero_le (x : ℕ) : 0 ≤ x := by
  -- Assume that the natural number x is the case we are considering. We need to show that x is equal to 0 plus x.
  use x
  -- Rewrite the goal replacing 0 + x with x, based on the fact that adding zero to any natural number results in the same natural number.
  rw [zero_add]

-- Proof Statement: Prove that x ≤ succ x for any natural number x
theorem truncated_le_succ_self (x : ℕ) : x ≤ succ x := by
  -- We simplify the claim to being succ x = x + 1 by using the case of 1.
  use 1
  -- Rewrite the left-hand side of the goal using the theorem that states that the successor of a number is equal to that number plus one. The goal now becomes proving that x + 1 equals x + 1.
  rw [succ_eq_add_one]

-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem truncated_le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb

-- Proof Statement: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem truncated_le_trans1 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
  use a + b
  -- Substitute z with y + b resulting in the equation y + b = x + (a + b).
  rw [hb]

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem truncated_le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- The goal is to prove that x equals 0 given that x is less than or equal to 0. We then consider the case where x is the sum of 0 and some natural number y. This gives us the equation 0 = x + y. Our goal now is to show that x equals 0 given this equation.
  cases hx with y hy
  -- Flip the equation so that it reads 'x + y = 0' instead of '0 = x + y'.
  symm at hy
  -- The sum of x and y is zero implies that y is zero because for all natural numbers a and n, n + a = 0 implies a = 0.
  apply add_right_eq_zero at hy

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem truncated_le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- We consider the case where x is less than or equal to y so y = x + some natural number a.
  cases hxy with a ha
  -- We consider the case where y is less than or equal to x so x = y + some natural number b.
  cases hyx with b hb
  -- We substitute y in the goal with x + a, changing our goal to prove that x equals x + a.
  rw [ha]
  -- Using the equality y = x + a, we substitute y in the equation x = y + b with x + a.
  rw [ha] at hb
  -- We re-arrange the right side of the equation x = x + a + b to x = x + (a + b) using the property that addition is associative.
  rw [add_assoc] at hb
  -- We flip the equation so that it reads 'x + (a + b) = x' instead of 'x = x + (a + b)'.
  symm at hb
  -- If x + (a + b) = x, then a + b = 0 by since for all natural numbers a and n, n + a = n implies a = 0.
  apply add_right_eq_self at hb
  -- If a + b = 0, then a = 0 and b = 0 by since for all natural numbers a and n, n + a = 0 implies a = 0.
  apply add_right_eq_zero at hb
  -- We substitute a with zero in the goal.
  rw [hb]
  -- We simplify x + 0 to x.
  rw [add_zero]

-- Proof Statement: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem truncated_le_antisymm1 (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- We consider the case where x is less than or equal to y so y = x + some natural number a.
  cases hxy with a ha
  -- We consider the case where y is less than or equal to x so x = y + some natural number b.
  cases hyx with b hb
  -- We substitute y in the goal with x + a, changing our goal to prove that x equals x + a.
  rw [ha]
  -- Using the equality y = x + a, we substitute y in the equation x = y + b with x + a. Then, we re-arrange the right side of the equation x = x + a + b to x = x + (a + b) using the property that addition is associative.
  rw [ha, add_assoc] at hb
  -- We flip the equation so that it reads 'x + (a + b) = x' instead of 'x = x + (a + b)'.
  symm at hb
  -- If x + (a + b) = x, then a + b = 0 by since for all natural numbers a and n, n + a = n implies a = 0.
  apply add_right_eq_self at hb

-- Proof Statement: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem truncated_orr_symm (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  --We consider the two possible cases given that either x equals 37 or y equals 42. For both cases, we aim to show that y equals 42 or x equals 37.
  cases h with hx hy
  -- We choose to prove the right side of the disjunction, which is x = 37.
  right

-- Proof Statement: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem truncated_le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- Induct on y, with d = 0 as the base case and the inductive hypothesis x = d. There are now two proof goals, prove base case: x <= 0 or 0 <= x and inductive step: x <= d + 1 or d + 1 <= x.
  induction y with d hd
  -- We choose to prove the right side of the disjunction, which is 0 ≤ x.
  right
  -- We assert that 0 is less than or equal to any natural number x, which completes the proof for this case.
  exact zero_le x

-- Proof Statement: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
theorem truncated_succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- We consider the case where the successor of x is less than or equal to the successor of y. This implies that the successor of y is equal to the successor of x plus some natural number d.
  cases hx with d hd
  -- We assume d as the difference such that when added to x results in y. The goal now is to prove that y is equal to x plus d.
  use d

-- Proof Statement: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem truncated_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- Replace 1 with the successor of 0. This means we are given that the succ y <= succ 0, and the updated goal is that the succ y = 0 or the succ y = succ 0.
  rw [one_eq_succ_zero] at hx ⊢

theorem truncated_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- We consider the case where y is a natural number. We then break down this case into two subcases: one where y is equal to 0, and the other where y is equal to the successor of another natural number z.
  cases y with z


-- Truncated Theorems Report:

-- truncated_le_refl: 2 steps kept

-- truncated_zero_le: 2 steps kept

-- truncated_le_succ_self: 2 steps kept

-- truncated_le_trans: 2 steps kept

-- truncated_le_trans1: 4 steps kept

-- truncated_le_zero: 3 steps kept

-- truncated_le_antisymm: 10 steps kept

-- truncated_le_antisymm1: 6 steps kept

-- truncated_orr_symm: 2 steps kept

-- truncated_le_total: 3 steps kept

-- truncated_succ_le_succ: 2 steps kept

-- truncated_le_one: 4 steps kept

-- truncated_le_two: 4 steps kept
