import Game.Metadata
import Game.MyNat.LE
import Game.Tactic.Use
import Game.LevelsClean.AdvAdditionClean

namespace MyNat

-- Proof Statement: Prove that x ≤ x for any natural number x
theorem le_refl (x : ℕ) : x ≤ x := by
  -- We claim that x is equal to x plus zero.
  use 0
  -- The goal is to prove that x equals x plus zero. By applying the theorem that states that adding zero to any natural number results in the original number, the goal simplifies to proving that x equals x.
  rw [add_zero]
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that x ≤ x for any natural number x
theorem le_refl_dev_1 (x : ℕ) : x ≤ x := by
  -- x <= x -> x + 0 = x
  use 0
  -- x + 0 = x -> 0 + x = x
  rw [add_comm]
  -- 0 + x = x -> x = x
  rw [zero_add]
  -- LHS = RHS
  rfl

-- Proof Statement: Prove that x ≤ x for any natural number x
theorem le_refl_dev_2 (x : ℕ) : x ≤ x := by
  -- By the definition of less than, x + n = x where n is some natural number. We set n to be 0
  use 0
  -- simplify the RHS using properties of addition to x = x
  rw [add_zero]
  -- The LHS = RHS, so we can conclude the proof.
  rfl

-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem zero_le (x : ℕ) : 0 ≤ x := by
  -- Assume that the natural number x is the case we are considering. We need to show that x is equal to 0 plus x.
  use x
  -- Rewrite the goal replacing 0 + x with x, based on the fact that adding zero to any natural number results in the same natural number.
  rw [zero_add]
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem zero_le_dev_1 (x : ℕ) : 0 ≤ x := by
  -- Using the definition of ≤ it suffices to show that x = 0 + x
  use x
  -- Simplify to x = x using the property that adding zero to a number doesn't change the number.
  rw [zero_add]
  -- The LHS and RHS are equal, completing the proof.
  rfl

-- Proof Statement: Prove that 0 ≤ x for any natural number x
theorem zero_le_dev_2 (x : ℕ) : 0 ≤ x := by
  -- x = 0 + x
  use x
  -- x = 0 + x -> x = x
  rw [zero_add]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove that x ≤ succ x for any natural number x
theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  -- We simplify the claim to being succ x = x + 1 by using the case of 1.
  use 1
  -- Rewrite the left-hand side of the goal using the theorem that states that the successor of a number is equal to that number plus one. The goal now becomes proving that x + 1 equals x + 1.
  rw [succ_eq_add_one]
  -- The goal is now to prove that x + 1 equals x + 1, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that x ≤ succ x for any natural number x
theorem le_succ_self_dev_1 (x : ℕ) : x ≤ succ x := by
  -- We simplify the claim to being succ x = x + 1 by using the case of 1.
  use 1
  -- The goal is now to prove that x + 1 equals x + 1, which can be proven by applying the theorem that states that the successor of a number is equal to that number plus one to the left-hand side of the goal.
  exact succ_eq_add_one x

-- Proof Statement: Prove that x ≤ succ x for any natural number x
theorem le_succ_self_dev_2 (x : ℕ) : x ≤ succ x := by
  -- succ x = x + 1
  use 1
  -- succ x = x + 1 -> x + 1 = x + 1
  rw [succ_eq_add_one]
  -- done
  rfl

-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
  use a + b
  -- Substitute z with y + b and y with x + a in the goal, resulting in the equation x + a + b = x + (a + b).
  rw [hb, ha]
  -- The goal is now to prove that x + a + b = x + (a + b), which can be proven by applying the theorem that states that addition is associative to the left-hand side of the goal.
  exact add_assoc x a b

-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem le_trans_dev_1 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
  use a + b
  -- Substitute z with y + b resulting in the equation y + b = x + (a + b).
  rw [hb]
  -- Substitute y with x + a resulting in the equation x + a + b = x + (a + b).
  rw [ha]
  -- The goal is now to prove that x + a + b = x + (a + b), which can be proven by applying the theorem that states that addition is associative to the left-hand side of the goal.
  exact add_assoc x a b

-- Proof Statement: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem le_trans_dev_2 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- y = x + a
  cases hxy with a ha
  -- z = y + b
  cases hyz with b hb
  -- z = x + (a + b)
  use a + b
  -- z = x + (a + b) -> y + b = x + (a + b)
  rw [hb]
  -- y + b = x + (a + b) -> (x + a) + b = x + (a + b)
  rw [ha]
  -- (x + a) + b = x + (a + b) by associativity
  exact add_assoc x a b

-- Proof Statement: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- The goal is to prove that x equals 0 given that x is less than or equal to 0. We then consider the case where x is the sum of 0 and some natural number y. This gives us the equation 0 = x + y. Our goal now is to show that x equals 0 given this equation.
  cases hx with y hy
  -- Flip the equation so that it reads 'x + y = 0' instead of '0 = x + y'.
  symm at hy
  -- The sum of x and y is zero implies that y is zero because for all natural numbers a and n, n + a = 0 implies a = 0.
  apply add_right_eq_zero at hy
  -- The goal is now to prove that x = 0, which can be proven by applying hy to the goal.
  exact hy

-- Proof Statement: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem le_zero_dev_1 (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- Using the definition of ≤, we have that 0 = x + y for some natural number y.
  cases hx with y hy
  -- By the symmetry of equality, we have x + y = 0.
  symm at hy
  -- Using the theorem that if a + b = 0, a = 0, we have that x = 0.
  apply add_right_eq_zero at hy
  -- So we know that x = 0, which is exactly what we wanted to prove.
  exact hy

-- Proof Statement: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem le_zero_dev_2 (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- 0 = x + y
  cases hx with y hy
  -- 0 = x + y -> x + y = 0
  symm at hy
  -- x + y = 0 -> x = 0
  apply add_right_eq_zero at hy
  -- done
  exact hy

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
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
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem le_antisymm_dev_1 (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
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
  -- If a + b = 0, then a = 0 and b = 0 by since for all natural numbers a and n, n + a = 0 implies a = 0.
  apply add_right_eq_zero at hb
  -- We substitute a in the equation x = x + a with zero, as given shown above, changing our goal to prove that x equals x.
  rw [hb, add_zero]
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Proof Statement: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
theorem le_antisymm_dev_2 (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- y = x + a
  cases hxy with a ha
  -- x = y + b
  cases hyx with b hb
  -- x = y -> x = x + a
  rw [ha]
  -- x = y + b -> x = (x + a) + b
  rw [ha] at hb
  -- x = (x + a) + a -> x = x + (a + b)
  rw [add_assoc] at hb
  -- x = x + (a + b) -> x + (a + b) = x
  symm at hb
  -- x + (a + b) = x -> a + b = 0
  apply add_right_eq_self at hb
  -- a + b = 0 -> a = 0
  apply add_right_eq_zero at hb
  -- x = x + a -> x = x + 0
  rw [hb]
  -- x = x + 0 -> x = x
  rw [add_zero]
  -- lhs = rhs
  rfl

-- Proof Statement: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem orr_symm (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  --We consider the two possible cases given that either x equals 37 or y equals 42. For both cases, we aim to show that y equals 42 or x equals 37.
  cases h with hx hy
  -- We choose to prove the right side of the disjunction, which is x = 37.
  right
  -- We are given that x equals 37, so we can use this to prove the goal.
  exact hx
  -- We choose to prove the left side of the disjunction, which is y = 42.
  left
  -- We are given that y equals 42, so we can use this to prove the goal.
  exact hy

-- Proof Statement: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem orr_symm_dev_1 (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  -- We have that either x = 37 or y = 42.
  cases h with hx hy
  -- In the first case, since we have to prove a disjunction, we choose to prove the right side.
  right
  -- We need to show x = 37, but this is exactly what we already know.
  exact hx
  -- In the second case, since we have to prove a disjunction, we choose to prove the left side.
  left
  -- We need to show y = 42, but this is exactly what we already know.
  exact hy

-- Proof Statement: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem orr_symm_dev_2 (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  -- x = 37 ∨ y = 42 -> x = 37 (case 1) or y = 42 (case 2)
  cases h with hx hy
  -- case 1: y = 42 ∨ x = 37 → x = 37
  right
  -- done
  exact hx
  -- case 2: y = 42 ∨ x = 37 → y = 42
  left
  -- done
  exact hy

-- Proof Statement: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- Induct on y, with d = 0 as the base case and the inductive hypothesis x = d. There are now two proof goals, prove base case: x <= 0 or 0 <= x and inductive step: x <= d + 1 or d + 1 <= x.
  induction y with d hd
  -- We choose to prove the right side of the disjunction, which is 0 ≤ x.
  right
  -- We assert that 0 is less than or equal to any natural number x, which completes the proof for this case.
  exact zero_le x
  -- We consider the two cases: either 'x' is less than or equal to 'd', or 'd' is less than or equal to 'x'. For both cases, we aim to show that x is less than or equal to d + 1 or d + 1 is less than or equal to x.
  cases hd with h1 h2
  -- We choose to prove the left side of the disjunction, which is x ≤ d + 1.
  left
  -- We consider the case that x is less than or equal to d. We know this is true because there exists a natural number e such that d equals x plus e.
  cases h1 with e h1
  -- We substitute d with x + e in the goal, resulting in the equation x = x + e + 1.
  rw [h1]
  -- Use the case of e + 1 to simplify the goal to succ (x + e) = x + (e + 1).
  use e + 1
  -- We first rewrite the left-hand side expression 'succ (x + e)' to 'x + e + 1' using the theorem that states the successor of a number is equal to the number plus one. Then, we use the theorem that addition is associative to rearrange 'x + e + 1' to 'x + (e + 1)'.
  rw [succ_eq_add_one, add_assoc]
  -- The goal is now to prove that x + (e + 1) = x + (e + 1), which is true by reflexivity.
  rfl
  -- We consider the case where d is less than or equal to x. We then break down this case into two subcases: one where x is equal to d plus some natural number e, and the other where x is greater than d by some natural number e.
  cases h2 with e he
  -- We consider the cases that e is zero or the successor of a natural number a.
  cases e with a
  -- We substitute x with d + 0 in the goal, resulting in the the goal d + 0 ≤ succ d ∨ succ d ≤ d + 0.
  rw [he]
  -- We choose to prove the left side of the disjunction, which is d + 0 ≤ succ d.
  left
  -- We rewrite the left-hand side of the goal to d because d + 0 = d.
  rw [add_zero]
  -- We use the case of 1 to simplify the goal to succ d = d + 1.
  use 1
  -- The goal is to prove that succ d equals d + 1. We directly apply the fact that the successor of a natural number d is equal to d + 1, which completes the proof for this goal.
  exact succ_eq_add_one d
  -- We choose to prove the right side of the disjunction, which is succ d <= x.
  right
  -- We use the case of a to rewrite the goal to succ x = succ d + a.
  use a
  -- The goal is to prove that succ d equals d + 1. We directly apply the fact that the successor of a natural number d is equal to d + 1.
  rw [add_succ] at he
  -- Rewrite the right hand side of the goal using the theorem that adding a successor to a natural number is the same as adding the natural number and then taking the successor. This leaves the goal unchanged in this case.
  rw [succ_add]
  -- We have shows that x = succ d + a, so we can use this to prove the goal.
  exact he

-- Proof Statement: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem le_total_dev_1 (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- We begin with induction on y.
  induction y with d hd
  -- For the base case, we need to prove x ≤ 0 ∨ 0 ≤ x, and we choose to show 0 ≤ x.
  right
  -- This follows from the theorem that 0 ≤ x for any natural number x.
  exact zero_le x
  -- For the inductive step, we are given that x ≤ d ∨ d ≤ x, so we do a proof by cases.
  cases hd with h1 h2
  -- In the first case, we need to show that x ≤ succ d ∨ succ d ≤ x, and we choose to show x ≤ succ d.
  left
  -- Using the definition of ≤, d = x + e for some natural number e.
  cases h1 with e h1
  -- We rewrite the goal so that we just need to show that x ≤ succ (x + e)
  rw [h1]
  -- Using the definition of ≤, it suffices to show that succ (x + e) = x + (e + 1)
  use e + 1
  -- We use two theorems to show that this is the same as (x + e) + 1 = x + (e + 1), which in turn is the same as x + (e + 1) = x + (e + 1).
  rw [succ_eq_add_one, add_assoc]
  -- We finish this case by reflexivity.
  rfl
  -- In the second case, we have d ≤ x, which means that x = d + e for some natural number e.
  cases h2 with e he
  -- Either e = 0, or e = succ a for some natural number a.
  cases e with a
  -- In the former case, x = d + 0, so by rewriting it suffices to show that d + 0 ≤ succ d ∨ succ d ≤ d + 0
  rw [he]
  -- We need to show that d + 0 ≤ succ d ∨ succ d ≤ d + 0, and we choose to show d + 0 ≤ succ d.
  left
  -- But d + 0 = d, so by rewriting we just need to show that d ≤ succ d.
  rw [add_zero]
  -- Using the definition of ≤, it suffices to show that succ d = d + 1.
  use 1
  -- But succ d = d + 1 is a theorem we proved earlier, so we are done.
  exact succ_eq_add_one d
  -- In th latter case, we need to show that x ≤ succ d ∨ succ d ≤ x, so we choose to show succ d ≤ x.
  right
  -- Using the definition of ≤, it suffices to show x = succ d + a.
  use a
  -- We know x = d + succ a, so by rewriting we know x = succ (d + a)
  rw [add_succ] at he
  -- We want to show x = succ d + a, so by rewriting we can instead show x = succ (d + a)
  rw [succ_add]
  -- But this is exactly what we just showed that we know.
  exact he

-- Proof Statement: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem le_total_dev_2 (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- induction on y
  induction y with d hd
  -- show the right side of the disjunction
  right
  -- 0 ≤ x, so this case is done
  exact zero_le x
  -- x ≤ d ∨ d ≤ x -> x ≤ d (case 1) or d ≤ x (case 2)
  cases hd with h1 h2
  -- x ≤ succ d ∨ succ d ≤ x -> x ≤ succ d
  left
  -- x ≤ d -> d = x + e for some natural number e
  cases h1 with e h1
  -- x ≤ succ d -> x ≤ succ (x + e)
  rw [h1]
  -- x ≤ succ (x + e) -> succ (x + e) = x + (e + 1)
  use e + 1
  -- succ (x + e) = x + (e + 1) -> (x + e) + 1 = x + (e + 1) -> x + (e + 1) = x + (e + 1)
  rw [succ_eq_add_one, add_assoc]
  -- lhs = rhs
  rfl
  -- d ≤ x -> x = d + e for some natural number e
  cases h2 with e he
  -- e = 0 or e = succ a for some natural number a
  cases e with a
  -- x ≤ succ d ∨ succ d ≤ x -> d + 0 ≤ succ d ∨ succ d ≤ d + 0
  rw [he]
  -- d + 0 ≤ succ d ∨ succ d ≤ d + 0 -> d + 0 ≤ succ d
  left
  -- d + 0 ≤ succ d -> d ≤ succ d
  rw [add_zero]
  -- d ≤ succ d -> succ d = d + 1
  use 1
  -- succ d = d + 1 by a theorem
  exact succ_eq_add_one d
  -- x ≤ succ d ∨ succ d ≤ x → succ d ≤ x
  right
  -- succ d ≤ x -> x = succ d + a
  use a
  -- x = d + succ a -> x = succ (d + a)
  rw [add_succ] at he
  -- x = succ d + a -> x = succ (d + a)
  rw [succ_add]
  -- x = succ (d + a) by a fact we know right now
  exact he

-- Proof Statement: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- We consider the case where the successor of x is less than or equal to the successor of y. This implies that the successor of y is equal to the successor of x plus some natural number d.
  cases hx with d hd
  -- We assume d as the difference such that when added to x results in y. The goal now is to prove that y is equal to x plus d.
  use d
  -- We rewrite the right-hand side of succ y = succ x + d using the theorem that states the the successor of a sum of two natural numbers is the same as the successor of the first number added to the second number.
  rw [succ_add] at hd
  -- We apply the property that if two natural numbers with successors are equal, then the original numbers are also equal.
  apply succ_inj at hd
  -- We have shown that x = y + d, so we can use this to prove the goal.
  exact hd

-- Proof Statement: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem succ_le_succ_dev_1 (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- Using the definition of ≤, we have that succ y = succ x + d for some natural number d
  cases hx with d hd
  -- Using the definition of ≤, to prove x ≤ y, it suffices to show that y = x + d
  use d
  -- Since succ y = succ x + d, we have succ y = succ (x + d)
  rw [succ_add] at hd
  -- Using the injectivity of succ, we have that y = x + d.
  apply succ_inj at hd
  -- Thus, we know y = x + d, which is exactly what we wanted to prove.
  exact hd

-- Proof Statement: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem succ_le_succ_dev_2 (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- succ x ≤ succ y -> succ y = succ x + d for some natural number d
  cases hx with d hd
  -- x ≤ y -> y = x + d
  use d
  -- succ y = succ x + d -> succ y = succ (x + d)
  rw [succ_add] at hd
  -- succ y = succ (x + d) -> y = x + d
  apply succ_inj at hd
  -- thus, y = x + d, so we are done
  exact hd

-- Proof Statement: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- Replace 1 with the successor of 0. This means we are given that the succ y <= succ 0, and the updated goal is that the succ y = 0 or the succ y = succ 0.
  rw [one_eq_succ_zero] at hx ⊢
  -- We use the property that if one natural number is less than or equal to another, then their successors also maintain this relationship. This means that y <= 0.
  apply succ_le_succ at hx
  -- We apply the property that if x is less than or equal to 0, then x must be equal to 0 so y = 0.
  apply le_zero at hx
  -- We substitute y with 0 in the goal, resulting in the goal succ 0 = 0 ∨ succ 0 = succ 0.
  rw [hx]
  -- We choose to prove the right side of the disjunction, which is succ 0 = succ 0.
  right
  -- We are given that succ 0 equals succ 0, so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
theorem le_one_dev_1 (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- Either x = 0 or x = succ y for some natural number y.
  cases x with y
  -- To prove 0 = 0 ∨ 0 = 1, we choose to prove 0 = 0.
  left
  -- by reflexivity, 0 = 0
  rfl
  -- We substitute 1 for succ 0 in both what we know and what we are trying to show
  rw [one_eq_succ_zero] at hx ⊢
  -- Using a theorem, since succ y ≤ succ 0, we have y ≤ 0
  apply succ_le_succ at hx
  -- Using another theorem, since y ≤ 0, y = 0.
  apply le_zero at hx
  -- Thus, our goal to show succ y = 0 ∨ succ y = succ 0 is really just succ 0 = 0 ∨ succ 0 = succ 0.
  rw [hx]
  -- To show succ 0 = 0 ∨ succ 0 = succ 0, we choose to show succ 0 = succ 0.
  right
  -- But this just follows from reflexivity.
  rfl

-- Proof Statement: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
theorem le_one_dev_2 (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  -- x = 0 (case 1) or x = succ y (case 2) for some natural number y
  cases x with y
  -- 0 = 0 ∨ 0 = 1 -> 0 = 0
  left
  -- lhs = rhs
  rfl
  -- succ y ≤ 1 -> succ y ≤ succ 0; succ y = 0 ∨ succ y = 1 -> succ y = 0 ∨ succ y = succ 0
  rw [one_eq_succ_zero] at hx ⊢
  -- succ y ≤ succ 0 -> y ≤ 0
  apply succ_le_succ at hx
  -- y ≤ 0 -> y = 0
  apply le_zero at hx
  -- succ y = 0 ∨ succ y = succ 0 -> succ 0 = 0 ∨ succ 0 = succ 0
  rw [hx]
  -- succ 0 = 0 ∨ succ 0 = succ 0 -> succ 0 = succ 0
  right
  -- lhs = rhs
  rfl

-- Proof Statement: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- We consider the case where x is a natural number. We then break down this case into two subcases: one where x is equal to 0, and the other where x is equal to the successor of another natural number y.
  cases x with y
  -- We choose to prove the left side of the disjunction, which is 0 = 0.
  left
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- We consider the case where y is a natural number. We then break down this case into two subcases: one where y is equal to 0, and the other where y is equal to the successor of another natural number z.
  cases y with z
  -- We choose to prove the right side of the disjunction, which is succ 0 = 1 ∨ succ 0 = 2.
  right
  -- We choose to prove the left side of the disjunction, which is succ 0 = 1.
  left
  -- We rewrite the goal using the theorem that states the successor of 0 is equal to 1.
  rw [one_eq_succ_zero]
  -- We are given that 0 equals 0, so we can use reflexivity to prove the goal.
  rfl
  -- We rewrite the number 2 as the successor of 1, and 1 as the successor of 0. Now was know that 'succ (succ z) ≤ succ (succ 0)' and the goal to 'succ (succ z) = 0 ∨ succ (succ z) = succ 0 ∨ succ (succ z) = succ (succ 0)'.
  rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢
  -- We simplify succ (succ z) <= succ (succ 0) to the assumption that the succ z <= succ 0.
  apply succ_le_succ at hx
  -- We simplify succ z <= succ 0 to z <= 0.
  apply succ_le_succ at hx
  -- We apply the property that if z is less than or equal to 0, then z must be equal to 0.
  apply le_zero at hx
  -- We substitute z with 0 in the goal, resulting in the goal succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0).
  rw [hx]
  -- We choose to prove the right side of the disjunction, which is succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0).
  right
  -- We choose to prove the right side of this disjunction, which is succ (succ 0) = succ (succ 0).
  right
  -- We have that succ (succ 0) = succ (succ 0), so we can use reflexivity to prove the goal.
  rfl

-- Proof Statement: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem le_two_dev_1 (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- Either x = 0 or x = succ y for some natural number y.
  cases x with y
  -- In the former case, we need to show 0 = 0 ∨ 0 = 1 ∨ 0 = 2, and we choose to show 0 = 0.
  left
  -- This is clear by reflexivity.
  rfl
  -- In the latter case, either y = 0 or y = succ z for some natural number z.
  cases y with z
  -- In the former case, we must show succ 0 = 0 ∨ succ 0 = 1 ∨ succ 0 = 2, and we choose to prove succ 0 = 1 ∨ succ 0 = 2
  right
  -- To prove succ 0 = 1 ∨ succ 0 = 2, we choose to prove succ 0 = 1
  left
  -- Rewriting using a theorem, need to show show succ 0 = succ 0.
  rw [one_eq_succ_zero]
  -- This is clear by reflexivity.
  rfl
  -- In the latter case, we substitute 2 = succ 1 and 1 = succ 0 into what we know and what we have to show.
  rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢
  -- We know that succ (succ z) ≤ succ (succ 0), so usinig a theorem we know succ z ≤ succ 0.
  apply succ_le_succ at hx
  -- We know that succ z ≤ succ 0, so using a theorem we know that z ≤ 0.
  apply succ_le_succ at hx
  -- Since z ≤ 0, using a theorem, z = 0.
  apply le_zero at hx
  -- We subsitute z = 0 into what we want to show.
  rw [hx]
  -- So, we need to show that succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0), so we choose to show that succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0)
  right
  -- We need to show that succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0), so we choose to show that succ (succ 0) = succ (succ 0)
  right
  -- But LHS = RHS, so this follows by reflexivity.
  rfl

-- Proof Statement: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem le_two_dev_2 (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- x = 0 (case 1) or x = succ y (case 2) for some natural number y
  cases x with y
  -- 0 = 0 ∨ 0 = 1 ∨ 0 = 2 -> 0 = 0
  left
  -- lhs = rhs
  rfl
  -- y = 0 (case 1) or y = succ z (case 2) for some natural number z
  cases y with z
  -- succ 0 = 0 ∨ succ 0 = 1 ∨ succ 0 = 2 -> succ 0 = 1 ∨ succ 0 = 2
  right
  -- succ 0 = 1 ∨ succ 0 = 2 -> succ 0 = 1
  left
  -- succ 0 = 1 -> succ 0 = succ 0
  rw [one_eq_succ_zero]
  -- lhs = rhs
  rfl
  -- succ (succ z) ≤ 2 -> succ (succ z) ≤ succ 1 -> succ (succ z) ≤ succ (succ 0); ... = 0 ∨ ... = 1 ∨ ... = 2 -> ... = 0 ∨ ... = 1 ∨ ... = succ 1 -> ... = 0 ∨ ... = succ 0 ∨ ... = succ (succ 0)
  rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢
  -- succ (succ z) ≤ succ (succ 0) -> succ z ≤ succ 0
  apply succ_le_succ at hx
  -- succ z ≤ succ 0 -> z ≤ 0
  apply succ_le_succ at hx
  -- z ≤ 0 -> z = 0
  apply le_zero at hx
  -- succ (succ z) = 0 ∨ succ (succ z) = succ 0 ∨ succ (succ z) = succ (succ 0) -> succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0)
  rw [hx]
  -- succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0) -> succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0)
  right
  -- succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0) -> succ (succ 0) = succ (succ 0)
  right
  -- lhs = rhs
  rfl

end MyNat
