import Game.Metadata
import Game.MyNat.LE
import Game.Tactic.Use
import Game.LevelsClean.AdvAdditionClean

namespace MyNat

-- Theorem Declaration: Prove that x ≤ x for any natural number x
theorem le_refl_dev_1 (x : ℕ) : x ≤ x := by
  -- By the definition of less than, x + n = x where n is some natural number. We set n to be 0
  use 0
  -- The LHS = RHS, so we can conclude the proof.
  rfl

-- Theorem Declaration: Prove that x ≤ x for any natural number x
theorem le_refl_dev_2 (x : ℕ) : x ≤ x := by
  -- x <= x -> x + 0 = x
  use 0
  -- x + 0 = x -> 0 + x = x
  rw [add_comm]
  -- LHS = RHS
  rfl

-- Theorem Declaration: Prove that 0 ≤ x for any natural number x
theorem zero_le_dev_1 (x : ℕ) : 0 ≤ x := by
  -- Using the definition of ≤ it suffices to show that x = 0 + x
  use x
  -- The LHS and RHS are equal, completing the proof.
  rfl

-- Theorem Declaration: Prove that 0 ≤ x for any natural number x
theorem zero_le_dev_2 (x : ℕ) : 0 ≤ x := by
  -- x = 0 + x
  use x
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove that x ≤ succ x for any natural number x
theorem le_succ_self_dev_1 (x : ℕ) : x ≤ succ x := by
  -- We simplify the claim to being succ x = x + 1 by using the case of 1.
  use _dev_1

-- Theorem Declaration: Prove that x ≤ succ x for any natural number x
theorem le_succ_self_dev_2 (x : ℕ) : x ≤ succ x := by
  -- succ x = x + _dev_1
  use _dev_1
  -- done
  rfl

-- Theorem Declaration: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem le_trans_dev_1 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Break down the assumption that x is less than or equal to y into a specific case where there exists a natural number 'a' such that y equals x plus 'a'.
  cases hxy with a ha
  -- Break down the assumption that y is less than or equal to z into a specific case where there exists a natural number 'b' such that z equals y plus 'b'.
  cases hyz with b hb
  -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
  use a + b
  -- Substitute y with x + a resulting in the equation x + a + b = x + (a + b).
  rw [ha]
  -- The goal is now to prove that x + a + b = x + (a + b), which can be proven by applying the theorem that states that addition is associative to the left-hand side of the goal.
  exact add_assoc x a b

-- Theorem Declaration: Prove that if x ≤ y and y ≤ z, then x ≤ z for any natural numbers x, y, and z
theorem le_trans_dev_2 (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- y = x + a
  cases hxy with a ha
  -- z = y + b
  cases hyz with b hb
  -- z = x + (a + b) -> y + b = x + (a + b)
  rw [hb]
  -- y + b = x + (a + b) -> (x + a) + b = x + (a + b)
  rw [ha]
  -- (x + a) + b = x + (a + b) by associativity
  exact add_assoc x a b

-- Theorem Declaration: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem le_zero_dev_1 (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- Using the definition of ≤, we have that 0 = x + y for some natural number y.
  cases hx with y hy
  -- Using the theorem that if a + b = 0, a = 0, we have that x = 0.
  apply add_right_eq_zero at hy
  -- So we know that x = 0, which is exactly what we wanted to prove.
  exact hy

-- Theorem Declaration: Prove that if x ≤ 0, then x = 0 for any natural number x
theorem le_zero_dev_2 (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  -- 0 = x + y
  cases hx with y hy
  -- 0 = x + y -> x + y = 0
  symm at hy
  -- done
  exact hy

-- Theorem Declaration: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
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
  -- We substitute a in the equation x = x + a with zero, as given shown above, changing our goal to prove that x equals x.
  rw [hb, add_zero]
  -- The goal is now to prove that x equals x, which is true by reflexivity.
  rfl

-- Theorem Declaration: Prove that if x is less than or equal to y and y is less than or equal to x, then x equals y.
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
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem orr_symm_dev_1 (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  -- We have that either x = 37 or y = 42.
  cases h with hx hy
  -- In the first case, since we have to prove a disjunction, we choose to prove the right side.
  right
  -- We need to show x = 37, but this is exactly what we already know.
  exact hx
  -- We need to show y = 42, but this is exactly what we already know.
  exact hy

-- Theorem Declaration: Prove that if x equals 37 or y equals 42, then y equals 42 or x equals 37.
theorem orr_symm_dev_2 (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  -- x = 37 ∨ y = 42 -> x = 37 (case 1) or y = 42 (case 2)
  cases h with hx hy
  -- case 1: y = 42 ∨ x = 37 → x = 37
  right
  -- case 2: y = 42 ∨ x = 37 → y = 4_dev_2
  left
  -- done
  exact hy

-- Theorem Declaration: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem le_total_dev_1 (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- We begin with induction on y.
  induction y with d hd
  -- For the base case, we need to prove x ≤ 0 ∨ 0 ≤ x, and we choose to show 0 ≤ x.
  right
  -- This follows from the theorem that 0 ≤ x for any natural number x.
  exact zero_le x
  -- For the inductive step, we are given that x ≤ d ∨ d ≤ x, so we do a proof by cases.
  cases hd with h1 h_dev_2
  -- In the first case, we need to show that x ≤ succ d ∨ succ d ≤ x, and we choose to show x ≤ succ d.
  left
  -- Using the definition of ≤, d = x + e for some natural number e.
  cases h1 with e h_dev_1
  -- We rewrite the goal so that we just need to show that x ≤ succ (x + e)
  rw [h1]
  -- Using the definition of ≤, it suffices to show that succ (x + e) = x + (e + 1)
  use e + _dev_1
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
  use _dev_1
  -- But succ d = d + 1 is a theorem we proved earlier, so we are done.
  exact succ_eq_add_one d
  -- In th latter case, we need to show that x ≤ succ d ∨ succ d ≤ x, so we choose to show succ d ≤ x.
  right
  -- Using the definition of ≤, it suffices to show x = succ d + a.
  use a
  -- We want to show x = succ d + a, so by rewriting we can instead show x = succ (d + a)
  rw [succ_add]
  -- But this is exactly what we just showed that we know.
  exact he

-- Theorem Declaration: Prove that for any natural numbers x and y, either x is less than or equal to y or y is less than or equal to x.
theorem le_total_dev_2 (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  -- induction on y
  induction y with d hd
  -- show the right side of the disjunction
  right
  -- 0 ≤ x, so this case is done
  exact zero_le x
  -- x ≤ d ∨ d ≤ x -> x ≤ d (case 1) or d ≤ x (case 2)
  cases hd with h1 h_dev_2
  -- x ≤ succ d ∨ succ d ≤ x -> x ≤ succ d
  left
  -- x ≤ d -> d = x + e for some natural number e
  cases h1 with e h_dev_1
  -- x ≤ succ d -> x ≤ succ (x + e)
  rw [h1]
  -- x ≤ succ (x + e) -> succ (x + e) = x + (e + 1)
  use e + _dev_1
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
  -- d ≤ succ d -> succ d = d + _dev_1
  use _dev_1
  -- succ d = d + 1 by a theorem
  exact succ_eq_add_one d
  -- x ≤ succ d ∨ succ d ≤ x → succ d ≤ x
  right
  -- succ d ≤ x -> x = succ d + a
  use a
  -- x = d + succ a -> x = succ (d + a)
  rw [add_succ] at he
  -- x = succ (d + a) by a fact we know right now
  exact he

-- Theorem Declaration: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem succ_le_succ_dev_1 (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- Using the definition of ≤, we have that succ y = succ x + d for some natural number d
  cases hx with d hd
  -- Using the definition of ≤, to prove x ≤ y, it suffices to show that y = x + d
  use d
  -- Since succ y = succ x + d, we have succ y = succ (x + d)
  rw [succ_add] at hd
  -- Thus, we know y = x + d, which is exactly what we wanted to prove.
  exact hd

-- Theorem Declaration: Prove that if the successor of x is less than or equal to the successor of y, then x is less than or equal to y.
theorem succ_le_succ_dev_2 (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  -- succ x ≤ succ y -> succ y = succ x + d for some natural number d
  cases hx with d hd
  -- succ y = succ x + d -> succ y = succ (x + d)
  rw [succ_add] at hd
  -- succ y = succ (x + d) -> y = x + d
  apply succ_inj at hd
  -- thus, y = x + d, so we are done
  exact hd

-- Theorem Declaration: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
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
  -- Thus, our goal to show succ y = 0 ∨ succ y = succ 0 is really just succ 0 = 0 ∨ succ 0 = succ 0.
  rw [hx]
  -- To show succ 0 = 0 ∨ succ 0 = succ 0, we choose to show succ 0 = succ 0.
  right
  -- But this just follows from reflexivity.
  rfl

-- Theorem Declaration: Prove that if x is less than or equal to 1, then x is equal to 0 or 1.
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
  -- succ y = 0 ∨ succ y = succ 0 -> succ 0 = 0 ∨ succ 0 = succ 0
  rw [hx]
  -- succ 0 = 0 ∨ succ 0 = succ 0 -> succ 0 = succ 0
  right
  -- lhs = rhs
  rfl

-- Theorem Declaration: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem le_two_dev_1 (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- Either x = 0 or x = succ y for some natural number y.
  cases x with y
  -- In the former case, we need to show 0 = 0 ∨ 0 = 1 ∨ 0 = 2, and we choose to show 0 = 0.
  left
  -- This is clear by reflexivity.
  rfl
  -- In the latter case, either y = 0 or y = succ z for some natural number z.
  cases y with z
  -- In the former case, we must show succ 0 = 0 ∨ succ 0 = 1 ∨ succ 0 = 2, and we choose to prove succ 0 = 1 ∨ succ 0 = _dev_2
  right
  -- To prove succ 0 = 1 ∨ succ 0 = 2, we choose to prove succ 0 = _dev_1
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
  -- So, we need to show that succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0), so we choose to show that succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0)
  right
  -- We need to show that succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0), so we choose to show that succ (succ 0) = succ (succ 0)
  right
  -- But LHS = RHS, so this follows by reflexivity.
  rfl

-- Theorem Declaration: Prove that if x is less than or equal to 2, then x is equal to 0, 1, or 2.
theorem le_two_dev_2 (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  -- x = 0 (case 1) or x = succ y (case 2) for some natural number y
  cases x with y
  -- 0 = 0 ∨ 0 = 1 ∨ 0 = 2 -> 0 = 0
  left
  -- lhs = rhs
  rfl
  -- y = 0 (case 1) or y = succ z (case 2) for some natural number z
  cases y with z
  -- succ 0 = 0 ∨ succ 0 = 1 ∨ succ 0 = 2 -> succ 0 = 1 ∨ succ 0 = _dev_2
  right
  -- succ 0 = 1 ∨ succ 0 = 2 -> succ 0 = _dev_1
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
  -- succ (succ 0) = 0 ∨ succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0) -> succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0)
  right
  -- succ (succ 0) = succ 0 ∨ succ (succ 0) = succ (succ 0) -> succ (succ 0) = succ (succ 0)
  right
  -- lhs = rhs
  rfl

end MyNat
