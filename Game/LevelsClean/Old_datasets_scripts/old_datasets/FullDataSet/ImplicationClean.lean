import Game.Levels.Addition
import Game.MyNat.PeanoAxioms

namespace MyNat

-- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
theorem exact (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
-- We can prove x + y = 37, using our given statement, which says exactly that x + y = 37, and complete the proof
  exact h1

-- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
theorem exact_dev_1 (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- By hypothesis, we know x + y = 37, so we are done.
  exact h1

-- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
theorem exact_dev_2 (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- x + y = 37
  exact h1

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Rewrite 0 + x in the LHS of the hypothesis to x
  rw [zero_add] at h
  -- Rewrite 0 + y to y in the RHS of the hypothesis
  rw [zero_add] at h
  -- Our simplified hypothesis is now x = y + 2, we can use this exactly to complete the proof
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_2_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- We simplify the hypothesis of 0 + x = 0 + y + 2 to x = 0 + x + 2.
  rw [zero_add] at h
  -- We simplify the hypothesis of x = 0 + y + 2 to x = y + 2.
  rw [zero_add] at h
  -- So, x = y + 2, which is exactly what we wanted to prove.
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_2_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- 0 + x = 0 + y + 2 -> x = 0 + y + 2
  rw [zero_add] at h
  -- x = 0 + y + 2 -> x = y + 2
  rw [zero_add] at h
  -- x = y + 2
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_3 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Rewrite 0 + x in the LHS of our given,  0 + x = 0 + y + 2, to x and 0 + y to y in the RHS of the hypothesis
  repeat rw [zero_add] at h
  -- Our simplified hypothesis is now x = y + 2, we can use this exactly to complete the proof
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_3_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Simplify 0 + x = 0 + y + 2 to x = y + 2
  repeat rw [zero_add] at h
  -- So, x = y + 2, which is exactly what we wanted to prove.
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_3_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- 0 + x = 0 + y + 2 -> x = y + 2
  repeat rw [zero_add] at h
  -- x = y + 2
  exact h

-- Proof Statement: For some x and y which are natural numbers, given that  x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- Starting with the given x = 37, use the implication that x = 37 → y = 42 on the given, to deduce that y = 42
  apply h2 at h1
  -- We can exactly prove that y = 42 with our given facts, to complete the proof
  exact h1

-- Proof Statement: For some x and y which are natural numbers, given that  x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_1 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- x = 37 → y = 42 and x = 37, so by modus ponens, y = 42.
  apply h2 at h1
  -- So y = 42, which is exactly what we wanted to prove.
  exact h1

-- Proof Statement: For some x and y which are natural numbers, given that  x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_2 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- x = 37, x = 37 -> y = 42 => y = 42
  apply h2 at h1
  -- y = 42
  exact h1

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Rewrite 4 as succ 3 in the given x + 1 = 4, changing it to x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- Rewrite LHS such that x + 1 = succ 3 changes to succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- Apply the injectivity of the successor function to the given succ x = succ 3, simplifying to x = 3.
  apply succ_inj at h
  -- We can exactly prove that x = 3 with our given facts, to complete the proof
  exact h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- We replace 4 with succ 3 in x + 1 = 4.
  rw [four_eq_succ_three] at h
  -- We replace x + 1 with succ x in x + 1 = succ 3.
  rw [←succ_eq_add_one] at h
  -- By the injectivity of succ, x = 3.
  apply succ_inj at h
  -- So, x = 3, which is exactly what we wanted to prove.
  exact h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_2 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- x + 1 = 4 -> x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- x + 1 = 4 -> succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- succ x = succ 3 -> x = 3
  apply succ_inj at h
  -- x = 3
  exact h

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Change the proof goal to succ x = succ 3 using the injectivity of the successor function
  apply succ_inj
  -- Rewrite the RHS, replacing 'succ x' with 'x + 1'.
  rw [succ_eq_add_one]
  -- Simplify succ (3) to 4
  rw [← four_eq_succ_three]
  -- We can exactly show that x + 1 = 4 holds true, assuming x = 3, completing the proof
  exact h

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- By the injectivity of succ, it suffices to prove succ x = succ 3
  apply succ_inj
  -- We replace succ x with x + 1 in succ x = succ 3.
  rw [succ_eq_add_one]
  -- We replace succ 3 with 4 in x + 1 = succ 3.
  rw [← four_eq_succ_three]
  -- So, we need to show x + 1 = 4, which is true by hypothesis.
  exact h

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6_dev_2 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- x = 3 <- succ x = succ 3
  apply succ_inj
  -- succ x = succ 3 -> x + 1 = succ 3
  rw [succ_eq_add_one]
  -- x + 1 = succ 3 -> x + 1 = 4
  rw [← four_eq_succ_three]
  -- x + 1 = 4
  exact h

-- Proof Statement: For some x which is a natural number, prove that x = 37 implies x = 37
theorem exact_7 (x : ℕ) : x = 37 → x = 37 := by
  -- We assume that x = 37
  intro h
  -- We can use this to prove x = 37, completing the proof
  exact h

-- Proof Statement: For some x which is a natural number, prove that x = 37 implies x = 37
theorem exact_7_dev_1 (x : ℕ) : x = 37 → x = 37 := by
  -- Consider the hypothesis x = 37.
  intro h
  -- So, x = 37, which is what we want to show.
  exact h

-- Proof Statement: For some x which is a natural number, prove that x = 37 implies x = 37
theorem exact_7_dev_2 (x : ℕ) : x = 37 → x = 37 := by
  -- assume x = 37
  intro h
  -- x = 37
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite x + 1 and y + 1 to succ x and succ y in the LHS and RHS respectively
  repeat rw [← succ_eq_add_one] at h
  -- Apply the injectivity of the successor function to 'succ x = succ y', simplifying it to 'x = y'.
  apply succ_inj at h
  -- We can exactly show that x + 1 = y + 1 implies x = y, completing the proof
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8_dev_1 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- Consider the hypothesis x + 1 = y + 1.
  intro h
  -- Change the + 1s to succs in x + 1 = y + 1.
  repeat rw [← succ_eq_add_one] at h
  -- By the injectivity of succ, x = y.
  apply succ_inj at h
  -- Thus, x = y, which is exactly what we wanted to show.
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- assume x + 1 = y + 1
  intro h
  -- x + 1 = y + 1 -> succ x = succ y
  repeat rw [← succ_eq_add_one] at h
  -- succ x = succ y -> x = y
  apply succ_inj at h
  -- x = y
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite the proof goal to 'succ x = succ y' using the injectivity of the successor function
  apply succ_inj
  -- Rewrite all instances of succ x and succ y as x + 1 and y + 1, the equation is now x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- We can exactly show how x = y equates to x + 1 = y + 1, completing the proof
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_1 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- Consider the hypothesis x + 1 = y + 1
  intro h
  -- By the injectivity of succ, it suffices to show that succ x = succ y
  apply succ_inj
  -- We replace succ with + 1 in succ x = succ y
  repeat rw [succ_eq_add_one]
  -- So we want to show x + 1 = y + 1, which is true by hypothesis
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- assume x + 1 = y + 1
  intro h
  -- x = y <- succ x = succ y
  apply succ_inj
  -- succ x = succ y -> x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- x + 1 = y + 1
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We apply the assumption that x ≠ y to the hypothesis that x = y, which contradicts it and results in a falsehood
  apply h2 at h1
  -- We have proven that both x = y and x ≠ y cannot be true, completing the proof
  exact h1

-- Proof Statement: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_1 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We have x ≠ y (which really means x = y -> False), and we know x = y, so by modus ponens, we know False
  apply h2 at h1
  -- So we have a falsehood/contradiction, which is exactly what we wanted to show.
  exact h1

-- Proof Statement: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_2 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- x = y and x ≠ y -> False
  apply h2 at h1
  -- False
  exact h1

-- Proof Statement: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  -- Assume that 0 = 1, which is false
  intro h
  -- Apply the Peano axiom that zero is not the successor of any natural number to our assumption that 0 = 1, making it false
  apply zero_ne_succ at h
  -- We have proven that 0 = 1 is false or that 0 ≠ 1, completing the proof
  exact h

-- Proof Statement: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one_dev_1 : (0 : ℕ) ≠ 1 := by
  -- To show 0 ≠ 1, we must assume 0 = 1 and derive a contradiction/falsehood
  intro h
  -- But 0 = 1 implies a falsehood by the theorem that zero is not equal to the success of any natural number
  apply zero_ne_succ at h
  -- So, we have a falsehood, as desired.
  exact h

-- Proof Statement: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one_dev_2 : (0 : ℕ) ≠ 1 := by
  -- assume 0 = 1
  intro h
  -- 0 = 1 -> False
  apply zero_ne_succ at h
  -- False
  exact h

-- Proof Statement: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  -- Rewrite our proof goal to 0 ≠ 1
  symm
  -- Apply the proof that 0 ≠ 1 exactly to our proof goal, completing the proof
  exact zero_ne_one

-- Proof Statement: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero_dev_1 : (1 : ℕ) ≠ 0 := by
  -- Instead of showing 1 ≠ 0, we can show 0 ≠ 1
  symm
  -- But 0 ≠ 1 by a previous theorem.
  exact zero_ne_one

-- Proof Statement: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero_dev_2 : (1 : ℕ) ≠ 0 := by
  -- 1 ≠ 0 <- 0 ≠ 1
  symm
  -- 0 ≠ 1 by previous thm
  exact zero_ne_one

-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- Assume that succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- Rewrite the LHS of our assumption, transforming succ (succ 0) + succ (succ 0) to succ (succ (succ (succ 0)))
  rw [add_succ, add_succ, add_zero] at h
  -- Repeatedly apply the injectivity of the successor function to the assumption until we simplify the assumption equation to 0 = succ 0
  repeat apply succ_inj at h
  -- Apply the fact that zero is not equal to the successor of zero, showing our assumption is false
  apply zero_ne_succ at h
  -- We have shown that succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) is false, completing the proof
  exact h

-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five_dev_1 : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- We must assume succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0)))) and derive a contradiction/falsehood.
  intro h
  -- Using our previous theorems, we can change succ (succ 0) + succ (succ 0) into succ (succ (succ (succ 0)))
  rw [add_succ, add_succ, add_zero] at h
  -- By the injectivity of succ, we know that 0 = succ 0
  repeat apply succ_inj at h
  -- By 0 is not equal to the success of any natural number, so we have a falsehood/contradiction
  apply zero_ne_succ at h
  -- Thus, we have a falsehood/contradiction, which is what we wanted to show
  exact h

-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five_dev_2 : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- assume succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0)))) -> succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0))))
  rw [add_succ, add_succ, add_zero] at h
  -- succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0)))) -> 0 = succ 0
  repeat apply succ_inj at h
  -- 0 = succ 0 -> False
  apply zero_ne_succ at h
  -- False
  exact h
