import Game.LevelsClean.AdditionClean
import Game.MyNat.PeanoAxioms

namespace MyNat

-- Proof Statement: Prove that given some natural numbers x, y, z;  x + y = 37. We are given that x + y = 37 and 3 * x + z = 42
theorem exact (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
-- We can prove x + y = 37, using our given statement, which says exactly that x + y = 37, and complete the proof
  exact h1

-- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
theorem exact_dev_1 (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- We are given that x + y = 37, so we are done.
  exact h1

-- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
theorem exact_dev_2 (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  -- x + y = 37
  exact h1

-- Proof Statement: For some natural number x, prove x = y + 2. We are given that 0 + x = 0 + y + 2
theorem exact_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Rewrite 0 + x in the LHS of the hypothesis to x
  rw [zero_add] at h
  -- Rewrite 0 + y to y in the RHS of the hypothesis
  rw [zero_add] at h
  -- Our simplified hypothesis is now x = y + 2, we have shown exactly our goal and can complete the proof
  exact h

-- Proof Statement: For some natural number x, prove x = y + 2. We are given that  0 + x = 0 + y + 2
theorem exact_2_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- We simplify the given statement of 0 + x = 0 + y + 2 to x = y + 2.
  rw [zero_add, zero_add] at h
  -- So, x = y + 2, which is exactly our proof goal.
  exact h

-- Proof Statement: For some natural number x, prove x = y + 2. We are given that  0 + x = 0 + y + 2
theorem exact_2_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- proof goal 0 + x = y + 2
  rw [← zero_add x]
  -- proof goal 0 + x = 0 + y + 2
  rw [← zero_add y]
  -- hypothesis (0 + x = 0 + y + 2) = proof goal (0 + x = 0 + y + 2)
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 3, prove x = y + 3
theorem exact_3 (x : ℕ) (h : 0 + x = 0 + y + 3) : x = y + 3 := by
  -- Rewrite 0 + x in the LHS of our given statement, 0 + x = 0 + y + 3, to x and 0 + y + 3 to y + 3 in the RHS of the given statement
  repeat rw [zero_add] at h
  -- Our simplified hypothesis is now x = y + 3, we can use this exactly to complete the proof
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 3, prove x = y + 3
theorem exact_3_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 3) : x = y + 3 := by
  -- Simplify LHS of 0 + x = 0 + y + 3 to x = 0 + y + 3
  rw [zero_add] at h
  -- Simplify RHS of x = 0 + y + 3 to x = y + 3
  rw [zero_add] at h
  -- So, x = y + 3, which is exactly what we wanted to prove.
  exact h

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 3, prove x = y + 3
theorem exact_3_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 3) : x = y + 3 := by
  -- given hypothesis x = y + 3
  repeat rw [zero_add] at h
  -- x = y + 3
  exact h

-- Proof Statement: For some x and y which are natural numbers, given that x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- Starting with the given statement that x = 37, use the given implication that x = 37 → y = 42, to deduce that y = 42
  apply h2 at h1
  -- We can exactly prove that y = 42 with our given facts, to complete the proof
  exact h1

-- Proof Statement: For some x and y which are natural numbers, given that x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_1 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- x = 37 → y = 42 and x = 37, so by modus ponens, y = 42
  apply h2 at h1
  -- So y = 42, which is exactly what we wanted to prove.
  exact h1

-- Proof Statement: For some x and y which are natural numbers, given that x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_2 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- given x = 37 and x = 37 -> y = 42 , y = 42
  apply h2 at h1
  -- y = 42
  exact h1

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Rewrite 4 as succ 3 in the given statement x + 1 = 4, changing it to x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- Rewrite LHS in the given hypothesis such that x + 1 is succ x, then given statement is succ x = succ 3.
  rw [←succ_eq_add_one] at h
  -- Apply the injectivity of the successor function to the given succ x = succ 3, simplifying to x = 3.
  apply succ_inj at h
  -- We can exactly prove that x = 3 with our given facts, to complete the proof
  exact h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- We replace 4 with succ 3 in x + 1 = 4 in the given statement.
  rw [four_eq_succ_three] at h
  -- We replace x + 1 with succ x in the given statement (x + 1 = 4).
  rw [←succ_eq_add_one] at h
  -- By the injectivity of successor function, x = 3.
  apply succ_inj at h
  -- So, x = 3, which is exactly what we wanted to prove.
  exact h

-- Proof Statement: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_2 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- given statement x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- given statement succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- given statement x = 3
  apply succ_inj at h
  -- x = 3
  exact h

-- Proof Statement: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- Expand the proof goal to succ x = succ 3 using the injectivity of the successor function
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
  -- expand goal succ x = succ 3
  apply succ_inj
  -- x + 1 = succ 3
  rw [succ_eq_add_one]
  --  x + 1 = 4
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
  -- Consider the given hypothesis x + 1 = y + 1.
  intro h
  -- Rewrite x + 1 to succ x in the given hypothesis
  rw [← succ_eq_add_one] at h
  -- Rewrite y + 1 to succ x in the given hypothesis
  rw [← succ_eq_add_one] at h
  -- Apply injectivity of the successor function, simplify to x = y
  apply succ_inj at h
  -- Thus, x = y, which is exactly what we wanted to show.
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- given that x + 1 = y + 1
  intro h
  -- succ x = y + 1
  rw [← succ_eq_add_one x] at h
  -- succ x = succ y
  rw [← succ_eq_add_one y] at h
  -- x = y
  apply succ_inj at h
  -- x = y
  exact h


-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- We assume that x + 1 = y + 1
  intro h
  -- Rewrite the proof goal to 'succ x = succ y' using the injectivity of the successor function
  apply succ_inj
  -- Rewrite all instances of succ x and succ y as x + 1 and y + 1, the proof goal is now x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- We can exactly show how x = y equates to x + 1 = y + 1, completing the proof
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_1 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- Assume the hypothesis x + 1 = y + 1
  intro h
  -- By the injectivity of succ, it suffices to show that succ x = succ y
  apply succ_inj
  -- Rewrite using successor definition, succ x as x + 1 and succ y as y + 1
  rw [succ_eq_add_one, succ_eq_add_one]
  -- Now we show x + 1 = y + 1, which is true by hypothesis
  exact h

-- Proof Statement: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- assume x + 1 = y + 1
  intro h
  -- succ x = succ y
  apply succ_inj
  -- x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- x + 1 = y + 1
  exact h

-- Proof Statement: For some x and y which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We apply the assumption x ≠ y to the given statement that x = y, which contradicts and results in a falsehood
  apply h2 at h1
  -- We have proven that both x = y and x ≠ y cannot be true, completing the proof
  exact h1

-- Proof Statement: For some x and y which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_1 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We have x ≠ y (which really means x = y -> False), and we know x = y, so by modus ponens, we know False
  apply h2 at h1
  -- So we have a falsehood/contradiction, which is exactly what we wanted to show.
  exact h1

-- Proof Statement: For some x and y which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_2 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- x = y AND x ≠ y is False
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
  -- To show 0 ≠ 1, we assume 0 = 1 and derive a contradiction/falsehood
  intro h
  -- Rewrite 1 as the successor of 0 in our assumption
  rw [one_eq_succ_zero] at h
  -- But 0 = succ 0 implies a falsehood by the Peano axiom that zero is not the successor of any natural number
  apply zero_ne_succ at h
  -- So, we have a falsehood, and the proof is complete.
  exact h

-- Proof Statement: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one_dev_2 : (0 : ℕ) ≠ 1 := by
  -- assume 0 = 1
  intro h
  -- Assumption is False
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
  -- Assume 1 = 0, we will prove this is a contradiction and false
  intro h
  -- Use the fact that 1 is the successor of zero in our assumption, which is now succ 0 = 0
  rw [one_eq_succ_zero] at h
  -- Use the definition of the successor function to rewrite the assumption as 0 + 1 = 0
  rw [succ_eq_add_one] at h
  -- Instead of proving 0 + 1 = 0, we will prove the equal statement that 0 = 0 + 1
  symm at h
  -- Simplify 0 + 1 to 0 via the zero property of addition. Assumption is now 0 = 1
  rw [zero_add] at h
  -- 0 = 1 is false, our assumption is false
  apply zero_ne_one at h
  -- We have proven our assumption false and completed the proof
  exact h

-- Proof Statement: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero_dev_2 : (1 : ℕ) ≠ 0 := by
  -- Assume contradiction, 1 = 0
  intro h
  -- Rewrite contradiction 0 = 1
  symm at h
  -- 0 ≠ 1
  apply zero_ne_one at h
  -- False
  exact h

-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- Assume the contradiction that succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
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
  -- Rewrite the proof goal using the definitions of successor and zero addition. Proof goal is now succ (succ (succ (succ 0))) ≠ succ (succ (succ (succ (succ 0))))
  rw [add_succ, add_succ, add_zero]
  -- Assume the contradiction, succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0))))
  intro h
  -- Apply injectivity of the successor function and simplify contradiction to 0 = succ (0)
  repeat apply succ_inj at h
  -- By the Peano axiom, 0 cannot be equal to the successor of a natural number, thus our contradiction is false
  apply zero_ne_succ
  -- We show our contradiction is indeed false, and the proof is complete
  exact h


-- Proof Statement: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five_dev_2 : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- assume contradiction succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- succ (succ (succ (succ (0)) + 0)) = succ (succ (succ (succ (succ 0))))
  rw [add_succ, add_succ] at h
  -- succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0))))
  rw [add_zero] at h
  -- 0 = succ 0
  repeat apply succ_inj at h
  -- False
  apply zero_ne_succ at h
  -- False, proof is complete
  exact h
