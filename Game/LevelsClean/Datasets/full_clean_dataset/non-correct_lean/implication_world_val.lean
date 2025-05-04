import Game.LevelsClean.AdditionClean
import Game.MyNat.PeanoAxioms

namespace MyNat

-- Theorem Declaration: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_2_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- We simplify the hypothesis of 0 + x = 0 + y + 2 to x = 0 + x + 2.
  rw [zero_add] at h
  -- So, x = y + 2, which is exactly what we wanted to prove.
  exact h

-- Theorem Declaration: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_2_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- 0 + x = 0 + y + 2 -> x = 0 + y + 2
  rw [zero_add] at h
  -- x = y + 2
  exact h

-- Theorem Declaration: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_3_dev_1 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- Simplify 0 + x = 0 + y + 2 to x = y + 2
  repeat rw [zero_add] at h

-- Theorem Declaration: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
theorem exact_3_dev_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  -- 0 + x = 0 + y + 2 -> x = y + 2
  repeat rw [zero_add] at h

-- Theorem Declaration: For some x and y which are natural numbers, given that  x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_1 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- x = 37 → y = 42 and x = 37, so by modus ponens, y = 42.
  apply h2 at h1

-- Theorem Declaration: For some x and y which are natural numbers, given that  x = 37 and that x = 37 implied y = 42, prove y = 42
theorem exact_4_dev_2 (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  -- x = 37, x = 37 -> y = 42 => y = 42
  apply h2 at h1

-- Theorem Declaration: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- We replace 4 with succ 3 in x + 1 = 4.
  rw [four_eq_succ_three] at h
  -- We replace x + 1 with succ x in x + 1 = succ 3.
  rw [←succ_eq_add_one] at h
  -- So, x = 3, which is exactly what we wanted to prove.
  exact h

-- Theorem Declaration: For some x which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_5_dev_2 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- x + 1 = 4 -> x + 1 = succ 3
  rw [four_eq_succ_three] at h
  -- x + 1 = 4 -> succ x = succ 3
  rw [←succ_eq_add_one] at h
  -- x = 3
  exact h

-- Theorem Declaration: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6_dev_1 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- By the injectivity of succ, it suffices to prove succ x = succ 3
  apply succ_inj
  -- We replace succ 3 with 4 in x + 1 = succ 3.
  rw [← four_eq_succ_three]
  -- So, we need to show x + 1 = 4, which is true by hypothesis.
  exact h

-- Theorem Declaration: For some x, which is a natural number, given x + 1 = 4, prove that x = 3
theorem exact_6_dev_2 (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- x = 3 <- succ x = succ 3
  apply succ_inj
  -- succ x = succ 3 -> x + 1 = succ 3
  rw [succ_eq_add_one]
  -- x + 1 = 4
  exact h

-- Theorem Declaration: For some x which is a natural number, prove that x = 37 implies x = 37
theorem exact_7_dev_1 (x : ℕ) : x = 37 → x = 37 := by
  -- Consider the hypothesis x = 37.
  intro h

-- Theorem Declaration: For some x which is a natural number, prove that x = 37 implies x = 37
theorem exact_7_dev_2 (x : ℕ) : x = 37 → x = 37 := by
  -- assume x = 37
  intro h

-- Theorem Declaration: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8_dev_1 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- Consider the hypothesis x + 1 = y + 1.
  intro h
  -- Change the + 1s to succs in x + 1 = y + 1.
  repeat rw [← succ_eq_add_one] at h
  -- Thus, x = y, which is exactly what we wanted to show.
  exact h

-- Theorem Declaration: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_8_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- assume x + 1 = y + 1
  intro h
  -- succ x = succ y -> x = y
  apply succ_inj at h
  -- x = y
  exact h

-- Theorem Declaration: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_1 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- Consider the hypothesis x + 1 = y + 1
  intro h
  -- By the injectivity of succ, it suffices to show that succ x = succ y
  apply succ_inj
  -- So we want to show x + 1 = y + 1, which is true by hypothesis
  exact h

-- Theorem Declaration: For some x and which are natural numbers, prove that x + 1 = y + 1 implies x = y
theorem exact_9_dev_2 (x : ℕ) : x + 1 = y + 1 → x = y := by
  -- assume x + 1 = y + 1
  intro h
  -- succ x = succ y -> x + 1 = y + 1
  repeat rw [succ_eq_add_one]
  -- x + 1 = y + 1
  exact h

-- Theorem Declaration: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_1 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- We have x ≠ y (which really means x = y -> False), and we know x = y, so by modus ponens, we know False
  apply h2 at h1

-- Theorem Declaration: For some x and which are natural numbers, prove that both x = y and x ≠ y cannot be true
theorem exact_10_dev_2 (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  -- x = y and x ≠ y -> False
  apply h2 at h1

-- Theorem Declaration: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one_dev_1 : (0 : ℕ) ≠ 1 := by
  -- To show 0 ≠ 1, we must assume 0 = 1 and derive a contradiction/falsehood
  intro h
  -- So, we have a falsehood, as desired.
  exact h

-- Theorem Declaration: Given that 0 is a natural number, prove that 0 ≠ 1
theorem zero_ne_one_dev_2 : (0 : ℕ) ≠ 1 := by
  -- assume 0 = 1
  intro h
  -- False
  exact h

-- Theorem Declaration: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero_dev_1 : (1 : ℕ) ≠ 0 := by
  -- Instead of showing 1 ≠ 0, we can show 0 ≠ 1
  symm

-- Theorem Declaration: Given that 1 is a natural number, prove that 1 ≠ 0
theorem one_ne_zero_dev_2 : (1 : ℕ) ≠ 0 := by
  -- 1 ≠ 0 <- 0 ≠ 1
  symm

-- Theorem Declaration: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five_dev_1 : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- We must assume succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0)))) and derive a contradiction/falsehood.
  intro h
  -- Using our previous theorems, we can change succ (succ 0) + succ (succ 0) into succ (succ (succ (succ 0)))
  rw [add_succ, add_succ, add_zero] at h
  -- By the injectivity of succ, we know that 0 = succ 0
  repeat apply succ_inj at h
  -- Thus, we have a falsehood/contradiction, which is what we wanted to show
  exact h

-- Theorem Declaration: Prove that 2 + 2 ≠ 5;  written in successor terms: succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0))))
theorem two_five_dev_2 : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  -- assume succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0))))
  intro h
  -- succ (succ 0) + succ (succ 0) = succ (succ (succ (succ (succ 0)))) -> succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0))))
  rw [add_succ, add_succ, add_zero] at h
  -- succ (succ (succ (succ 0))) = succ (succ (succ (succ (succ 0)))) -> 0 = succ 0
  repeat apply succ_inj at h
  -- False
  exact h

end MyNat
