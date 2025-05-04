import Game.LevelsClean.ImplicationClean
import Game.LevelsClean.AlgorithmClean


namespace MyNat

-- Theorem Declaration: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_right_cancel_dev_1 (a b n : ℕ) : a + n = b + n → a = b := by
  -- We start with induction on n.
  induction n with d hd
  -- For the base case, to show that a + 0 = b + 0 → a = b, we first assume a + 0 = b + 0.
  intro h
  -- We simplify a + 0 = b + 0 to a = b.
  repeat rw [add_zero] at h
  -- So a = b, which concludes the base case.
  exact h
  -- For the inductive step, we must show that a + succ d = b + succ d → a = b, so we start by assuming a + succ d = b + succ d.
  intro h
  -- So, succ (a + d) = succ (b + d), but because succ is injective, we have that a + d = b + d.
  apply succ_inj at h
  -- The inductive hypothesis states that a + d = b + d → a = b and we know a + d = b + d, so by modus ponens, a = b.
  apply hd at h
  -- So a = b, which concludes the inductive step.
  exact h

-- Theorem Declaration: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_right_cancel_dev_2 (a b n : ℕ) : a + n = b + n → a = b := by
  -- induct on n
  induction n with d hd
  -- assume a + 0 = b + 0
  intro h
  -- a + 0 = b + 0 -> a = b
  repeat rw [add_zero] at h
  -- a = b, as desired
  exact h
  -- assume a + succ d = b + succ d
  intro h
  -- a + succ d = b + succ d -> succ (a + d) = succ (b + d)
  repeat rw [add_succ] at h
  -- a + d = b + d -> a = b by inductive hypothesis
  apply hd at h
  -- a = b, as desired
  exact h

-- Theorem Declaration: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_1 (a b n : ℕ) : n + a = n + b → a = b := by
  -- We use the commutativity of addition to change n + a = n + b into a + n = b + n.
  repeat rw [add_comm n]
  -- By the theorem that a + n = b + n -> a = b, we have that a = b.
  apply add_right_cancel at h
  -- So, a = b, as desired.
  exact h

-- Theorem Declaration: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_2 (a b n : ℕ) : n + a = n + b → a = b := by
  -- (n + a = n + b → a = b) -> (a + n = b + n → a = b)
  repeat rw [add_comm n]
  -- assume a + n = b + n
  intro h
  -- a = b, as desired
  exact h

-- Theorem Declaration: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self_dev_1 (x y : ℕ) : x + y = y → x = 0 := by
  -- To show x + y = y → x = 0, we begin by assuming x + y = y.
  intro h
  -- We use the fact that 0 + n = n to change x + y = y into x + y = 0 + y.
  nth_rewrite 2 [← zero_add y] at h
  -- So, x = 0, as desired.
  exact h

-- Theorem Declaration: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self_dev_2 (x y : ℕ) : x + y = y → x = 0 := by
  -- assume x + y = y
  intro h
  -- x + y = 0 + y -> x = 0
  apply add_right_cancel at h
  -- x = 0, as desired
  exact h

-- Theorem Declaration: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self_dev_1 (x y : ℕ) : x + y = x → y = 0 := by
  -- To show x + y = x → y = 0, we start by assuming x + y = x.
  intro h
  -- We apply the theorem that a + b = b implies that a = 0.
  apply add_left_eq_self at h
  -- So, y = 0, as desired.
  exact h

-- Theorem Declaration: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self_dev_2 (x y : ℕ) : x + y = x → y = 0 := by
  -- assume x + y = x
  intro h
  -- y + x = x -> y = 0
  apply add_left_eq_self at h
  -- y = 0, as desired.
  exact h

-- Theorem Declaration:
theorem add_right_eq_zero_dev_1 (a b : ℕ) : a + b = 0 → a = 0 := by
  -- We have two cases: b = 0, or b = succ d for some natural number d.
  cases b with d
  -- In the former case, we must show that a + 0 = 0 → a = 0, so we start by assuming that a + 0 = 0.
  intro h
  -- We apply the theorem that n + 0 = n change a + 0 = 0 into a = 0.
  rw [add_zero] at h
  -- So, a = 0, which concludes this case of the theorem.
  exact h
  -- In the latter case, we must show that a + succ d = 0 → a = 0, so we start by assuming that a + succ d = 0.
  intro h
  -- Using the theorem that a + succ d = succ (a + d), we get that succ (a + d) = 0.
  rw [add_succ] at h
  -- By the symmetry of equality, we have that 0 = succ (a + d).
  symm at h
  -- Since a contradiction/falsehood implies anything, we are done.
  cases h

-- Theorem Declaration:
theorem add_right_eq_zero_dev_2 (a b : ℕ) : a + b = 0 → a = 0 := by
  -- either b = 0 or b = succ d for some natural number d
  cases b with d
  -- (case 1) assume a + 0 = 0
  intro h
  -- a + 0 = 0 -> a = 0
  rw [add_zero] at h
  -- a = 0, as desired
  exact h
  -- (case 2) assume a + succ d = 0
  intro h
  -- succ (a + d) = 0 -> 0 = succ (a + d)
  symm at h
  -- 0 = succ (a + d) -> False
  apply zero_ne_succ at h
  -- False -> anything
  cases h

-- Theorem Declaration: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_1 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- By the commutativity of addition, it suffices to show that b + a = 0 → b = 0
  rw [add_comm]

-- Theorem Declaration: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_2 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- (a + b = 0 → b = 0) -> (b + a = 0 → b = 0)
  rw [add_comm]

end MyNat
