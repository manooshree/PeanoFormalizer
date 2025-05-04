import Game.Levels.Implication
import Game.Levels.Algorithm


World "AdvAddition"
Level 1
Title "add_right_cancel"
namespace MyNat

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a + d = b + d. There are now two proof goals, prove base case: a + 0 = b + 0 and inductive step: a + succ (d) = b + succ (d) implies a = b.
  induction n with d hd
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = b + 0. The goal now is to prove that a = b.
  intro h
  -- Repeatedly apply the rewrite rule add_zero to the hypothesis h, which simplifies any terms of the form x + 0 in h to x. In this case
  repeat rw [add_zero] at h
  -- Apply the hypothesis 'h' to the goal, changing it to: if 'a + succ d' equals 'b + succ d', then 'a' equals 'b'
  exact h
  -- Introduce a hypothesis h: a + succ d = b + succ d. Now the goal is to prove a = b given this hypothesis.
  intro h
  -- For any natural numbers x and y, x + succ y = succ (x + y). Applying this repeatedly simplifies the hypothesis but leaves the goal state a = b unchanged.
  repeat rw [add_succ] at h
  -- If succ a = succ b, then a = b which simplifies the hypotheses.
  apply succ_inj at h
  -- Apply the inductive hypothesis 'hd' at the hypothesis 'h'. This simplifies the hypothesis to a = b.
  apply hd at h
  -- h proves the goal a = b so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
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
  -- We use the theorem that n + succ m = succ (n + m) to change a + succ d = b + succ d into succ (a + d) = succ (b + d).
  repeat rw [add_succ] at h
  -- So, succ (a + d) = succ (b + d), but because succ is injective, we have that a + d = b + d.
  apply succ_inj at h
  -- The inductive hypothesis states that a + d = b + d → a = b and we know a + d = b + d, so by modus ponens, a = b.
  apply hd at h
  -- So a = b, which concludes the inductive step.
  exact h

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
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
  -- succ (a + d) = succ (b + d) -> a + d = b + d
  apply succ_inj at h
  -- a + d = b + d -> a = b by inductive hypothesis
  apply hd at h
  -- a = b, as desired
  exact h

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  -- Rewrite the goal by repeatedly swapping the addition operands in the left side of both equations, changing n + a = n + b to a + n = b + n.
  repeat rw [add_comm n]
  -- Assume that the statement 'a + n = b + n' is true and denote it as 'h'. Then, our new goal is to prove that 'a = b'.
  intro h
  -- Simplify the hypothesis 'h' using the theorem 'add_right_cancel' assuming the theorem is true, which leaves the goal state unchanged as 'a = b'
  apply add_right_cancel at h
  -- h proves the goal a = b so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_1 (a b n : ℕ) : n + a = n + b → a = b := by
  -- We use the commutativity of addition to change n + a = n + b into a + n = b + n.
  repeat rw [add_comm n]
  -- So, we just need to show that a + n = b + n → a = b. We start by assuming a + n = b + n.
  intro h
  -- By the theorem that a + n = b + n -> a = b, we have that a = b.
  apply add_right_cancel at h
  -- So, a = b, as desired.
  exact h

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_2 (a b n : ℕ) : n + a = n + b → a = b := by
  -- (n + a = n + b → a = b) -> (a + n = b + n → a = b)
  repeat rw [add_comm n]
  -- assume a + n = b + n
  intro h
  -- a + n = b + n -> a = b
  apply add_right_cancel at h
  -- a = b, as desired
  exact h

-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  -- Assume that x + y = y as our hypothesis h, and then prove that x = 0.
  intro h
  -- Rewrite the second occurrence of the theorem 'zero_add y' in reverse in the hypothesis 'h', but the goal 'x = 0' remains unchanged.
  nth_rewrite 2 [← zero_add y] at h
  -- If a + n = b + n, then a = b. So, in our case, if x + y = 0 + y, then x = 0.
  apply add_right_cancel at h
  -- h proves the goal x = 0 so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self_dev_1 (x y : ℕ) : x + y = y → x = 0 := by
  -- To show x + y = y → x = 0, we begin by assuming x + y = y.
  intro h
  -- We use the fact that 0 + n = n to change x + y = y into x + y = 0 + y.
  nth_rewrite 2 [← zero_add y] at h
  -- We use the theorem that a + n = b + n → a = b on the fact x + y = 0 + y.
  apply add_right_cancel at h
  -- So, x = 0, as desired.
  exact h

-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self_dev_2 (x y : ℕ) : x + y = y → x = 0 := by
  -- assume x + y = y
  intro h
  -- x + y = y -> x + y = 0 + y
  nth_rewrite 2 [← zero_add y] at h
  -- x + y = 0 + y -> x = 0
  apply add_right_cancel at h
  -- x = 0, as desired
  exact h

-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  -- Assume that x + y = x is true, then we need to prove that y = 0.
  intro h
  -- Rewrite the expression in hypothesis h using the add_comm theorem, which states that addition is commutative i.e., for all natural numbers a and b, a + b = b + a.
  rw [add_comm] at h
  -- For any natural numbers x, y: x + y = y implies x = 0. So, in our case, it implies that if y = 0.
  apply add_left_eq_self at h
  -- h proves the goal y = 0 so we can use it to finish the proof
  exact h

-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self_dev_1 (x y : ℕ) : x + y = x → y = 0 := by
  -- To show x + y = x → y = 0, we start by assuming x + y = x.
  intro h
  -- By the commutativity of addition, we know that y + x = x.
  rw [add_comm] at h
  -- We apply the theorem that a + b = b implies that a = 0.
  apply add_left_eq_self at h
  -- So, y = 0, as desired.
  exact h

-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self_dev_2 (x y : ℕ) : x + y = x → y = 0 := by
  -- assume x + y = x
  intro h
  -- x + y = x -> y + x = x
  rw [add_comm] at h
  -- y + x = x -> y = 0
  apply add_left_eq_self at h
  -- y = 0, as desired.
  exact h

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Split the natural number 'b' into two cases: 'b' is zero, and 'b' is the successor of another natural number 'd'.
  cases b with d
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = 0. The goal now is to prove that a = 0.
  intro h
  -- Repeatedly apply the theorem that adding zero to any number does not change its value to the hypothesis h.
  rw [add_zero] at h
  -- We use the hypothesis 'h' which is a proof that 'a = 0' to close the current goal. The new goal is now to prove that 'a + succ d = 0' implies 'a = 0'.
  exact h
  -- Assume that the hypothesis 'h' is true, that is, a + succ d = 0. The goal now is to prove that a = 0.
  intro h
  -- For any natural numbers x and y, x + succ y = succ (x + y). Applying this repeatedly simplifies the hypothesis but leaves the goal state a = 0 unchanged.
  rw [add_succ] at h
  -- Swap the left-hand side and the right-hand side of the equality in the hypothesis.
  symm at h
  -- Apply the theorem that states that the successor of any natural number cannot equal 0 to our hypothesis h which shows that h is false.
  apply zero_ne_succ at h
  -- Since h is a proof of False, and there are no ways to construct False so we have our contradiction and can close the proof
  cases h

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
  -- But since 0 is not the successor of anything, we have a contradiction/falsehood.
  apply zero_ne_succ at h
  -- Since a contradiction/falsehood implies anything, we are done.
  cases h

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
  -- a + succ d = 0 -> succ (a + d) = 0
  rw [add_succ] at h
  -- succ (a + d) = 0 -> 0 = succ (a + d)
  symm at h
  -- 0 = succ (a + d) -> False
  apply zero_ne_succ at h
  -- False -> anything
  cases h

-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  -- Rewrite the goal by swapping the addition operands in the left side of both equations, changing a + b = 0 to b + a = 0.
  rw [add_comm]
  -- Apply the theorem that states that if a + b = 0, then b = 0 for all natural numbers.
  exact add_right_eq_zero b a

-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_1 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- By the commutativity of addition, it suffices to show that b + a = 0 → b = 0
  rw [add_comm]
  -- But this is exactly the same as the theorem that a + b = 0 → a = 0, so we are done.
  exact add_right_eq_zero b a

-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_2 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- (a + b = 0 → b = 0) -> (b + a = 0 → b = 0)
  rw [add_comm]
  -- b + a = 0 → b = 0 by a previous theorem, so done
  exact add_right_eq_zero b a

end MyNat
