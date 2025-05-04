import Game.LevelsClean.ImplicationClean
import Game.LevelsClean.AlgorithmClean

namespace MyNat

-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis a + d = b + d. There are now two proof goals, prove base case: a + 0 = b + 0 and inductive step: a + succ (d) = b + succ (d) implies a = b.
  induction n with d hd
  -- Assume that the hypothesis 'h' is true, that is, a + 0 = b + 0. The goal now is to prove that a = b.
  intro h
  -- Repeatedly apply the rewrite rule add_zero to the hypothesis h, which simplifies any terms of the form x + 0 in h to x. In this case we get a = b
  repeat rw [add_zero] at h
  -- Apply the hypothesis 'h' to the goal which is a = b, hence this concludes the base case.
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
  -- induct on n
  induction n with d hd
  -- assume a + 0 = b + 0
  intro h
  -- a = b at hypothesis
  repeat rw [add_zero] at h
  -- a = b, as desired
  exact h
  -- assume a + succ d = b + succ d
  intro h
  -- succ(a + d) = b + succ d at hypothesis
  rw [add_succ] at h
  -- succ(a + d) = succ(b + d) at hypothesis
  rw [add_succ] at h
  -- a + d = b + d at hypothesis
  apply succ_inj at h
  -- a = b by inductive hypothesis
  apply hd at h
  -- a = b from the inductive hypothesis
  exact h

  -- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_right_cancel_dev_2 (a b n : ℕ) : a + n = b + n → a = b := by
  -- We start with induction on n.
  induction n with d hd
  -- For the base case, to show that a + 0 = b + 0 → a = b, we first assume a + 0 = b + 0.
  intro h
  -- we simplify the LHS in the hypothesis using the theorem that n + 0 = 0
  rw [add_zero] at h
  -- we simplify the RHS in the hypothesis using the theorem that n + 0 = 0
  rw [add_zero] at h
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
  -- a + n = n + b implies a = b
  rw [add_comm]
  -- initiate induction on n
  induction n with d hd
  -- assume a + 0 = 0 + b
  intro h
  -- a + 0 = b in the hypothesis
  rw [zero_add] at h
  -- a = b in the hypthesis
  rw [add_zero] at h
  -- a = b as desired
  exact h
  -- assume a + succ d = succ d + b
  intro h
  --  a + succ d = succ (d + b) in the hypothesis
  rw [succ_add] at h
  -- succ (a + d) = succ (d + b) in the hypothesis
  rw [add_succ] at h
  -- a + d = d + b in the hypothesis
  apply succ_inj at h
  -- a = b by using the inductive hypotheis
  apply hd at h
  -- a = b as desired
  exact h


-- Proof Statement: Prove that a + n = b + n implies a = b for all natural numbers
theorem add_left_cancel_dev_2 (a b n : ℕ) : n + a = n + b → a = b := by
  -- We start with induction on n.
  induction n with d hd
  -- For the base case, we assume the hypothesis 0 + a = 0 + b.
  intro h
  -- Using the theorem 0 + d = d we obtain a = b
  repeat rw [zero_add] at h
  -- applying the hypothesis we conclude the base case
  exact h
  -- For the inductive case, we assume the hypothesis succ d + a = succ d + b
  intro h
  -- Using the theorem succ a + b = succ (a + b) we obtain succ (d + a) = succ (d + b) as the hypothesis
  repeat rw [succ_add] at h
  -- By the injectivity of succ we obtain d + a = d + b in the hypothesis
  apply succ_inj at h
  -- using the induction hypothesis in the current hypothesis we obtain a = b
  apply hd at h
  -- applying the hypothesis we conclude
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
  -- intitiate induction on y
  induction y with d hd
  -- assume x + 0 = 0
  intro h
  -- x = 0 in our assumption
  rw [add_zero] at h
  -- we have x = 0 as desired
  exact h
  -- assume x + succ d = succ d
  intro h
  -- succ (x + d) = succ d in our assumption
  rw [add_succ] at h
  -- x + d = d by injectivity in our assumption
  apply succ_inj at h
  -- x = 0 by induction hypothesis
  apply hd at h
  -- we have x = 0 as desired
  exact h


-- Proof Statement: Prove that x + y = y implies x = 0 for all natural numbers
theorem add_left_eq_self_dev_2 (x y : ℕ) : x + y = y → x = 0 := by
  -- To show x + y = y → x = 0, we begin by assuming x + y = y.
  intro h
  -- We use the fact that 0 + n = n to change x + y = y into x + y = 0 + y.
  nth_rewrite 2 [← zero_add y] at h
  -- We use the theorem that a + n = b + n implies a = b on the fact x + y = 0 + y.
  apply add_right_cancel at h
  -- So, x = 0, as desired.
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
  -- initiate induction on x
  induction x with d hd
  -- assume 0 + y = 0
  intro h
  -- y = 0 from our assumptiom
  rw [zero_add] at h
  -- y = 0 as desired
  exact h
  -- assume y + succ d = succ d
  intro h
  -- succ (y + d) = succ d from our assumption
  rw [succ_add] at h
  -- y + d = d from our assumption
  apply succ_inj at h
  -- y = 0 using the induction hypothesis
  apply hd at h
  -- y = 0 as desired
  exact h


-- Proof Statement: Prove that x + y = x implies y = 0 for all natural numbers
theorem add_right_eq_self_dev_2 (x y : ℕ) : x + y = x → y = 0 := by
  -- To show x + y = x → y = 0, we start by assuming x + y = x.
  intro h
  -- By the commutativity of addition, we know that y + x = x.
  rw [add_comm] at h
  -- We apply the theorem that a + b = b implies that a = 0.
  apply add_left_eq_self at h
  -- So, y = 0, as desired.
  exact h


-- Proof Statement: Prove that a + b = 0 implies a = 0 for all natural numbers
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
  tauto


-- Proof Statement: Prove that a + b = 0 implies a = 0 for all natural numbers
theorem add_right_eq_zero_dev_1 (a b : ℕ) : a + b = 0 → a = 0 := by
  -- Proof by induction on b
  induction a with d hd
  -- 0 = 0 is trivially true
  tauto
  -- assume that succ d + b = 0
  intro h
  -- succ (d + b) = 0
  rw [succ_add] at h
  -- 0 = succ (a + d)
  symm at h
  -- 0 = succ (a + d) is impossible as its false
  apply zero_ne_succ at h
  -- This is vacuously true
  tauto


-- Proof Statement: Prove that a + b = 0 implies a = 0 for all natural numbers
theorem add_right_eq_zero_dev_2 (a b : ℕ) : a + b = 0 → a = 0 := by
  -- use the theorem that a + b = b + a to obtain b + a = 0 implies a = 0
  rw [add_comm]
  -- initiate induction on b
  induction b with d hd
  -- Assume the hypothesis 0 + a = 0 for the base case
  intro h
  -- use the theorem that 0 + n = 0 to obtain a = 0
  rw [zero_add] at h
  -- a = 0 is what was desired
  exact h
  -- Assume hypothesis succ d + a = 0
  intro h
  -- use the theorem that succ a + b = succ (a + d) to obtain succ (d + a) = 0
  rw [succ_add] at h
  -- Use the fact that a = b implies b = a to obtain 0 = succ (d + a)
  symm at h
  -- Apply the theorem that states that the successor of any natural number cannot equal 0 to our hypothesis h which shows that h is false.
  apply zero_ne_succ at h
  -- Since h is a proof of False, and there are no ways to construct False so we have our contradiction and can close the proof
  tauto

-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  -- Rewrite the goal by swapping the addition operands in the left side of both equations, changing a + b = 0 to b + a = 0.
  rw [add_comm]
  -- Apply the theorem that states that if a + b = 0, then b = 0 for all natural numbers.
  exact add_right_eq_zero b a


-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_1 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- initiate induction on b
  induction b with d hd
  -- 0 = 0 is obviously true
  tauto
  -- assume a + succ d = 0
  intro h
  -- succ (a + d) = 0 from assumption
  rw [add_succ] at h
  -- 0 = succ (a + d) from assumption
  symm at h
  -- 0 = succ (a + d) is impossible and is false
  apply zero_ne_succ at h
  -- This is vacuously true
  tauto


-- Proof Statement: Prove that a + b = 0 implies b = 0 for all natural numbers
theorem add_left_eq_zero_dev_2 (a b : ℕ) : a + b = 0 → b = 0 := by
  -- initiate induction on a
  induction a with d hd
  -- assume that 0 + b = 0
  intro h
  -- use the fact that 0 + n = n to obtain b = 0
  rw [zero_add] at h
  -- we have b = 0 as desired
  exact h
  -- assume that succ n + b = 0
  intro h
  -- we use that fact that succ a + b = succ (a + b) hence obtaining succ (n + b) = 0
  rw [succ_add] at h
  -- apply the fact that a = b implies b = a to obtain  0 = succ (n + b)
  symm at h
  -- Apply the theorem that states that the successor of any natural number cannot equal 0 to our hypothesis h which shows that h is false.
  apply zero_ne_succ at h
  -- -- Since h is a proof of False, and there are no ways to construct False so we have our contradiction and can close the proof
  tauto

end MyNat
