import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean

namespace MyNat

-- Theorem Declaration: Prove that 0 + n = n for all natural numbers
theorem zero_add__dev_1 (n : ℕ) : 0 + n = n := by
  -- Induct on n
  induction n with d hd
  -- substitute 0 -> 0 + 0 into the RHS giving us 0 + 0 = 0 + 0
  nth_rewrite 3 [← add_zero 0]
  -- 0 + 0 = 0 + 0, completing base case
  rfl
  -- 0 + d -> d on LHS -> succ d = succ d
  rw [hd]
  -- succ d = succ d, QED
  rfl

-- Theorem Declaration: Prove that 0 + n = n for all natural numbers
theorem zero_add__dev_2 (n : ℕ) : 0 + n = n := by
  -- Begin by initiating induction on n
  induction n with d hd
  -- Using the properties of addition by 0 we can rewrite 0 + 0 to 0 on the LHS
  rw [add_zero]
  -- Since both sides are equal, we are done with the base case
  rfl
  -- Using the induction hypothesis we can rewrite succ (0 + d) to succ d
  rw [hd]
  -- Since both sides are equal, we are done with the proof
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add__dev_1 (a b : ℕ) : succ a + b = succ (a + b) := by
  -- Initiate induction on b
  induction b with n hn
  -- succ(a) + 0 -> succ(a) on LHS giving us succ(a) = succ(a+0)
  rw [add_zero]
  -- a + 0 -> a on RHS giving us succ(a) = succ(a)
  rw [add_zero]
  -- succ(a) = succ(a), Hence we are done with the base case
  rfl
  -- Now for the induction case. succ(a) + succ(n) -> succ(succ(a) + n) on LHS giving us succ(succ(a) + n) = succ(a + succ(n))
  rw [add_succ]
  -- a + succ(n) -> succ(a + n) on RHS giving us succ(succ(a) + n) = succ(succ(a + n))
  rw [add_succ]
  -- succ(succ(a) + n) = succ(succ(a) + n), QED
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add__dev_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
  -- Initiate induction on b.
  induction b with n hn
  -- We start by proving the base case using properties of succession, succ(a+0) = a + succ(0) on RHS
  rw [← add_succ]
  -- Now using properties of addition by 0, we can rewrite succ(a) + 0 to succ(a) on the LHS
  rw [add_zero]
  -- Now using properties of succession, we can rewrite succ(a) + 0 to succ(a+0) on the RHS
  rw [add_succ]
  -- Now using properties of addition by 0, we can rewrite a + 0 to a on the RHS
  rw [add_zero]
  -- since succ(a) = succ(a), we are done with the base case
  rfl
  -- Now to prove the induction case, we use properties of succession substituting succ(a) + succ(n) = succ(succ(a) + n) on LHS
  rw [add_succ]
  -- Now again using properties of succession, we substitute succ(a + succ(n)) to succ(succ(a + n)) on the RHS
  rw [add_succ]
  -- both sides are equal, hence we are done
  rfl

-- Theorem Declaration: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm__dev_1 (a b : ℕ) : a + b = b + a := by
  -- Start by inducting on b
  induction b with d hd
  -- 0 + a -> a on RHS giving us a + 0 = a
  rw [zero_add]
  --  a + 0 -> a into the LHS to get a = a
  rw [add_zero]
  -- a=a, we are done with the base case
  rfl
  -- a + succ d -> succ (a + d) on LHS giving us succ (a + d) = succ (d + a) on LHS
  rw [add_succ]
  -- succ d + a -> succ (d + a) on RHS giving us succ (a + d) = succ (d + a) on RHS
  rw [succ_add]
  -- succ (n + a) = succ (n + a), we are done.
  rfl

-- Theorem Declaration: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm__dev_2 (a b : ℕ) : a + b = b + a := by
  -- Start by inducting on b
  induction b with d hd
  -- We start with the base case. using properties of addition by 0 we can rewrite a + 0 to a on the LHS
  rw [add_zero]
  -- using properties of addition by 0 we can rewrite 0 + a to a on the RHS
  rw [zero_add]
  -- since both sides are equal, we are done with the base case
  rfl
  -- Now to the (n+1) step. using properties of successors, succ (n) + a -> succ (n + a) and substitute this into the RHS
  rw [succ_add]
  -- using properties of succession, we substitute a + succ(n) -> succ(a+n) on the RHS
  rw [add_succ]
  -- since both sides are equal, we are done with the proof
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc__dev_1 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- intiate induction on b
  induction b with d hd
  -- We rewrite on the RHS 0 + c -> c to get a + 0 + c = a + c
  rw [zero_add]
  -- We rewrite on the LHS a + 0 -> a to get a + c = a + c
  rw [add_zero]
  -- a + c = a + c, completing the base case.
  rfl
  -- Now prove the inductive step.  a + succ d -> succ (a + d) giving us succ (a + d) + c = a + (succ d + c)
  rw [add_succ]
  -- Now on the LHS we write succ(a + d) + c -> succ(a + d + c). This gives us succ (a + d + c) = a + succ (d + c)
  rw [succ_add]
  -- Now we use the inductive hypothesis on LHS (a + d + c) -> a + (d + c) to get succ(a + (d + c)) = a + succ (d + c)
  rw [hd]
  -- Rewrite on RHS, a + succ (d + c) -> succ (a + (d + c)) to get succ (a + (d + c)) = succ (a + (d + c))
  rw [add_succ]
  -- succ (a + (d + c)) = succ (a + (d + c)), QED
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc__dev_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on b
  induction b with d hd
  -- First prove base case. we use properties of addition by 0 to rewrite 0 + c to c on the RHS
  rw [zero_add]
  -- using properties of addition by 0 we can rewrite a + 0 to a on the LHS
  rw [add_zero]
  -- both sides are equal, hence we are done with the base case
  rfl
  -- Now for the inductive case. we use properties of succession to rewrite (succ n + c) to succ (n + c) on the RHS
  rw [succ_add]
  -- Now using properties of succession we rewrite a + succ n to succ (a + n) on the LHS
  rw [add_succ]
  -- Again using properties of succession we rewrite a + succ(n + c) to succ(a + (n + c)) on the RHS
  rw [add_succ]
  -- Using the induction hypothesis we rewrite succ(a + n + c) to succ(a + (n + c)) on the LHS
  rw [hd]
  -- both sides are equal, hence we are done with the proof
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm__dev_1 (a b c : ℕ) : a + b + c = a + c + b := by
  -- a + b + c -> a + (b + c) on the LHS giving us a + (b + c) = a + c + b
  rw [add_assoc]
  -- b + c -> c + b on the LHS giving us a + (c + b) = a + (c + b)
  rw [add_comm b c]
  -- a + (c + b) = a + (c + b), QED
  rfl

-- Theorem Declaration: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm__dev_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Write the RHS using the associative property: a + c + b to a + (c + b).
  rw [add_assoc]
  -- since both sides are equal, we are done with the proof
  rfl

end MyNat
