import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean
-- import Game_Levels_Tut

namespace MyNat



-- theorem zero_add (n : ℕ) : 0 + n = n := by
--   induction n with d hd
--   · rw [add_zero]
--     rfl
--   · rw [add_succ]
--     rw [hd]
--     rfl



--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add (n : ℕ) : 0 + n = n := by
-- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd
-- First prove base case. Reduce LHS 0 + 0 = 0.
  rw [add_zero]
-- Prove LHS and RHS are equal, 0 = 0, completing base case
  rfl
-- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d)
  rw [add_succ]
-- Simplify RHS succ (0 + d) = succ(d) using the inductive hypothesis.
  rw [hd]
-- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
  rfl

--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add_persona_1_d (n : ℕ) : 0 + n = n := by
-- Induct on n
  induction n with d hd
-- substitute 0 -> 0 + 0 into the RHS giving us 0 + 0 = 0 + 0
  nth_rewrite 3 [← add_zero 0]
-- 0 + 0 = 0 + 0, completing base case
  rfl
-- 0 + succ d -> succ (0 + d) on LHS giving us succ (0 + d) = succ d
  rw [add_succ]
-- 0 + d -> d on LHS -> succ d = succ d
  rw [hd]
-- succ d = succ d, QED
  rfl

--Proof Statement: Prove that 0 + n = n for all natural numbers
theorem zero_add_persona_2 (n : ℕ) : 0 + n = n := by
-- Begin by initiating induction on n
  induction n with d hd
-- Using the properties of addition by 0 we can rewrite 0 + 0 to 0 on the LHS
  rw [add_zero]
-- Since both sides are equal, we are done with the base case
  rfl
-- Now using properties of successors we can rewrite 0 + succ d to succ (0 + d) on the LHS getting succ (0 + d) = succ d
  rw [add_succ]
-- Using the induction hypothesis we can rewrite succ (0 + d) to succ d
  rw [hd]
-- Since both sides are equal, we are done with the proof
  rfl




-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
  rw [add_zero]
-- Prove succ (a) = succ (a), finishing the base case
  rfl
-- Now prove the inductive step. Rewrite succ (a) + succ (d) = succ (succ a + d)
  rw [add_succ]
-- Rewrite succ (a + succ d) = succ (succ (a + d))
  rw [add_succ]
-- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
  rw [hd]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add_persona_1_d (a b : ℕ) : succ a + b = succ (a + b) := by
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
-- using induction hypothesis, succ(a + n) -> succ(a) + n on RHS. Hence we get succ(succ(a) + n) = succ(succ(a) + n)
rw [← hn]
-- succ(succ(a) + n) = succ(succ(a) + n), QED
rfl


-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add_persona_2_d (a b : ℕ) : succ a + b = succ (a + b)  := by
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
-- Using the induction hypothesis giving us succ(succ(a) + n) = succ(succ(a) + n) on the LHS
 rw [← hn]
-- both sides are equal, hence we are done
 rfl


-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add_2 (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d))
  induction b with d hd
-- First prove base case. Reduce LHS succ (a) + 0 = succ (a)
  rw [add_zero]
-- Reduce RHS succ(a + 0) = succ (a)
  rw [add_zero]
-- Prove succ (a) = succ (a), finishing the base case
  rfl
-- Now prove the inductive step. Rewrite the LHS succ (a) + succ (d) = succ (succ (a + d)) and the RHS succ (a + succ d) = succ (succ (a + d)). Then rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis
  rw [add_succ, add_succ, hd]
-- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add_logically_eq (a b : ℕ) : succ a + b = succ (a + b)  := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
  induction b with n hn
-- We start by proving the base case using the fact that c + 0 = c ∀ c ∈ ℕ and setting c := a giving us succ(a) + 0 = succ(a)
  rw [add_zero]
-- Now we can set c = succ(a) and use c + 0 = c ∀ c ∈ ℕ again to get succ(a) = succ(a)
  rw [add_zero]
-- Since we have succ(a) = succ(a) we are done with the base case
  rfl
-- Now to prove the induction case, we use the fact that a + succ(b) = succ(a + b) ∀ a, b ∈ ℕ and set a := succ(a) and b := n giving us succ(succ(a) + n) = succ(a+succ(n))
  rw [add_succ]
-- We again use the fact that a + succ(b) = succ(a + b) ∀ a, b ∈ ℕ on the right hand side and set a := a and b := n giving us succ(succ(a) + n) = succ(succ(a+n))
  rw [add_succ]
-- Rewrite the left hand side using the hypothesis giving us succ(succ(a+n)) = succ(succ(a+n))
  rw [hn]
-- Hence we are done.
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, that is a + b + c = a + (b + c).
theorem succ_add_logical_deviation_1 (a b : ℕ) : succ a + b = succ (a + b) := by
-- Initiate induction on b, the base case (b=0) succ(a) + 0 = succ(a + 0)
induction b with n hn
-- We start by proving the base case using the fact that c + 0 = c ∀ c ∈ ℕ and setting c := a giving us succ(a) + 0 = succ(a)
rw [add_zero]
-- Now we can set c = succ(a) and use c + 0 = c ∀ c ∈ ℕ again to get succ(a) = succ(a)
rw [add_zero]
-- Since we have succ(a) = succ(a) we are done with the base case
rfl
-- Now to prove the induction case, we use the fact that a + succ(b) = succ(a + b) ∀ a, b ∈ ℕ and set a := succ(a) and b := n giving us succ(succ(a) + n) = succ(a+succ(n))
rw [add_succ]
-- We again use the fact that a + succ(b) = succ(a + b) ∀ a, b ∈ ℕ on the right hand side and set a := a and b := n giving us succ(succ(a) + n) = succ(succ(a+n))
rw [add_succ]
-- Rewrite the right hand side using the hypothesis giving us succ(succ(a) + n) = succ(succ(a) + n)
rw [← hn]
-- Hence we are done.
rfl


-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a.
  rw [add_zero]
-- Simplify RHS 0 + a = a
  rw [zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
  rfl
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d)
  rw [add_succ]
-- Rewrite RHS succ (d) + a = succ (d + a)
  rw [succ_add]
-- Rewrite LHS succ (a + d) to succ (d + a) using the inductive hypothesis
  rw [hd]
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_persona_1_d (a b : ℕ) : a + b = b + a := by
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
-- using the induction hypothesis, succ (a + d) -> succ (d + a) on the LHS giving us succ (d + a) = succ (d + a)
  rw [hd]
-- succ (n + a) = succ (n + a), we are done.
  rfl


-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_persona_2_d (a b : ℕ) : a + b = b + a := by
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
-- Use the induction hypothesis on the LHS to substitute succ (a + n) -> succ (n + a)
  rw [hd]
-- since both sides are equal, we are done with the proof
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_logical_persona_3_d_1 (a b : ℕ) : a + b = b + a := by
-- Start by inducting on b
  induction b with d hd
-- We start with the base case by substitute 0 + a = a into the RHS to get a + 0 = a
  rw [zero_add]
-- Then we substitute a + 0 = a into the LHS to get a = 0 + a
  rw [add_zero]
-- Since a = a, we are done with the base case.
  rfl
-- Now to prove the (n+1) step. We know that succ(a) + b = succ(a+b) set a := n and b := a to get succ (n) + a = succ (n + a) and substitute this into the RHS
  rw [succ_add]
-- We know that a + succ (b) = succ (a + b), we substitute b := n, and then take this expression and substitute it into the LHS to get succ(a + n) = succ(n + a)
  rw [add_succ]
-- Use the induction hypothesis on the LHS to rewrite succ (a + n) = succ (n + a)
  rw [hd]
-- Now that we have succ (n + a) = succ (n + a), we are done.
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_logical_persona_3_d_2 (a b : ℕ) : a + b = b + a := by
-- Start by inducting on b
  induction b with d hd
-- We start with the base case by substitute 0 + a = a into the RHS to get a + 0 = a
  rw [zero_add]
-- Then we substitute a + 0 = a into the LHS to get a = 0 + a
  rw [add_zero]
-- Since a = a, we are done with the base case.
  rfl
-- Now to prove the (n+1) step. We know that a + succ (b) = succ (a + b), we substitute b := n, and then take this expression and substitute it into the LHS to get succ(a + n) = succ(n) + a
  rw [add_succ]
-- We know that succ(a) + b = succ(a+b) set a := n and b := a to get succ (n) + a = succ (n + a) and substitute this into the RHS
  rw [succ_add]
-- Use the induction hypothesis on the LHS to rewrite succ (a + n) = succ (n + a)
  rw [hd]
-- Now that we have succ (n + a) = succ (n + a), we are done.
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_logical_persona_3_d_3 (a b : ℕ) : a + b = b + a := by
-- Start by inducting on b
  induction b with d hd
-- We start with the base case. We substitute a + 0 = a into the LHS to get a = 0 + a
  rw [add_zero]
-- now we substitute 0 + a = a into the RHS to get a = a
  rw [zero_add]
-- Since a = a, we are done with the base case.
  rfl
-- Now to prove the (n+1) step. We know that succ(a) + b = succ(a+b) set a := n and b := a to get succ (n) + a = succ (n + a) and substitute this into the RHS
  rw [succ_add]
-- We know that a + succ (b) = succ (a + b), we substitute b := n, and then take this expression and substitute it into the LHS to get succ(a + n) = succ(n + a)
  rw [add_succ]
-- Use the induction hypothesis on the LHS to rewrite succ (a + n) = succ (n + a)
  rw [hd]
-- Now that we have succ (n + a) = succ (n + a), we are done.
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_2 (a b : ℕ) : a + b = b + a := by
-- Induct on b, with d = 0 as the base case and the inductive hypothesis a + d = d + a. There are now two proof goals, prove base case: a + 0 = 0 + a and the inductive step: a + succ d = succ d + a
  induction b with d hd
-- First prove base case. Simplify LHS a + 0 = a and RHS 0 + a = a.
  rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, a = a, completing the base case.
  rfl
-- Now prove the inductive step. Rewrite LHS a + succ (d) = succ (a + d) and RHS succ (d) + a = succ (d + a). Then, use the inductive hypothesis to rewrite succ (a + d) = succ (d + a)
  rw [add_succ, succ_add, hd]
-- Prove succ LHS and RHS are equal, (d + a) = succ (d + a), completing the proof
  rfl

-- Proof Statement: Prove that addition is commutative, that is a + b  = b + a for all natural numbers
theorem add_comm_3 (a b : ℕ) : a + b = b + a := by
-- Induct on a, with d = 0 as the base case and the inductive hypothesis d + b = b + d. There are now two proof goals, prove base case: 0 + b = b + 0 and the inductive step: succ d + b = b + succ d
  induction a with d hd
-- First prove base case. Simplify RHS b + 0 = b and LHS 0 + b = b
  rw [add_zero, zero_add]
-- Prove LHS and RHS are equal, b = b, completing the base case.
  rfl
-- Now prove the inductive step. Rewrite RHS b + succ d = succ (b + d) and LHS succ (d) + b = succ (d + b). Then, use the inductive hypothesis to rewrite succ (d + b) = succ (b + d)
  rw [add_succ, succ_add, hd]
-- Prove LHS and RHS are equal, succ (b + d) = succ (b + d), completing the proof
  rfl


-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d))
  induction c with d hd
  -- First prove base case. Simplify LHS a + b + 0 = a + b
  rw [add_zero]
    -- Reduce RHS a + (b + 0) to a + b
  rw [add_zero]
    -- Prove LHS and RHS are equal, a + b = a + b, completing the base case.
  rfl
  -- Now prove the inductive step. Rewrite the LHS expression a + b + succ d to succ (a + b + d)
  rw [add_succ]
  -- Rewrite RHS a + (b + succ d) to a + succ (b + d)
  rw [add_succ]
  -- Use the inductive hypothesis to rewrite the left-hand side, changing succ (a + b + d) to succ (a + (b + d))
  rw [hd]
--  Rewrite the RHS, a + succ (b + d) to succ (a + (b + d))
  rw [add_succ]
-- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc_persona_1_d (a b c : ℕ) : a + b + c = a + (b + c) := by
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
--  Rewrite the RHS, succ (d) + c -> succ(d + c), to get succ (a + (d + c)) = a + succ (d + c)
  rw [succ_add]
-- Rewrite on RHS, a + succ (d + c) -> succ (a + (d + c)) to get succ (a + (d + c)) = succ (a + (d + c))
  rw [add_succ]
-- succ (a + (d + c)) = succ (a + (d + c)), QED
  rfl

-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc_persona_2_d (a b c : ℕ) : a + b + c = a + (b + c) := by
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
  --  Again using properties of succession we rewrite succ (a + n) + c to succ (a + n + c) on the LHS
  rw [succ_add]
  -- Again using properties of succession we rewrite a + succ(n + c) to succ(a + (n + c)) on the RHS
  rw [add_succ]
  -- Using the induction hypothesis we rewrite succ(a + n + c) to succ(a + (n + c)) on the LHS
  rw [hd]
  -- both sides are equal, hence we are done with the proof
  rfl


-- Proof Statement: Prove that the addition of natural numbers is associative, i.e., a + b + c = a + (b + c).
theorem add_assoc_2 (a b c : ℕ) : a + b + c = a + (b + c) := by
  -- Induct on c, with d = 0 as the base case and the inductive hypothesis a + b + d = a + (b + d). There are now two proof goals, prove base case: a + b + 0 = a + (b + 0), and inductive step: a + b + succ (d) = a + (b + succ (d)).
  induction c with d hd
  -- First we prove the base case. Simplify the LHS and RHS both to a + b
  · rw [add_zero, add_zero]
  -- Prove LHS and RHS are equal, a + b = a + b, completing the base case.
    rfl
  -- Now prove the inductive step. Rewrite the LHS: a + b + succ (d) to succ (a + b + d) and then to succ (a + (b + d)), using the inductive hypothesis. Change the RHS: a + (b + succ d) to a + succ (b + d) to succ (a + (b + d))
  · rw [add_succ, add_succ, hd, add_succ]
  -- Prove LHS and RHS are equal, succ (a + (b + d)) = succ (a + (b + d)), completing the proof
    rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS of the equation, changing a + b + c to a + (b + c)
  rw [add_assoc]
  -- Rewrite the LHS of the equation by applying the commutative property of addition to b and c, LHS is now a + (c + b)
  rw [add_comm b c]
  -- Rewrite the RHS using the associative property: a + c + b to a + (c + b).
  rw [add_assoc]
  -- Prove LHS and RHS are equal, a + (c + b) = a + (c + b), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm_persona_1_d (a b c : ℕ) : a + b + c = a + c + b := by
  -- a + b + c -> a + (b + c) on the LHS giving us a + (b + c) = a + c + b
  rw [add_assoc]
  -- a + c + b -> a + (c + b) on the RHS giving us a + (b + c) = a + (c + b)
  rw [add_assoc]
  -- b + c -> c + b on the LHS giving us a + (c + b) = a + (c + b)
  rw [add_comm b c]
  -- a + (c + b) = a + (c + b), QED
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm_persona_2_d (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Write the RHS using the associative property: a + c + b to a + (c + b).
  rw [add_assoc]
  -- use the commutative property of addition to rewrite c + b to b + c on the RHS, a + (b + c) = a + (b + c)
  rw [add_comm c b]
  -- since both sides are equal, we are done with the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm_persona_2_d_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Rewrite the LHS using the commutative property of addition for b and c: a + (b + c) to a + (c + b).
  rw [add_comm b]
  -- Rewrite the RHS using the associative property of addition: a + c + b to a + (c + b).
  rw [add_assoc]
  -- Prove LHS and RHS are equal, a + (c + b) = a + (c + b), completing the proof
  rfl

-- Proof Statement: Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b
theorem add_right_comm_2 (a b c : ℕ) : a + b + c = a + c + b := by
  -- Apply the associative property of addition to rewrite the LHS: a + b + c to a + (b + c).
  rw [add_assoc]
  -- Rewrite the LHS using the commutative property of addition for b and c: a + (b + c) to a + (c + b).
  rw [add_comm b c]
  -- Rewrite the RHS using the associative property of addition: a + c + b to a + (c + b).
  rw [add_assoc]
  -- Prove LHS and RHS are equal, completing the proof.
  rfl
