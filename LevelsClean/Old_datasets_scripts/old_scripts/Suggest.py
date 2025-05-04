import sys
import re
import openai
import json



def gpt_prompt(tactic, before_state="No before state provided", after_state="No after state provided"):
    openai.api_key = ""


    NL_prompt = f'''
    These are three commented examples of Lean code:

    -- Proof Statement: Prove 2 * y = 2 * (x + 7) for natural numbers x, y, given that y = x + 7
theorem rw_intro (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- Rewrite 2 * y in the LHS of the proof goal as 2 * (x + 7) using the fact that y = x + 7
  rw [h]
  -- Prove LHS and RHS are equal, 2 * (x + 7) = 2 * (x + 7), completing the proof
  rfl
  
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
    -- Proof Statement: Prove that given some x, y, z which are natural numbers, x + y = 37. We can assume that x + y = 37 and 3 * x + z = 42
    theorem exact (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
    -- We can prove x + y = 37, using our given statement, which says exactly that x + y = 37, and complete the proof
    exact h1

-- Proof Statement: For some x which is a natural number, given that  0 + x = 0 + y + 2, prove x = y + 2
    theorem exact_2 (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
    -- Rewrite 0 + x in the LHS of the hypothesis to x
    rw [zero_add] at h
    -- Rewrite 0 + y to y in the RHS of the hypothesis
    rw [zero_add] at h
    -- Our simplified hypothesis is now x = y + 2, we can use this exactly to complete the proof
    exact h

    You need to write an in-line comment which is a natural language version of a Lean tactic.

    This is the goal state before the tactic was applied: {before_state}
    The tactic {tactic} was applied and the goal state changed to: {after_state}
    ''' + '''IMPORTANT: Respond with ONLY a raw JSON object in the following format, without any code block formatting or additional text:
    {
    "Inline Comment": "Comment"
    }
    '''


    try:
        response = openai.ChatCompletion.create(
            model="gpt-4",
            messages=[
                {"role": "system", "content": "You are a Lean4 expert translating Lean proofs to natural language."},
                {"role": "user", "content": NL_prompt},
            ],
            temperature=0.5,
        )
        reply = response['choices'][0]['message']['content']
        if reply.startswith('```'):
            start = reply.find('{')
            end = reply.rfind('}') + 1
            if start != -1 and end != 0:
                reply = reply[start:end]
        reply_json = json.loads(reply)
        return reply_json.get("Inline Comment")
    except Exception as e:
        return f"An error occurred: {e}"



# if __name__ == "__main__":
#     if len(sys.argv) > 1:
#         input_data = sys.argv[1]
#         goal_match = re.search(r"⊢ .*", input_data)
#         tactic_match = re.search(r"Tactic: (.*)", input_data)  # Match the tactic line

#         goal = goal_match.group(0) if goal_match else "No goal found"
#         tactic = tactic_match.group(1) if tactic_match else "No tactic provided"
#         print(f"\nGoal:\n{goal}")
#         print(f"Tactic:\n{tactic}")
#         natural_language = gpt_prompt(str(goal), str(tactic))
#         print(f"NL Translation: \n{natural_language}")


#     else:
#         print("No input received from Lean!")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        input_data = sys.argv[1]

        before_goal_match = re.search(r"Before:\n(.*?⊢.*)", input_data, re.DOTALL)
        before_goal = before_goal_match.group(1).strip() if before_goal_match else "No before goal found"

        after_goal_match = re.search(r"After:\n(.*?⊢.*)", input_data, re.DOTALL)
        after_goal = after_goal_match.group(1).strip() if after_goal_match else "No after goal found"

        tactic_match = re.search(r"Tactic:\s*(.*)", input_data)
        tactic = tactic_match.group(1).strip() if tactic_match else "No tactic provided"

        # print(f"Goal Before Tactic:\n⊢ {before_goal}\n")
        # print(f"User-Provided Tactic:\n{tactic}\n")
        # print(f"Goal After Tactic:\n⊢ {after_goal}\n")
        natural_language = gpt_prompt(str(tactic), str(before_goal), str(after_goal))
        print(f"NL Translation: \n{natural_language}")


    else:
        print("No input received from Lean!")