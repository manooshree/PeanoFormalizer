import openai
import json

# Set your OpenAI API key
openai.api_key = ""

NL_prompt = '''
These are two commented examples of Lean code:
theorem zero_add (n : ℕ) : 0 + n = n := by
-- Proof Statement: Prove that 0 + n = n for all natural numbers
  induction n with d hd
  -- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d).
  · rw [add_zero]
    -- First prove base case. Reduce LHS 0 + 0 = 0.
    rfl
    -- Prove LHS and RHS are equal, 0 = 0, completing base case.
  · rw [add_succ]
    -- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d).
    rw [hd]
    -- Simplify RHS succ (0 + d) = succ(d) using the inductive hypothesis.
    rfl
    -- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof.

-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with d hd
  -- Induct on b, with d = 0 as the base case and the inductive hypothesis succ (a) + d = succ (a + d). There are now two proof goals, prove base case: succ (a) + 0 = succ (a + 0) and inductive step: succ (a) + succ (d) = succ (a + succ (d)).
  · rw [add_zero]
    -- First prove base case. Reduce LHS succ (a) + 0 = succ (a).
    rw [add_zero]
    -- Reduce RHS succ(a + 0) = succ (a).
    rfl
    -- Prove succ (a) = succ (a), finishing the base case.
  · rw [add_succ]
    -- Now prove the inductive step. Rewrite succ (a) + succ (d) = succ (succ a + d).
    rw [add_succ]
    -- Rewrite succ (a + succ d) = succ (succ (a + d)).
    rw [hd]
    -- Rewrite RHS succ (succ a + d) to succ (succ (a + d)) using the inductive hypothesis.
    rfl
    -- Prove succ (succ (a + d)) = succ (succ (a + d)), completing the proof.

Can you create such an in-line comment for the following line of lean code? This is the current goal-state for reference: ⊢ a + b + c = a + (b + c)

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by

Output the in-line comment as a valid JSON object.
IMPORTANT: Respond with ONLY a raw JSON object in the following format, without any code block formatting or additional text:
{
"Inline Comment": "Comment"
}
'''
def chat_with_gpt(prompt):
    try:
        response = openai.ChatCompletion.create(
            model="gpt-4o",
            messages=[
                {"role": "system", "content": "You are a Lean4 expert translating Lean proofs to natural language."},
                {"role": "user", "content": prompt},
            ],
            temperature=0.5,
        )
        return response['choices'][0]['message']['content']
    except Exception as e:
        return f"An error occurred: {e}"

if __name__ == "__main__":
    reply = chat_with_gpt(NL_prompt)
    reply_json = json.loads(reply)
    print(reply_json.get("Inline Comment"))
