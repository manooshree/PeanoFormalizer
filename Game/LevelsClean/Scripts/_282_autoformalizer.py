import os
import torch 
from transformers import AutoModelForCausalLM, AutoTokenizer

# set to available gpu
os.environ["CUDA_VISIBLE_DEVICES"] = "1"
# insert your hf token
os.environ["HF_TOKEN"] = ""


# base model is SFT 
# model_name = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"

# tokenizer = AutoTokenizer.from_pretrained(model_name)
# model = AutoModelForCausalLM.from_pretrained(
#     model_name, 
#     torch_dtype = torch.float16, 
#     device_map = "auto", 
#     token=os.environ["HF_TOKEN"]
# )

# finetuned checkpoint path
checkpoint_path = "deepseek-prover-lora-3/checkpoint-1784" 
tokenizer = AutoTokenizer.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-SFT", token=os.environ["HF_TOKEN"])
model = AutoModelForCausalLM.from_pretrained(
    checkpoint_path,
    torch_dtype=torch.float16,
    device_map="auto",
    token=os.environ["HF_TOKEN"]
)


# tactics = "Available tactics: rw, induction, rfl, have, cases h with"
tactics = "Available tactics: rw, induction, rfl, cases, intro, decide, exact, apply, symm, use, left, right, contrapose, have, tauto, trivial"
theorems = "Available theorems = Available theorems: add_succ, add_zero, succ_add, add_assoc, add_comm, add_comm_right, zero_add, add_right_cancel, add_left_cancel, add_left_eq_self, add_right_eq_self, zero_ne_succ, add_right_eq_zero, add_left_eq_zero, mul_le_mul_right, mul_left_ne_zero, eq_succ_of_ne_zero, one_le_of_ne_zero, succ_inj, ne, zero_ne_one, le_refl, zero_le, le_succ_self, le_trans, le_zero, le_antisymm, le_total, succ_le_succ, le_one, le_two, one_add_le_self, mul_zero, mul_succ, mul_one, zero_mul, succ_mul, mul_comm, one_mul, two_mul, mul_add, add_mul, mul_assoc, pow_zero, pow_succ, zero_pow_zero, zero_pow_succ, pow_one, one_pow, pow_two, pow_add, mul_pow, pow_pow, add_sq"



# prompt 
def build_prompt(nl_statement, current_lean_state, theorem_statement):
#     return f"""You are an expert Lean 4 programmer assisting in autoformalization.
# Your goal is to faithfully formalize a single step described in natural language by a student into *one single line* of valid Lean 4 tactic code.
# Output *only* the Lean 4 code line, without any explanation, comments, or markdown formatting. Output should be syntactically correct Lean 4 and directly correspond to the student's instruction. DO NOT USE simp. 

# {tactics}
# {theorems}

# Theorem to prove:
# {theorem_statement}

# Current Lean goal state: 
# {current_lean_state}

# Student's Natural Language Step:
# {nl_statement}

# Generate the single line of Lean 4 code for this step:
# """
    return f"""You are an expert Lean 4 programmer assisting in autoformalization.Your goal is to faithfully formalize a single step described in natural language by a student into *one single line* of valid Lean 4 tactic code.

Generate the single line of Lean 4 code for this step:
NL: {nl_statement}
FL: """





def autoformalize_deepseek(nl_statement, current_lean_state, theorem_statement): 
    prompt = build_prompt(nl_statement, current_lean_state, theorem_statement)
    
    # return pytorch tensor pt
    inputs = tokenizer(prompt, return_tensors = "pt", return_attention_mask=True).to(model.device)

    # inference 
    with torch.no_grad():
        outputs = model.generate(
            inputs.input_ids, # tokenized +vectorized inputs
            max_new_tokens = 100, 
            temperature = 0.1, 
            do_sample = True, # sample outputs, not greedy decoding
            top_p = 0.8, # nucleus sampling
            pad_token_id = tokenizer.eos_token_id
        )

    response = tokenizer.decode(outputs[0][inputs.input_ids.shape[1]:], skip_special_tokens=True)

    # clean response (remove ``` or lean4 from output)
    response = response.strip()
    response = response.removeprefix("```lean4").strip()
    response = response.removesuffix("```").strip()
    return response
    

# TEST BELOW

nl = "Simplify RHS 0 + a = a"
lean_state = '''2 goals
case zero
a : ℕ
⊢ a = 0 + a
case succ
a d : ℕ
hd : a + d = d + a
⊢ a + d.succ = d.succ + a'''
theorem_statement = "theorem add_commutative (a b : ℕ) : a + b = b + a"

print(autoformalize_deepseek(nl, lean_state, theorem_statement))

