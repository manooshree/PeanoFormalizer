import os
import json
import openai
from pathlib import Path
from dotenv import load_dotenv
from openai import OpenAI
from lean_compile import lean_compile

load_dotenv("NNG4/.env")
client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))   

with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json', 'r') as f:
    theorem_dict = json.load(f)
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
    tactic_dict = json.load(f)

def generate_synthetic_proofs(theorem, examples):
    # Configure OpenAI
    openai.api_key = os.getenv("OPENAI_API_KEY")

    proof_statement = theorem.split("\n")[0:2]
    proof_statement = "\n".join(proof_statement)

    print(proof_statement)
    prompt = f"""Given this Lean proof:
        {theorem}

        Generate 5 DIFFERENT valid versions of the natural language comments of this proof do not change the lean code. 
        Each comment starts with -- and ends with a period and is on a new line right before the line of code it is explaining.
        One comment is for one line of code.

        separate each proof with three dashes \n---
        The natural language comments must be differnt from each other.

        Try these different styles when writing the comments:
        - bare minimum comments
        - descriptive comments
        - wordy comments
        
    """

    # system_prompt = f"""You are an expert in Lean theorem proving. 
    #     Some past proof deviation examples are: {examples} follow the format of the examples closely, the changes should be similar but not the exact same.
    #     You must generate 5 different proofs that achieve the same result.
    #     IMPORTANT: Each version of the proof must be different from every other version and the examples provided.
    #     IMPORTANT: Do not use the theorem you're trying to prove in your proof.
    # """

    try:
        response = client.chat.completions.create(
            model="gpt-4",
            messages=[
                {"role": "user", "content": prompt}
            ],
            temperature=0.7
        )
        
        # Split response into individual proofs
        synthetic_proofs = response.choices[0].message.content.split("\n---")
        for proof in synthetic_proofs:
            print(proof)
            print("\n")
        return [theorem] + [proof.strip() for proof in synthetic_proofs]
    
    except Exception as e:
        print(f"Error generating synthetic proofs: {e}")
        return []

def main():
    # Read original theorems
    input_file = "NNG4/Game/LevelsClean/Datasets/theorems_with_comments.json"
    output_file = "NNG4/Game/LevelsClean/Datasets/leanopeano_train_synthetic.json"
    
    if not os.path.exists(input_file):
        print(f"Input file {input_file} not found!")
        return
        
    with open(input_file, 'r') as f:
        theorems = json.load(f)
    
    all_synthetic_proofs = []

    # Randomly select 10 theorems
    import random
    examples = [theorem for theorem in random.sample(theorems, 15) if "theorem succ_add" not in theorem]

    print(f"Processing theorem {1}/{len(theorems)}")
    synthetic_versions = generate_synthetic_proofs(theorems[31], examples) # succ add
    all_synthetic_proofs.extend([{"proof": proof, "compiled": None, "error": None} for proof in synthetic_versions])

    # Process each theorem
    # for i, theorem in enumerate(theorems):
    #     print(f"Processing theorem {i+1}/{len(theorems)}")
    #     synthetic_versions = generate_synthetic_proofs(theorem)
    #     all_synthetic_proofs.extend(synthetic_versions)
    
#   {
#     "theorem": "add_right_comm",
#     "NL": "Prove that the addition of natural numbers is commutative, that is a + b + c = a + c + b",
#     "FL": "theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by",
#     "filename": "AdditionClean.lean"
#   },

    proof_dict = []

    # Compile the proofs
    for i, proof in enumerate(all_synthetic_proofs):
        result = lean_compile(proof=proof["proof"], file_name=f"temp_{i}")
        if result:
            print("proof did not compile", result)

        # Save proof
        proof_lines = proof["proof"].split("\n")
        print("Proof lines", proof_lines)
    # Save synthetic proofs
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(all_synthetic_proofs, f, indent=2)
        
    print(f"Generated {len(all_synthetic_proofs)} synthetic proofs saved to {output_file}")

if __name__ == "__main__":
    main()
