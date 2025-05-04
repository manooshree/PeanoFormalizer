from openai import OpenAI
import os
import re
correct_lean_path = '/Users/manooshreepatel/dev/LeanTutor/NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_lean/'
noncorrect_lean_path = '/Users/manooshreepatel/dev/LeanTutor/NNG4/Game/LevelsClean/Datasets/full_clean_dataset/non-correct_lean'

# Manooshree's key below
openai_key = ""

WORLDS = [
    # ('implication_world_val', 'exact_2'), exact_2 removed from analysis as there are no deviations in Lean

    ('multiplication_world_val', 'zero_mul'),
    ('AdvMultiplication_world_val', 'mul_left_ne_zero'),
    ('algorithm_world_val', 'add_left_comm'), 
    ('less_or_equal_world_val', 'le_two'),
    ('power_world_val', 'zero_pow_succ'),
    ('tutorial_world_val', 'succ_eq_add_one'),
    ('AdvAddition_world_val', 'add_right_eq_zero'),
    ('addition_world_val', 'zero_add')
]





def select_proofs(worlds, base_path):
    selected_proofs = []

    for filename, prefix in worlds:
        filepath = os.path.join(base_path, f'{filename}.lean')
        with open(filepath, 'r') as file:
            content = file.read()

        # Correct proofs start with "Proof Statement" and non-correct proofs start with "Theorem Declaration"
        # proofs = re.split(r'--\s*Proof Statement:', content)
        proofs = re.split(r'--\s*Theorem Declaration:', content)


        for proof in proofs:
            if f'theorem {prefix}_' in proof:
                # print(filename, f'theorem {prefix}_')
                selected_proofs.append('-- Proof Statement:' + proof.strip())

    return selected_proofs

def strip_nl(proof: str) -> str: 
    lines = proof.strip().splitlines()
    proof_body = []
    for line in lines: 
        line = line.strip()
        # separate proof statement line
        if line.startswith("--Proof") or line.startswith("-- Proof"): 
            proof_statement = line.replace("--", "").strip()
        # append each proof line to proof body
        elif line.startswith("--"): 
            proof_body.append(line.replace("--", "").strip())
        else: 
            continue
    proof_body = "\n".join(proof_body)
    return proof_statement, proof_body


def openai_call(statement: str, proof: str) -> str:
    client = OpenAI(api_key=openai_key)
    prompt = f'''You are grading an undergraduate student's proof submission proving {statement}. 
    Is the following proof correct or incorrect? 
    {proof} 
    Answer with "Yes" if the proof is correct or "No" if the proof is not correct. Do not reply with anything else.'''
    print(prompt)
    response = client.chat.completions.create(
            model="gpt-4",
            messages=[
                {"role": "system", "content": "You are a math professor who teaches undergraduate students."},
                {"role": "user", "content": prompt},
            ],
            temperature=0,  # Set temperature to 0 for grading: deterministic, no randomness
        )
    return response.choices[0].message.content.strip()



'''
Select the experiment proofs across all worlds. 
Remove Lean from proof. 
Prompt GPT-4 to assess if proof is correct or incorrect 
'''
def main():
    proofs = select_proofs(WORLDS, noncorrect_lean_path)
    nl_proofs = []
    for proof in proofs: 
        nl_proofs.append(strip_nl(proof))
    
    yes = 0
    no = 0
    total = 0
    for statement, proof in nl_proofs: 
        assessment = openai_call(statement, proof)
        assessment = assessment.strip().strip('.')
        if assessment == "Yes": 
            yes += 1
        elif assessment == "No": 
            no += 1
        else: 
            print("GPT-4 printed out something other than Yes/No: ")
            print(assessment)
        total += 1
    print(f"{yes} proofs were correct and {no} proofs were incorrect out of {total} total proofs")

main()


