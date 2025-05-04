import os
import json
from openai import OpenAI
from rag import lean_rag
from dotenv import load_dotenv
from lean_compile import lean_compile
import re
from pydantic import BaseModel

leanopeano_path = 'NNG4/Game/LevelsClean/Datasets/leanopeano_train_deviations.json'
tactic_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json'
theorem_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json'
embed_path_examples = 'NNG4/Game/LevelsClean/Datasets/Embeddings/leanopeano_embeddings_deviations.pt'
embed_path_theorem = 'NNG4/Game/LevelsClean/Datasets/Embeddings/theorem_embeddings.pt'
embed_path_tactic = 'NNG4/Game/LevelsClean/Datasets/Embeddings/tactic_embeddings.pt'

possible_actions = {
    'initiate induction': ['which variable to induct on'], 
    'continue the base case': ['which theorem to substitute'], 
    'continue in the inductive case': ['which theorem to substitute']
}

    # Load theorem and tactic dictionaries
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json', 'r') as f:
    theorem_dict = json.load(f)
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
    tactic_dict = json.load(f)


load_dotenv("NNG4/.env")
client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))

class ProofLine(BaseModel):
    action: str
    blanks: list[str]

def process_action(action: str, blanks: list[str], new_case = False):
    ans = ""
    if new_case:
        ans = "rfl"
    if action == 'initiate induction':
        ans += f'induction {blanks[0]} with d hd'
    elif action == 'continue the base case':
        ans += f'rw [{blanks[0]}]'
    elif action == 'continue in the inductive case':
        ans += f'rw [{blanks[0]}]'
    return ans

def autoformalize_structured(nl_statement: str, last_turn = {"action": "", "blanks": []}):
    prompt_action = f"""
    We are playing a math game related to induction. 
    I will tell you the last turn that the player made, what the controller told us to do and 
    the possible choices of things you can do and blanks/questions to fill if you choose the given choice.
    Your goal is to follow the controller as closely as possible.

    The last turn was:
    {last_turn}

    all possible theorems are:
    {theorem_dict}

    This is a dictionary of possible actions and the blanks/questions to fill if you choose the given action:
    {possible_actions}

    The controller told us to do:
    {nl_statement}
    """

    proof = client.beta.chat.completions.parse(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": prompt_action}],
        response_format=ProofLine,
    )
    output = proof.choices[0].message.content
    print(output)
    new_case = False
    if last_turn['action'] == "continue the base case":
        new_case = True
    lean_code = process_action(output['action'], output['blanks'], new_case)
    return {'raw action': output, 'lean code':lean_code}

def parse_unsolved_state(compiler_dump):
    # Parses the current goal states, if there are any, from the stdout dump
    def is_warning(line):
        warnings = ["error", "warning"]
        for warning in warnings:
            if(re.search(warning, line)):
                return True
        return False
    lines = compiler_dump.stdout.split("\n")
    lines = [i for i in lines if not is_warning(i) and len(i) > 2]
    return "".join([i + "\n" for i in lines])

def autoformalize(nl_statement: str, prev_fl = [], prev_goal = ""):
    # Get similar examples using RAG
    similar_examples = lean_rag(nl_statement, embed_path_examples, leanopeano_path)
    similar_tactics = lean_rag(nl_statement, embed_path_tactic, tactic_path, top_k=3)
    similar_theorems = lean_rag(nl_statement, embed_path_theorem, theorem_path, top_k=3)

    base_prompt = f"""
    Given a natural language mathematical statement, convert it to formal Lean theorem syntax.
    Use these similar examples as reference:
    {similar_examples}

    Here are available theorems and their descriptions:
    {json.dumps(theorem_dict, indent=2)}

    Here are available tactics and their descriptions:
    {json.dumps(tactic_dict, indent=2)}

    the output should match the one of the theorems and tactics exactly.
    Do not use multiple lines of lean code. You can use multiple premises per tactic if needed but each output will be 1 line.

    The previous lines of Lean code for this theorem are:
    {prev_fl}

    Now formalize this statement which is the next line of Lean code:
    {nl_statement}

    Output only the formal Lean theorem syntax with no additional text or explanation.
    """

    prompt = f"""
    Given a natural language mathematical statement, convert it to formal Lean theorem syntax.

    the output should match the one of the theorems and tactics exactly.
    Do not use multiple lines of lean code. You can use multiple premises per tactic if needed but each output will be 1 line.
    
    Use these similar examples of lines of Lean code as reference:
    {similar_examples}

    Now formalize this statement which is a line of Lean code while proving the theorem:
    {nl_statement}

    The current goal in lean is:
    {prev_goal}

    This goal is the current state the proof is in. Please use the natural language statement to formalize the next tactic to prove the theorem.

    Output only the formal Lean theorem syntax with no additional text or explanation.
    """

    # Get completion from GPT
    response = client.chat.completions.create(
        model="gpt-4o",
        messages=[{"role": "user", "content": prompt}]
    )

    formalized = response.choices[0].message.content.strip()
    return formalized

def evaluate_test_set(test_file: str):
    """Evaluate autoformalization on a test set"""
    with open(test_file, 'r') as f:
        test_data = json.load(f)

    results = []
    
    current_theorem = ""
    theorem_def = ""
    prev_fl = []
    # prev_goal = ""
    print(theorem_def)
    for item in test_data:
        print(current_theorem, item['NL'], prev_fl)
        nl = item['NL']
        theorem = item['theorem']
        expected_fl = item['FL']
        # print("prev_goal", prev_goal)
        raw_action, predicted_fl = autoformalize_structured(nl, prev_fl)
        if theorem == current_theorem:
            prev_fl.append(predicted_fl)
        else:
            theorem_def = item['FL'].split()[0] + ' ' + item['FL'].split()[1] + '_temp' + ' '.join(item['FL'].split()[2:])
            prev_fl = [theorem_def]
            current_theorem = theorem
        compiler_output = lean_compile(prev_fl, current_theorem)
        prev_goal = parse_unsolved_state(compiler_output)
        error = f"Compilation Error:\n{compiler_output.stdout}\n{compiler_output.stderr}"
        if error and "unsolved goals" not in error:
            prev_goal = ""
            print(f'NL: {item['NL']}, FL: {item['FL']}, error: {error}')

        # Remove 'theorem' and theorem name from expected/predicted if they start with 'theorem'
        if expected_fl.startswith('theorem'):
            expected_fl = ' '.join(expected_fl.split()[2:])
        if predicted_fl.startswith('theorem'):
            predicted_fl = ' '.join(predicted_fl.split()[2:])
        if predicted_fl.startswith('```lean'):
            predicted_fl = predicted_fl.split('```lean')[1].split('```')[0].strip()

        results.append({
            'NL': nl,
            'Expected': expected_fl,
            'Predicted': predicted_fl,
            'Correct': expected_fl.strip() == predicted_fl.strip()
        })

    # Calculate accuracy
    accuracy = sum(r['Correct'] for r in results) / len(results)

    return results, accuracy

if __name__ == "__main__":
    # Example usage
    test_file = 'NNG4/Game/LevelsClean/Datasets/leanopeano_val.json'
    test_file = 'NNG4/Game/LevelsClean/Datasets/leanopeano_val_deviations.json'
    results, accuracy = evaluate_test_set(test_file)

    print("\nDetailed Results:")
    for r in results:
        print(f"\nNL: {r['NL']}")
        print(f"Expected: {r['Expected']}")
        print(f"Predicted: {r['Predicted']}")
        print(f"Correct: {r['Correct']}")
    print(f"\nAccuracy: {accuracy:.2%}")