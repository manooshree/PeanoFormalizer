import os
import json
from openai import OpenAI
from rag import lean_rag
from dotenv import load_dotenv
from lean_compile import lean_compile
import re
from pydantic import BaseModel
import threading

leanopeano_path = 'NNG4/Game/LevelsClean/Datasets/leanopeano_train_deviations.json'
add_succ_path = 'NNG4/Game/LevelsClean/Datasets/add_succ_train.json'
tactic_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json'
theorem_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json'
embed_path_examples = 'NNG4/Game/LevelsClean/Datasets/Embeddings/leanopeano_embeddings_deviations.pt'
embed_path_theorem = 'NNG4/Game/LevelsClean/Datasets/Embeddings/theorem_embeddings.pt'
embed_path_tactic = 'NNG4/Game/LevelsClean/Datasets/Embeddings/tactic_embeddings.pt'
embed_path_add_succ = 'NNG4/Game/LevelsClean/Datasets/Embeddings/add_succ_embeddings.pt'

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

def autoformalize(nl_statement: str, proof_name: str, proof: str):
    # Get similar examples using RAG
    similar_examples = lean_rag(nl_statement, embed_path_examples, leanopeano_path, top_k=5)
    proof_steps = proof.split("\n\n")
    possible_fl = [proof_steps[i].split("\n") for i in range(len(proof_steps)) if i % 2 == 1]
    possible_fl.extend(similar_examples)

    # Give me the index of the line of lean code that represents the natural language statement in the list of similar examples provided below:
    # {similar_examples}

    prompt = f"""
    We are trying to formalize the following theorem:
    {proof_name}

    Here is one possible proof of this theorem:
    {proof}

    Here are other possible lines of lean code that could be used to prove this theorem:
    {similar_examples}

    Given a natural language mathematical statement, convert it to formal Lean theorem syntax.

    This is the natural language statement:
    {nl_statement}

    IMPORTANT: Output only the line of lean code with no other formatting.
    """

    # Get completion from GPT
    response = client.chat.completions.create(
        model="o1-preview",
        messages=[{"role": "user", "content": prompt}]
    )
    # print("NL", nl_statement)
    # print('index', response.choices[0].message.content)
    # print('similar_examples', similar_examples)
    res = response.choices[0].message.content.strip()
    if res.isdigit() and int(res) < len(similar_examples):
        formalized = similar_examples[int(res)]
    else:
        formalized = similar_examples[0]
    return formalized

def autoformalize_threaded(nl_statements: list[str], results: list[dict], result_lock: threading.Lock, expected_fls: list[str], thread_num: int, correct_proof: str):
    for i, nl, expected_fl in zip(range(len(nl_statements)), nl_statements, expected_fls):
        print(f"Thread {thread_num} num_processed: {i}/{len(nl_statements)}")
        if not expected_fl.startswith("theorem"):
            predicted_fl = autoformalize(nl, "add_succ", correct_proof)
            with result_lock:
                results.append({
                    'NL': nl,
                    'Expected': expected_fl,
                    'Predicted': predicted_fl,
                    'Correct': expected_fl.strip() == predicted_fl.strip()
                })
                if len(results) % 15 == 0:
                    print("thread", thread_num, "current accuracy: ", sum(r['Correct'] for r in results) / len(results))
    return results

def evaluate_test_set(test_file: str, correct_proof: str):
    """Evaluate autoformalization on a test set"""
    with open(test_file, 'r') as f:
        test_data = json.load(f)

    test_data_proofs = test_data[5:]
    results = []

    threads = []
    num_threads = 5
    result_lock = threading.Lock()
    for i in range(num_threads):
        # print(current_theorem, item['NL'], prev_fl)
        nls = [test_data_proofs[j]['NL'] for j in range(i, len(test_data_proofs), num_threads)]
        # theorem = item['theorem']
        expected_fls = [test_data_proofs[j]['FL'] for j in range(i, len(test_data_proofs), num_threads)]
        # print("prev_goal", prev_goal)
        thread = threading.Thread(target=autoformalize_threaded, args=(nls, results, result_lock, expected_fls, i, correct_proof))
        threads.append(thread)
        thread.start()

    for thread in threads:
        thread.join()
    # Calculate accuracy
    accuracy = sum(r['Correct'] for r in results) / len(results)

    return results, accuracy

if __name__ == "__main__":
    # Example usage
    test_file = 'NNG4/Game/LevelsClean/Datasets/add_succ_val.json'
    # test_file = 'NNG4/Game/LevelsClean/Datasets/leanopeano_val_synthetic.json'

    correct_proof = f"""
    "-- Proof Statement: Prove that succ (a) + b  = succ (a + b) for all natural numbers
    theorem succ_add (a b : \u2115) : succ a + b = succ (a + b)  := by
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
    """
    results, accuracy = evaluate_test_set(test_file, correct_proof)

    print("\nDetailed Results:")
    for r in results:
        print(f"\nNL: {r['NL']}")
        print(f"Expected: {r['Expected']}")
        print(f"Predicted: {r['Predicted']}")
        print(f"Correct: {r['Correct']}")
    print(f"\nAccuracy: {accuracy:.2%}")