import json
import re
from lean_compile import lean_compile
from NNG4.Game.LevelsClean.Scripts.dataset_scripts.parse_states import parse_unsolved_state

def parse_lean_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()

    # Split into lines
    lines = content.split('\n')
    
    parsed_data = []
    current_theorem = None
    
    for i, line in enumerate(lines):
        # Find theorem declarations
        if line.strip().startswith('theorem'):
            current_proof = line.strip().split()[0] + ' ' + line.strip().split()[1] + '_temp' + ' ' + ' '.join(line.strip().split()[2:])
            theorem_match = re.search(r'theorem\s+(\w+)', line)
            if theorem_match:
                current_theorem = theorem_match.group(1)
                out = lean_compile(current_theorem, proof = current_proof)
                state = parse_unsolved_state(out)\
                # Add theorem declaration
                parsed_data.append({
                    "theorem": current_theorem,
                    "NL": "-- Theorem Declaration: " + get_proof_statement(lines, i),
                    "FL": line.strip(),
                    "state": state
                })
        
        # Find comments and their associated Lean code
        elif current_theorem and line.strip().startswith('--'):
            # Skip if this is the proof statement comment
            if "Proof Statement:" in line:
                continue
                
            comment = line.strip()
            # Get the next non-empty line (should be Lean code)
            next_code = get_next_code_line(lines, i)
            if next_code:
                current_proof += "\n" + next_code.strip()
                out = lean_compile(current_theorem, proof = current_proof)
                state = parse_unsolved_state(out)
                parsed_data.append({
                    "theorem": current_theorem,
                    "NL": comment,
                    "FL": next_code.strip(),
                    "state": state
                })

    return parsed_data

def get_proof_statement(lines, theorem_line_idx):
    # Look for proof statement in comments before the theorem
    for i in range(theorem_line_idx - 3, theorem_line_idx):
        if i >= 0 and "Proof Statement:" in lines[i]:
            return lines[i].split("Proof Statement:")[1].strip()
    return ""

def get_next_code_line(lines, comment_line_idx):
    idx = comment_line_idx + 1
    while idx < len(lines):
        if lines[idx].strip() and not lines[idx].strip().startswith('--'):
            return lines[idx]
        idx += 1
    return None

def write_json(data, output_file):
    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)

incomplete_worlds = [
    # ('addition_world_val', 'AdditionClean'),
    ('AdvAddition_world_val', 'AdvAdditionClean'),
    # ('multiplication_world_val', 'MultiplicationClean'),
    # ('AdvMultiplication_world_val', 'AdvMultiplicationClean'),
    # ('algorithm_world_val', 'AlgorithmClean'),
    # ('less_or_equal_world_val', 'LessOrEqualClean'),
    # ('power_world_val', 'PowerClean'),
    # ('tutorial_world_val', 'TutorialClean'),
    # ('implication_world_val', 'ImplicationClean')
]

for world in incomplete_worlds:
    # Main execution
    print(f"Parsing {world[0]}")   
    input_file = f"NNG4/Game/LevelsClean/Datasets/FullDataSet/Wrong/Truncated_{world[1]}.lean"
    output_file = f"NNG4/Game/LevelsClean/Datasets/world_vals_incomplete/{world[0]}.json"
    parsed_data = parse_lean_file(input_file)
    write_json(parsed_data, output_file)
