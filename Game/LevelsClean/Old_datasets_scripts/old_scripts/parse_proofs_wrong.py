import json
import re
import os
from lean_compile import lean_compile
from NNG4.Game.LevelsClean.Scripts.dataset_scripts.parse_states import parse_unsolved_state

def parse_lean_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()

    # Split into lines
    lines = content.split('\n')
    
    parsed_data = []
    current_theorem = None
    theorem_has_error = False
    
    for i, line in enumerate(lines):
        # Find theorem declarations
        if line.strip().startswith('theorem'):
            current_proof = line.strip().split()[0] + ' ' + line.strip().split()[1] + '_temp' + ' ' + ' '.join(line.strip().split()[2:])
            theorem_match = re.search(r'theorem\s+(\w+)', line)
            if theorem_match:
                current_theorem = theorem_match.group(1)
                out = lean_compile(current_theorem, proof = current_proof)
                state = parse_unsolved_state(out)
                theorem_has_error = False  # Reset error flag for new theorem
                # Add theorem declaration
                parsed_data.append({
                    "theorem": current_theorem,
                    "NL": "-- Theorem Declaration: " + get_proof_statement(lines, i),
                    "FL": line.strip(),
                    "state": state,
                    "is_error": False
                })
        
        # Find comments and their associated Lean code
        elif current_theorem and line.strip().startswith('--') and not theorem_has_error:
            # Skip if this is the proof statement comment
            if "Proof Statement:" in line:
                continue
                
            comment = line.strip()
            # Get the next non-empty line (should be Lean code)

            
            next_code, is_error = get_next_code_line(lines, i)
            current_proof += "\n" + next_code.strip()
            out = lean_compile(current_theorem, proof = current_proof)
            state = parse_unsolved_state(out)
            if next_code:
                parsed_data.append({
                    "theorem": current_theorem,
                    "NL": comment,
                    "FL": next_code.strip(),
                    "state": state,
                    "is_error": is_error
                })
                
                # If this step has an error, set the flag to skip remaining steps in this theorem
                if is_error:
                    theorem_has_error = True
    
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
            if "error" in lines[idx].strip(): 
                return lines[idx], True
            return lines[idx], False
        idx += 1
    return None, None

def write_json(data, output_file):
    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)

# Main execution
# input_file = "/Users/arnavmehta/Desktop/GITHUBLeanTutor/LeanTutor/NNG4/Game/LevelsClean/Datasets/FullDataSet/Wrong/Skipped_AdditionClean.lean"
# output_file = "/Users/arnavmehta/Desktop/GITHUBLeanTutor/LeanTutor/NNG4/Game/LevelsClean/incorrect_world_vals/incorrect_Addition_world_val.json"
# parsed_data = parse_lean_file(input_file)
# write_json(parsed_data, output_file)

def process_skipped_files(input_dir, output_dir):
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    # Get all files that start with "Skipped" in the input directory
    for filename in os.listdir(input_dir):
        if filename.startswith("IncompleteProofs"):
            input_file = os.path.join(input_dir, filename)
            
            # Extract the world name from the filename (remove "Skipped_" and ".lean")
            world_name = filename[8:].replace("Clean.lean", "")
            
            # Create output filename
            output_file = os.path.join(output_dir, f"incorrect_proofs.json")
            
            print(f"Processing {input_file} -> {output_file}")
            
            # Parse and write to JSON
            parsed_data = parse_lean_file(input_file)
            write_json(parsed_data, output_file)
            
            print(f"Successfully processed {filename}")

# Example usage
input_directory = "NNG4/Game/LevelsClean/Datasets/FullDataSet/Wrong"
output_directory = "NNG4/Game/LevelsClean/incorrect_world_vals"

process_skipped_files(input_directory, output_directory)