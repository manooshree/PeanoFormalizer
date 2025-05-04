import os
import subprocess

script_dir = os.path.dirname(os.path.abspath(__file__))
# os.chdir(os.path.join(script_dir, "../../../"))
project_root = os.path.abspath(os.path.join(script_dir, "../../../"))

def build_str(tactics: str):
    #proof_body = "\n".join("  " + tactic for tactic in tactics[1:]) 
    proof_body = tactics

    return f"""
import Game.LevelsClean.MultiplicationClean
import Game.MyNat.Power
import Game.Metadata
import Game.MyNat.Addition
import Game.LevelsClean.TutorialClean
import Game.LevelsClean.ImplicationClean
import Game.LevelsClean.AlgorithmClean
import Game.LevelsClean.LessOrEqualClean
import Game.LevelsClean.MultiplicationClean
import Game.MyNat.PeanoAxioms
import Game.MyNat.LE
import Game.Tactic.Use
import Game.LevelsClean.AdvAdditionClean

namespace MyNat
{tactics}
end MyNat
"""

def lean_compile(tactics: str, file_name: str):
    

    # print("tactics", tactics)
    clean_tactics = [
    tactic.split('```lean')[1].split('```')[0].strip() if tactic.startswith('```lean') else tactic
    for tactic in tactics]
    #print(clean_tactics)
    #state = build_str(clean_tactics)
    state = build_str(tactics)
    
    # print("\nGenerated Lean file content:")
    # print(state)
    # temp_file_path = f'Game/LevelsClean/Manooshree_tests/test_autoformalize.lean'
    temp_file_path = os.path.join(project_root, 'Game/LevelsClean/Manooshree_tests/test_autoformalize.lean')


    try:
        os.makedirs(os.path.dirname(temp_file_path), exist_ok=True)
        with open(temp_file_path, "w") as f:
            f.write(state)

        result = subprocess.run(
            ['lake', 'env', 'lean', f'Game/LevelsClean/Manooshree_tests/test_autoformalize.lean'],
            capture_output=True,
            text=True,
            timeout=30, 
            cwd = project_root
        )
        # print("Result of subprocess")
        # print(result)

        # Check compilation result
        if result.returncode == 0:
            message = False  # Successful compilation
        else:
            # Check if error is just unsolved goals
            if "error: unsolved goals" in result.stdout:
                message =  "UNSOLVED_GOALS"
            else:
                # Return other errors
                message =  f"Compilation Error:\n{result.stdout}\n{result.stderr}"
        return message, result

    except subprocess.TimeoutExpired:
        return "Compilation timed out"
    except Exception as e:
        return f"Compilation error: {str(e)}"