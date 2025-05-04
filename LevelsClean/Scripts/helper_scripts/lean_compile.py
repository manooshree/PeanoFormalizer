import os
import subprocess
import re
def build_str(tactics: str):
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
{tactics[0]}
{''.join('  ' + tactic + chr(10) for tactic in tactics[1:])}
end MyNat
"""

def build_str_with_proof(proof: str):
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
{proof}
end MyNat
    """
def lean_compile(file_name: str, tactics: str = "", proof: str = ""):
    if not proof:
        clean_tactics = []
        for tactic in tactics:
            if tactic.startswith('```lean'):
                tactic = tactic.split('```lean')[1].split('```')[0].strip()
            clean_tactics.append(tactic.strip('`'))
        state = build_str(clean_tactics)
    else:
        state = build_str_with_proof(proof)
    temp_file_path = f'NNG4/Game/LevelsClean/lean_files/{file_name}.lean'

    # Create temp file in the correct location
    try:
        # Ensure the directory exists
        os.makedirs(os.path.dirname(temp_file_path), exist_ok=True)

        # Write the Lean code to a temporary file
        with open(temp_file_path, "w") as f:
            f.write(state)

        # Try compiling with explicit project root
        result = subprocess.run(
            ['lake', 'env', 'lean', f'Game/LevelsClean/lean_files/{file_name}.lean'],
            capture_output=True,
            text=True,
            cwd="NNG4",  # Change working directory to NNG4 where Game module is located
            timeout=30
        )
        return result
        # Check compilation result
        if result.returncode == 0:
            return False  # Successful compilation
        else:
            # Return detailed error output
            return f"Compilation Error:\n{result.stdout}\n{result.stderr}"

    except subprocess.TimeoutExpired:
        return "Compilation timed out"
    except Exception as e:
        return f"Compilation error: {str(e)}"

# if __name__ == "__main__":
#     lean_compile(["```lean\nexample : 1 + 1 = 2 :=\nbegin\n  refl\nend\n```"], "test")