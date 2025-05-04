import json
import re

with open('incorrect_supplemental.json', 'r') as file:
    proofs = json.load(file)

lean_dump = ""
for world in proofs.keys():
    proofs_list = proofs[world]
    for proof in proofs_list:
        proof_text = proof["full_proof"].split("\n")

        lean_dump += f"-- Proof statement: {proof['theorem']}\n{proof_text[0]}\n  -- sample comment"
        
        proof_text = proof_text[1:]
        for line in proof_text:
            lean_dump += f"\n  {line}"
            if(re.search("error", line)):
                break

        lean_dump += "\n\n"

with open('incorrect_supplemental_add.lean', 'w', encoding="utf-8") as file:
    file.write(lean_dump)