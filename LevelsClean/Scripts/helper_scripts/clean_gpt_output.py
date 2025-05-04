import json
import re

with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
    tactic_dict = json.load(f)

LIST_TACTICS = [tactic['FL'].split()[0] for tactic in tactic_dict]

def clean_formalized(formalized: str):
    formalized = formalized.strip()
    for tactic in LIST_TACTICS:
        if tactic in formalized:
            second_index = formalized.find(tactic, 1)
            if second_index != -1:
                formalized = formalized[:second_index].strip("\n ,\t")
    return formalized