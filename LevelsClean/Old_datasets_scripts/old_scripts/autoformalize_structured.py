from openai import OpenAI
from dotenv import load_dotenv
import os
import re
import json
from pydantic import BaseModel
from autoformalize import autoformalize


class ProofType(BaseModel):
    proof_type: str
    confidence: float

# class ProofSection(BaseModel):
#     proof_statement: str
#     full_proof: str

class ProofSteps(BaseModel):
    steps: list[str]
class InductionProof(BaseModel):
    base_case: str
    inductive_step: str

class DirectProof(BaseModel):
    proof: str

load_dotenv("NNG4/.env")
client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))       

def autoformalize_structured(proof: str):
    proof_type = get_structure(proof)['proof_type']
    parsed_proof = parse_proof(proof, proof_type)
    print("parsed_proof", parsed_proof)
    full_proof = ""
    for section in parsed_proof:
        print("section", section)
        print("section[1]", section[1])
        steps = parse_direct(section[1])
        print("steps", steps)
        for step in steps['steps']:
            lean = autoformalize(step)
            print("lean", lean)
            full_proof += lean
    return full_proof

def get_structure(proof: str):
    proof_types = ["Induction", "Direct"]

    prompt = f"""
    Given a proof, determine the type of proof.
    The proof types are:
    {proof_types}

    The proof is:
    {proof}
    """
    response = client.beta.chat.completions.parse(
        model="gpt-4o-mini",
        messages=[
            {"role": "user", "content": prompt}
        ],
        response_format=ProofType,
    )
    print(response.choices[0].message.content)
    return json.loads(response.choices[0].message.content)

def parse_proof(proof: str, proof_type: str):
    if proof_type == "Induction":
        return parse_induction(proof)
    elif proof_type == "Direct":
        return parse_direct(proof)
    
def parse_induction(proof: str):
    get_base_prompt = f"""
        Extract the base case of the proof word for word. Do not make any additions or subtractions.
        Only return what was in the proof and nothing else.
        {proof}
    """
    base_case = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "user", "content": get_base_prompt}
        ]
    )
    print(base_case.choices[0].message.content)
    base_case = base_case.choices[0].message.content

    get_inductive_prompt = f"""
        Extract the inductive step of the proof word for word. Do not make any additions or subtractions.
        Only return what was in the proof and nothing else.
        {proof}
    """
    inductive_step = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "user", "content": get_inductive_prompt}
        ])
    inductive_step = inductive_step.choices[0].message.content

    return InductionProof(base_case=base_case, inductive_step=inductive_step)

def parse_direct(proof: str):
    get_proof_prompt = f"""
        break the proof up into granular steps.
        {proof}
    """
    proof = client.beta.chat.completions.parse(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": get_proof_prompt}],
        response_format=ProofSteps,
    )
    return json.loads(proof.choices[0].message.content)

if __name__ == "__main__":
    exmaple_proof = '''
    Prove that a + b = b + a

    Induct on b, the base case is a + 0 = 0 + a. This is trivial, and I assume there is a lemma that asserts this.  

    Moving to (n+1) we are given that a + n = n + a and we need to show that a + n+1 =  n+1 + a we simplify this to (a+n)+1 = (n+a)+1 and now we substitute the hypothesis giving us (a+n)+1 = (a+n)+1
    '''
    print(autoformalize_structured(exmaple_proof))