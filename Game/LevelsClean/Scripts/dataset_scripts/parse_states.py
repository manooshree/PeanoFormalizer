import re
import os
import time
import multiprocessing as mp
from helper_scripts.lean_compile import lean_compile

import sys
sys.path.append('../')

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

def parse_steps_from_proof(proof):
    # Extracts the list of steps in a proof as a list, deleting comments and whitespace
    proof_steps = proof.split("\n")
    proof_steps = [step.strip() for step in proof_steps]
    proof_steps = [step for step in proof_steps if len(step) > 0 and not step[:2] == "--"]
    return proof_steps

def _extract_states_map_func(args):
    # Unpack arguments
    theorem, tactics, working_dir = args
    out = lean_compile(theorem, tactics, f"extract_states_{os.getpid()}", working_dir=working_dir)
    return parse_unsolved_state(out)

def extract_intermediate_states(proof, num_threads=16, verbose=False, working_dir=None, as_set=True):
    # Extracts the intermediate goal states of the proof
    steps = parse_steps_from_proof(proof)
    theorem, tactics = steps[0], steps[1:]

    tactic_subsets = [tactics[:i] for i in range(len(tactics)+1)]
    
    # Create argument tuples for the map function
    map_args = [(theorem, tactics, working_dir) for tactics in tactic_subsets]
    
    clock = time.time()
    with mp.Pool(num_threads) as p:
        inter_states = p.map(_extract_states_map_func, map_args)
    if verbose:
        print(f"Extracted {len(tactic_subsets)} intermediate states in {round(time.time() - clock, 2)} seconds with {num_threads} threads.")

    if as_set:
        inter_states = set(inter_states)
    return inter_states[-1], inter_states