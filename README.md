# PeanoFormalizer
A low-resource training approach for faithful Lean autoformalization of natural language proofs. We train PeanoFormalizer, a language model that faithfully autoformalizes natural language proofs into formal Lean syntax. Importantly, we release our training and evaluation pipelines. Our framework is model-agnostic and can effectively be used to train on other model families. 

The original ~80 Peano Arithmetic proofs in lean are derived from the [Natural Numbers Game](https://github.com/leanprover-community/NNG4). <br/>
You can develop this repo as any lean project and use ```lake build``` to build it. If this is your first time installing Lean, we recommend [this guide](https://leanprover-community.github.io/get_started.html). 

Repo Map:
Dataset: Game/LevelsClean/Datasets/full_clean_dataset <br/>
Scripts: Game/LevelsClean/Scripts (Those prefixed with _282_) <br/>
Model weights were not included in the repo, but our entire training pipeline is present. <br/>


Repo contributors: Manooshree Patel, Arnav Mehta, Rayna Bhattacharyya*, Thomas Lu*, Niels Voss* <br/>
*(Rayna, Thomas, and Niels are not students in CS182/282, but some scripts for this final project build on work from the LeanTutor project they contributed to.)


