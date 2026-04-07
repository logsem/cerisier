# Cerisier: A Program Logic for Attestation
This repository contains the Rocq mechanization accompanying the submission 
"Cerisier: A Program Logic for Attestation".
It provides a model of a capability machine featuring local attestation
and principles to reason about the interaction of known, unknown, and attested code.
Cerisier extends the Cerise capability machine. 
We do not assume prior experience with Cerise.

# Getting Started Guide

For ease of setup, we provide a Docker image. We encourage making use of it over manual installation since package management can sometimes be tricky.

## With Docker

Proceed by building the Docker image. This step takes approximately 15 minutes to build the Docker
image, because it installs all the dependencies.

```sh
$ docker build -t cerisier:pldi26 .
```

Next, run the loaded image to spawn a container.

```sh
$ docker run -it --hostname cerisier --rm cerisier:pldi26
```

This drops you in a shell at `/home/rocq/cerisier` under the `rocq` user. This directory contains all the artifact's sources, and the container provides all dependencies needed for compiling from these sources.

From this directory, invoke the Makefile with the `fundamental` target to double-check that everything is in working order. This can take up to 15 minutes on some machines.

```sh
rocq@cerisier:~/cerisier$ make fundamental -j$(nproc)
```

Ensure the output matches what is below:

```
... [omitted] ...
COQC theories/proofmode/classes.v
COQC theories/proofmode/contiguous.v
COQC theories/proofmode/tactics_helpers.v
COQC theories/proofmode/proofmode_instr_rules.v
COQC machine_utils/theories/class_instances.v
COQC theories/proofmode/class_instances.v
COQC theories/proofmode/solve_addr_extra.v
COQC machine_utils/theories/solve_pure.v
COQC theories/proofmode/solve_pure.v
COQC theories/utils/NamedProp.v
COQC machine_utils/theories/tactics.v
COQC theories/proofmode/proofmode.v
COQC theories/logrel/ftlr/EInit.v
COQC theories/logrel/ftlr/EDeInit.v
COQC theories/logrel/ftlr/EStoreId.v
COQC theories/logrel/fundamental.v
make[1]: Leaving directory '/home/rocq/cerisier'
```

The output should list all recursive dependencies up to and including `theories/logrel/fundamental.v` being compiled by `COQC`.
This is sufficient for a kick-the-tyres session to ensure everything else will also compile successfully.


## Without Docker

### Obtaining Cerisier

The Cerisier sources can be obtained through GitHub by cloning the git repository:

```
git clone https://github.com/logsem/cerisier.git --depth=1
```

### Building the proofs

The repository depends on the submodule `machine_utils`.
After cloning Cerisier, you can load the submodule using
```
git submodule update --init
```

#### Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.18.0, stdpp 1.9.0, and Iris 4.1.0. 
To install those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.14.2
eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.14.0:

```
    # Add the coq-released repo (skip if you already have it)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install coq.8.18.0 coq-iris.4.1.0 coq-equations.1.3+8.18
```

#### Troubleshooting

If the `opam switch` invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y .` (this will continue from where it failed).

#### Building

This artifact requires at least 8 GB of RAM to build successfully, and more will make building faster.

```
make -jN  # replace N with the number of CPU cores of your machine
```
We recommend using `-j1` (the default) if you have less then 16Gb of RAM.
Please be aware that the development takes around an hour to compile with `-j1`.

In particular, the files `theories/case_studies/mutual_attestation/mutual_attestation_A_spec.v`
and `theories/case_studies/mutual_attestation/mutual_attestation_B_spec.v`
can each take up to 10 minutes and up to 8Gb of RAM to compile.

It is possible to run `make fundamental` to only build files up to the Fundamental Theorem. This should take less than 15 minutes.

# Step by step Instructions

Our artifact is a mechanization of the definitions, theorems, and proofs discussed in the paper. There, we discuss three case studies. Ensure that these case studies compile successfully by running `make` (this can take up to 45 minutes on some machines):

```sh
rocq@cerisier:~/cerisier$ make
```

You can double check to make sure that `theories/case_studies` is in fact listed in stdout. I.e. it contains

```
COQC theories/case_studies/template_adequacy_attestation.v
COQC theories/case_studies/soc/soc_code.v
COQC theories/case_studies/soc/soc_enclave_spec.v
COQC theories/case_studies/soc/soc_spec.v
COQC theories/case_studies/soc/soc_adequacy.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_code.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_client_spec.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_sensor_spec.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_enclaves_spec.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_main_spec.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_spec.v
COQC theories/case_studies/memory_readout/trusted_memory_readout_adequacy.v
COQC theories/case_studies/mutual_attestation/mutual_attestation_code.v
COQC theories/case_studies/mutual_attestation/mutual_attestation_A_spec.v
COQC theories/case_studies/mutual_attestation/mutual_attestation_B_spec.v
COQC theories/case_studies/mutual_attestation/mutual_attestation_spec.v
COQC theories/case_studies/mutual_attestation/mutual_attestation_adequacy.v
```

We make 3 claims about our artifact in the paper.

1. We do not rely on any axioms, except those discussed in the paper.
2. The Rocq development comprises around 35k LoC/LoP.
3. The artifact's definitions and theorems are faithful to the paper.

## 1. No axioms used except those discussed in the paper

In the paper we claim that our Rocq development relies on the following assumptions about the machine:
- (Inherited from Cerise) there exist `encode` and `decode` functions for instructions and permissions.
Encoding is injective. Decoding is the inverse of encoding. 
- (New for Cerisier) there exist `hash` and `hash_concat` functions. These are both injective, and several algebraic properties hold for these functions (Paper: lines 519-521).
These assumptions are part of the `MachineParameters` typeclass in `opsem/machine_parameters.v`.

Axioms can be printed using the Rocq command `Print Assumptions`.

We have already prepared a file `theories/assumptions.v` that does exactly that for the entire codebase. Invoke `make assumptions` from the root directory (this can take up to 45 min if you did not compile the project earlier):

```sh
rocq@cerisier:~/cerisier$ make assumptions
```

The output should resemble what's below.

``` text
COQC theories/Assumptions.v
Assumptions of fundamental theorem:
Closed under the global context

Assumptions of SOC end-to-end theorem:
Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g

Assumptions of trusted memory readout end-to-end theorem:
Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g

Assumptions of mutual attestation end-to-end theorem:
Axioms:
hash_cap.hash_singleton
  : forall (H : machine_parameters.MachineParameters) (A : Type) (a : A),
    machine_parameters.hash (a :: nil)%list = machine_parameters.hash a
hash_cap.hash_concat_assoc
  : forall H : machine_parameters.MachineParameters,
    base.Assoc eq machine_parameters.hash_concat
hash_cap.hash_concat_app
  : forall (H : machine_parameters.MachineParameters)
      (A : Type) (la la' : list A),
    machine_parameters.hash (la ++ la')%list =
    machine_parameters.hash_concat (machine_parameters.hash la)
      (machine_parameters.hash la')
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
```

Note that we make use of the axiom of extensionality, which is well known to be compatible with Rocq's internal theory.
The axioms `hash_cap.*` correspond to the algebraic assumptions required for mutual attestation (Paper: line 885).

## 2. Verification effort

In the paper, we claim the verification effort is comprised of roughly 35,000 lines of code, and the FTLR case for `EInit` is roughly 2,000 lines of proofs.

To verify this claim, run the `count-lines` make target:

```sh
rocq@cerisier:~/cerisier$ make count-lines
```

This invokes `coqwc`, a command line utility that counts specification lines and proof lines.
A table should be printed to stdout that summarizes the sources per file.

Confirm that the sum of the lines of spec (last row, first column) and the lines of proof (last row, second column) roughly amount to 35,000 lines:

```
... [omitted] ...
   59      445       80 theories/case_studies/memory_readout/trusted_memory_readout_client_spec.v
   64      436       87 theories/case_studies/memory_readout/trusted_memory_readout_sensor_spec.v
  136      255       49 theories/case_studies/memory_readout/trusted_memory_readout_main_spec.v
  142      236       30 theories/case_studies/memory_readout/trusted_memory_readout_adequacy.v
  450       32      228 theories/case_studies/mutual_attestation/mutual_attestation_code.v
  142     1218      180 theories/case_studies/mutual_attestation/mutual_attestation_A_spec.v
   54      730      127 theories/case_studies/mutual_attestation/mutual_attestation_B_spec.v
  263      513       37 theories/case_studies/mutual_attestation/mutual_attestation_spec.v
  141      200       30 theories/case_studies/mutual_attestation/mutual_attestation_adequacy.v
   14        8        0 theories/assumptions.v
15051    21366     2798 total
```

and moreover, that the `theories/logrel/ftlr/EInit.v`'s proof lines column (second column after spec) is roughly 2,000 lines.

```
23     1871       84 theories/logrel/ftlr/EInit.v
```

## 3. Artifact faithful to the paper
In the rest of the README, we provide an explanation of the organisation of this artifact,
and we provide correspondence tables between the Rocq implementation and the paper.

# Organization

For completeness, we give an overview of the artifact's directory structure below, and couple definitions and theorems back to the paper.

All paths below are under the `theories/` repository.

## Organization of the repository

### Utils `utils/`
This folder contains a collection of additional Iris and stdpp utilitary lemmas.

### Operational Semantics `opsem/`
- `addr_reg.v`: Defines registers, the set of (finite) memory addresses and the set of (finite) otypes.
- `machine_base.v`: Contains the syntax (permissions, capability, instructions, ...) of the capability machine.
- `machine_parameters.v`: Defines a number of "settings" for the machine, that parameterize the whole development (e.g. the specific encoding scheme for instructions, etc.).
- `cap_lang.v`: Defines the operational semantics of the machine, and the embedding of the capability machine language into Iris 

### Program Logic `program_logic`
- `transiently.v`: Contains a definition of the transiently modality, a convenient modality to prove the program logic rules.
- `wp_opt.v`: Defines a custom WP, built on top of the transiently modality and the regular Iris WP.
- `logical_mapsto.v`: Defines the logical version layer to reason about revocation, inspired by Hur et al.
- `base_logic.v`: Defines the resources of the program logic: registers and memory points-to
  predicates, enclave resources, and their associated lemmas to manipulate them.
- `rules_base.v`: Contains a collection of lemma about WP to prove the rules of the program logic.
- `rules_fail.v`: Contains the Hoare triple rules for the fail cases.
- `rules/*.v`: Contains the Hoare triple rules for each instructions.
- `rules.v`: Imports all the Hoare triple rules for each instruction. These rules are separated into separate files (located in the rules/ folder).

### Logical Relation `logrel/`
- `seal_store.v`: Defines the ... for sealing predicates, inspired by Skorstensgaard et al.
- `logrel.v`: Defines the logical relation, the system invariant and the custom enclave contract.
- `ftlr/ftlr_base.v`: Contains the induction hypothesis of the proof of FTLR.
- `ftlr/interp_weakening.v`: Contains utility lemmas for FTLR. More precisely, it shows that the
value relation still holds when weakening the permissions of a capability.
- `ftlr/*.v`: Proof of FTLR for each instructions.
- `fundamental.v`: Contains the proof of the FTLR / universal contract.

### Proofmode `proofmode/`
This folder contains the setup for a Cerisier proofmode.
A description of the proofmode can be found in [proofmode.md](proofmode.md).

### Case Studies `case_studies/`
- `template_adequacy_attestation.v`: Contains the Cerisier adequacy, used as a template for the
  end-to-end theorems.
- `macros/*.v*`: Defines macros used in the examples, and their specifications. In particular:
  + `macros/assert.v`: Defines the `assert` macros. It is used in all our case studies.
  + `macros/hash_cap.v`: Defines a `hash` macros to hash capabilities. It is used in the mutual
    attestation case study.
- `soc/*.v`: Contains the Secure Outsourced Computation (SOC) case study.
- `mutual_attestation/*.v`: Contains the Mutual Attestation case study.
- `memory_readout/*.v`: Contains the Secure Memory Readout case study.

For each case study: 
- `*_code.v`: Contains the assembly code of the case study.
- `*_spec.v`: Contains the specification (and proof of the specification), phrased in terms of the program logic.
- `*_adequacy.v`: Contains the end-to-end specification of the case study, phrased in terms of the
  operational semantics.

## Link and differences between the paper and the mechanization

In this section, we explain how to compare the paper with our mechanization.

We provide a table that link the different sections of the paper with the related Rocq files:
| *technical section*                | *Rocq files*                                   |
|------------------------------------|------------------------------------------------|
| Operational semantics              | `opsem/*`                                      |
| Program Logic                      | `program_logic/*`                              |
| Logical Relation (Fig 8, §4.4)     | `logrel/logrel.v`                              |
| FTLR (§4.5, §4.6)                  | `logrel/ftlr/*`, `fundamental.v`               |
| Adequacy (§4.7)                    | `case_studies/template_adequacy_attestation.v` |
| Case Study - SOC (§5.1)            | `case_studies/soc/*.v`                         |
| Case Study - Mutual Attest (§5.2)  | `case_studies/mutual_attestation/*.v`          |
| Case Study - Sensor Readout (§5.3) | `case_studies/memory_readout/*.v`              |

We also provide a table that link the different figures and theorems of the paper with the related Rocq files:
| *figure*                       | *Rocq definition/theorem*                                | remark                                                                               |
|--------------------------------|----------------------------------------------------------|--------------------------------------------------------------------------------------|
| Figures 2 and 15               | `case_studies/soc/soc_code.v`                            |                                                                                      |
| Figures 3, 5, 9, 10, 12, 13,14 | `opsem/*`                                                |                                                                                      |
| Figure 7                       | `program_logic/rules/rules_Load:wp_load_success`         | The Rocq implementation uses points-to with logical versions, discussed in §3.4.     |
| Figure 8                       | `logrel/logrel.v:interp`                                 |                                                                                      |
| Theorem 3.1                    | ---                                                      | Theorem 3.1 comes from Cerise. Our version is Theorem 4.1.                           |
| Figure 11                      | `program_logic/rules/rules_IsUnique:wp_isunique_success` |                                                                                      |
| Figure 16                      | `program_logic/rules/rules_EInit`                        | The rules presented in the implementation is more general than the one in the paper. |
| Figure 17                      | `logrel/logrel.v:system_inv`                             |                                                                                      |
| Figure 18                      | `logrel/logrel.v:custom_enclave_contract`                |                                                                                      |
| Theorem 4.1                    | `logrel/fundamental:cerisier_universal_contract`         |                                                                                      |


Finally, some definitions have different names from the paper.

In the operational semantics:

| *name in paper* | *name in mechanization* |
|-----------------|-------------------------|
| Running         | Instr Executable        |
| Halted          | Instr Halted            |
| Failed          | Instr Failed            |
| cseal           | Seal                    |
| cunseal         | UnSeal                  |

For technical reasons (so that Iris considers a single instruction as an atomic step), 
the execution mode is interweaved with the "Instr Next" mode, which reduces to a value.
The Seq _ context can then return and continue to the next instruction. The full expression 
for an executing program is Seq (Instr Executable).

In the program logic:

| *name in paper*                | *name in mechanization* |
|--------------------------------|-------------------------|
| EC(ecn)                        | EC⤇ ecn                 |
| tidx $\mapsto_{E}^{\square}$ I | enclave_all tidx I      |
| tidx $\mapsto_{E}$ I           | enclave_cur tidx I      |
| DeInitialized(tidx)            | enclave_prev tidx       |

In the logical relation:

| *name in paper*                  | *name in mechanization* |
|----------------------------------|-------------------------|
| $$\mathcal{V}$$                  | interp                  |
| $$\mathcal{E}$$                  | interp_expression       |
| safe_to_deinit                   | safe_to_attest          |
| Global Invariant $$\mathcal{I}$$ | system_inv              |
