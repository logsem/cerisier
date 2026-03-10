# Cerisier: A Program Logic for Attestation
This repository contains the Rocq mechanization accompanying the submission 
"Cerisier: A Program Logic for Attestation".
It provides a model of a capability machine with feature for local attestation and TEE,
and principles to reason about the interaction of known, unknown, and attested code.

The repository depends on the submodule `machine_utils`.
After cloning Cerisier, you can load the submodule using
```
git submodule update --init
```

# Building the proofs

## Installing the dependencies

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
    # Install Coq 8.18.0 (skip if already installed)
    opam update
    opam install coq.8.18.0
    opam install coq-iris.4.1.0
```

### Troubleshooting

If the `opam switch` invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y .` (this will continue from where it failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem.

# Assumptions

The typeclass `MachineParameters` in `opsem/machine_parameters.v` contains the assumptions
on the machine, in particular:
- `encode` and `decode` functions for instructions, permissions and sealing permissions.
  Encoding is injective. Decoding is the inverse of encoding. (Assumptions from Cerise)
- `hash` and `hash_concat` functions. They are both injective. (Paper: lines 519-521)

The file `assumption.v` shows which axioms are required for each theorems.
The mutual attestation requires some additional algebraic assumptions on hash (Paper: lines 883-885)
Compiling `assumption.v` should output the following:

``` text
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

# Organization

TODO: is there a better way to following present the tables

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

| *figure*                       | *Rocq definition/theorem*                                | remark                                                |
|--------------------------------|----------------------------------------------------------|-------------------------------------------------------|
| Figures 2 and 15               | `case_studies/soc/soc_code.v`                            |                                                       |
| Figures 3, 5, 9, 10, 12, 13,14 | XXX `opsem/*`                                            |                                                       |
| Figure 7                       | `program_logic/rules/rules_Load:wp_load_success`         | The Rocq implementation also contains logical version |
| Figure 8                       | `logrel/logrel.v:interp`                                 |                                                       |
| Theorem 3.1                    | ---                                                      | Theorem 3.1 comes from Cerise                         |
| Figure 11                      | `program_logic/rules/rules_IsUnique:wp_isunique_success` |                                                       |
| Figure 16                      | `program_logic/rules/rules_EInit`                        | TODO: we should derive the exact rules                |
| Figure 17                      | `logrel/logrel.v:system_inv`                             |                                                       |
| Figure 18                      | `logrel/logrel.v:custom_enclave_contract`                |                                                       |
| Theorem 4.1                    | `logrel/fundamental:fundamental'`                        | TODO: the implement is different from the paper       |


# Differences with the paper

Some definitions have different names from the paper.  

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper* | *name in mechanization* |
|-----------------|-------------------------|
| Running         | Instr Executable        |
| Halted          | Instr Halted            |
| Failed          | Instr Failed            |

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
| I(M)                           | system_inv              |
