# Resdet Lean verification

Machine-checked response agreement, duplicate suppression, and conditional
workflow-delivery liveness for an abstract Resdet protocol model. The proofs
are parameterized by replica, request, payload, and response types; there is
no fixed bound on replicas, requests, batches, or execution length.

## Run

The project uses Lean 4.24.0 and its bundled standard library, with no external
Lean packages. From this repository's root:

```sh
make fetch-lean    # one-time project-local toolchain installation
make check-lean    # compile proofs/tests and run the transitive axiom audit
```

To use an existing Lean 4.24.0 installation:

```sh
LEAN_BIN=/absolute/path/to/bin make check-lean
```

Warnings are errors. The audit permits only Lean's standard logical axioms
(`propext`, `Quot.sound`, and `Classical.choice`); unfinished proofs, added
axioms, and native-evaluation axioms fail the check. `lake build` alone does
not run this audit.

## Review

Start with the [reading guide](lean/README.md), then:

- [Dedup.lean](lean/Resdet/Dedup.lean): shared duplicate suppression and its guarantees.
- [Delivery.lean](lean/Resdet/Delivery.lean): shared delivery state and handler.
- [ResdetProtocol.lean](lean/Resdet/ResdetProtocol.lean): state and allowed Resdet actions.
- [DeliveryModel.lean](lean/Resdet/DeliveryModel.lean): delivery core and its inductive invariant.
- [Paper.lean](lean/Resdet/Paper.lean): theorem statements and liveness assumptions.
- [Proof contracts](lean/PROTOCOL.md) and [paper correspondence](lean/PAPER.md).

## Scope

Consensus is an abstract append-only log. A received request can proceed directly to leader dispatch.
Liveness assumes ingress,
handler/downstream progress, eventual stable leadership, consensus progress,
and learning/processing progress. The main failure-model interface is
crash-stop. The optional recovery action retains all state; it does not verify
the paper's volatile-state recovery behavior. There is no checked refinement
of the Go implementation or TLA+ specification, and no guarantee of exactly-once
external side effects.

This repository contains the Lean portion of the Resdet verification work,
including its regression examples and axiom audit.
