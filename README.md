# QWIRE — Refactoring and Infrastructure Strengthening

This repository contains a Coq implementation of the QWIRE quantum programming language, as described in the following papers by Jennifer Paykin, Robert Rand, Dong-Ho Lee, and Steve Zdancewic:

- **QWIRE: a core language for quantum circuits**
- **QWIRE Practice: Formal Verification of Quantum Circuits in Coq**
- **ReQWIRE: Reasoning about Reversible Quantum Circuits**
- **Phantom Types for Quantum Programs**

This version of QWIRE is compatible with **Coq 8.19** and depends on **QuantumLib 1.6.0**.

---

## Purpose of this Fork / Project Work

The goal of this project is **not to add new quantum algorithms or gates**, but to **strengthen and refactor QWIRE’s foundational infrastructure** so that:

- algebraic abstractions (notably monads) can be used *reliably* in proofs,
- law-based reasoning and automation behave uniformly,
- and the repository structure reflects the conceptual architecture of the system.

These changes are intended to make QWIRE **easier to understand, extend, and maintain**, especially for developers working on semantics or verification rather than example circuits.

---

## Summary of Changes

### 1. Strengthened Monadic Infrastructure (`Monad.v`)

**File modified**
- `Monad.v`

**What was changed**
- QWIRE already defined interfaces for `Functor`, `Applicative`, and `Monad`, but several **law instances were missing or incomplete**, especially for standard monads such as lists.
- This project completes the missing **law-level instances** (e.g., `Functor_Correct`, `Applicative_Correct`, `Monad_Correct`) for standard monads.

**Why this matters**
- Proofs and tactics that rely on monad laws (associativity, identity) now work **uniformly**, instead of silently failing or requiring ad hoc unfolding.
- Proof scripts become **less brittle**, since they rely on algebraic laws rather than concrete implementation details (e.g., list concatenation order).
- This supports scalable proof development, where effects and control flow are reasoned about abstractly.

This change does not alter the *behavior* of monads; it makes their algebraic properties explicit and usable.

---

### 2. Repository Refactoring to Reflect Architectural Layers

**What was changed**
- Files were reorganized into directories that mirror QWIRE’s conceptual structure:

Base/
Syntax/
Typing/
Semantics/
CompilationQASM/

**Why this matters**
- The original flat layout made it difficult to see how syntax, typing, semantics, and compilation depend on one another.
- The refactored layout makes the **verification workflow explicit**:
  - foundational abstractions live in `Base/`,
  - the circuit language in `Syntax/`,
  - typing rules in `Typing/`,
  - meaning in `Semantics/`,
  - and export tooling in `CompilationQASM/`.
- This reduces accidental dependencies (e.g., examples depending on semantic internals) and makes the system easier to navigate for new contributors.

This refactoring primarily improves **maintainability and clarity**, rather than adding new functionality.

---

## How to Build and Check the Project

### Prerequisites

Install QuantumLib 1.6.0:

opam pin coq-quantumlib 1.6.0 https://github.com/inQWIRE/QuantumLib.git

Ensure you are using **Coq 8.19**.

---

### Build the Core and Proofs

From the repository root:

make builds src/ only

make libraries make examples

make examples builds examples

make all builds everything (src + libraries + examples)

make MyFile.vo builds "input" file placed by the user at the root of the directory. 

Example: make MyAdder.vo

make cleanall cleans everything

make cleanuser cleans user files 

Successful completion indicates:

* the refactoring did not break dependencies,
* the strengthened monad law instances typecheck,
* and existing proofs continue to hold.

---

### Build the QASM Backend

make qasm

This checks that the QWIRE-to-QASM compilation pipeline still builds correctly after refactoring.

---

## How to Sanity-Check the Changes

There is no separate executable or runtime output. Correctness is established by **successful Coq compilation**.

In particular:

* Proofs or tactics that rely on monad-law-based rewriting (`simplify_monad`) should now work uniformly for standard monads that previously lacked completed law instances.
* The refactored directory structure makes it easier to trace how circuit definitions, typing lemmas, and semantic proofs depend on one another.

If all targets build successfully, the changes are functioning as intended.

---

## Original Project Structure (for Reference)

The original QWIRE files implement:

* monadic and algebraic preliminaries,
* the QWIRE circuit language (HOAS and de Bruijn),
* typing and denotational semantics,
* verified example circuits,
* and compilation to OpenQASM.

This project preserves all of that functionality while improving the underlying structure and proof infrastructure.

Original README: https://github.com/inQWIRE/QWIRE/blob/master/README.md