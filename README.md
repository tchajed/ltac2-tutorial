# Ltac2 tutorial

[![Build Status](https://travis-ci.com/tchajed/ltac2-tutorial.svg?branch=master)](https://travis-ci.com/tchajed/ltac2-tutorial)

A tutorial on Ltac2.

## What is Ltac2?

Ltac2 is a new tactic language for Coq, intended as a replacement for Ltac. The
goal is to provide a language with types and saner execution semantics. The
proof scripting mode is mostly compatible with basic Ltac1 scripts, but
automation (that is, user-defined Ltac1 tactics) is largely incompatible.

The aim is to be more productive but not dramatically change how tactics work.
As such the implementation closely follows the underlying Ltac1 implementation,
where tactics operate in a monad with access to the goals, hypotheses, and
exceptions. This is a less drastic change than other tactic languages like Mtac,
where the types of tactics also talk about how the manipulate the goal and the
Gallina type system, or Lean, where tactics are typed in Lean itself.

## Why a tutorial?

My ultimate goal for Ltac2 is to port the Iris Proof Mode to Ltac2 in order to
make useful and interesting improvements, both as a user for my own proofs and
for research.

This tutorial was a good way to learn and to teach Ltac2.

## What's in the tutorial?

- Ltac2 variables. We need variables to access Ltac2 bindings, Gallina names,
  and proof hypotheses, which are all different in Ltac2.
- Matching the goal and terms (Ltac1's `match ... with`). Backtracking.
- Creating new inductive types in Ltac2.
- Accessing the Ltac1 standard library, which includes a large body of OCaml
  tactics that are needed for any automation in Coq.
- The foreign-function interface to call Ltac1 from Ltac2 and vice-versa, for
  porting developments piecemeal.
- Exceptions in Ltac2, which are a significant new feature compared to Ltac1's
  failure levels and combinators (eg, `fail 1`, `match goal with`, and `try`).
- How to read the Ltac2 source code to learn more. You will need to read the
  source code.
