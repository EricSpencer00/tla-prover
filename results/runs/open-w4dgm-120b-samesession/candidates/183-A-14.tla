---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas invoking the automated theorem provers/SMT solvers the
\* TLA+ proof manager knows about.  Proof rules for temporal logic follow
\* the naming convention of Lamport's paper "The Temporal Logic of Actions":
\* Invariance, WellFormed, StrongFairness, WeakFairness, and SimStep.
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4, NIL

\* BASE unlocks the primitive action set of the system (doing nothing here).
Base == TRUE

\* Backend pragmas: tell the proof manager which solver to invoke for a goal.
PragmaZenon == Zenon
PragmaIsabelle == Isabelle
PragmaCVC3 == CVC3
PragmaYices == Yices
PragmaVeriT == VeriT
PragmaZ3 == Z3
PragmaSpass == Spass
PragmaLS4 == LS4

\* Temporal-logic proof rules, named exactly as in Lamport's TLA+ paper.
Invariance == NIL
WellFormed == NIL
StrongFairness == NIL
WeakFairness == NIL
SimStep == NIL

\* Foundational theorems the library reserves (not proved here).
Extensionality == NIL
UnivNotCovering == NIL

Specification == [Base |-> Base,
                  PragmaZenon |-> PragmaZenon,
                  PragmaIsabelle |-> PragmaIsabelle,
                  PragmaCVC3 |-> PragmaCVC3,
                  PragmaYices |-> PragmaYices,
                  PragmaVeriT |-> PragmaVeriT,
                  PragmaZ3 |-> PragmaZ3,
                  PragmaSpass |-> PragmaSpass,
                  PragmaLS4 |-> PragmaLS4,
                  Invariance |-> Invariance,
                  WellFormed |-> WellFormed,
                  StrongFairness |-> StrongFairness,
                  WeakFairness |-> WeakFairness,
                  SimStep |-> SimStep,
                  Extensionality |-> Extensionality,
                  UnivNotCovering |-> UnivNotCovering]

Init == Specification

Next == Specification

INVARIANTS == Extensionality

Properties == UnivNotCovering

vars == Specification

Spec == Init /\ [][Next]_vars
====