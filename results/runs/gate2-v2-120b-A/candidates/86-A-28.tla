---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLAPS_theory

(* 
  This module defines backend pragmas for the TLA Proof System (TLAPS),
  providing operators that instruct the proof system to dispatch proof
  obligations to various automated theorem provers and SMT solvers, and
  stating fundamental temporal logic proof rules.
*)

\* ----------------------------------------------------------------------
\* Backend pragma operators (no runtime effect, used only by TLAPS)
\* ----------------------------------------------------------------------
Zenon(e) == e \* Dispatch to Zenon prover
Isabelle(e) == e \* Dispatch to Isabelle prover
CVC3(e) == e \* Dispatch to CVC3 prover
Yices(e) == e \* Dispatch to Yices prover
VeriT(e) == e \* Dispatch to veriT prover
Z3(e) == e \* Dispatch to Z3 prover
SPASS(e) == e \* Dispatch to SPASS prover
LS4(e) == e \* Dispatch to LS4 temporal prover

\* Optional timeout and tactic annotations (no effect in model)
Timeout(e, t) == e
Tactic(e, s) == e

\* ----------------------------------------------------------------------
\* Fundamental temporal logic proof rules (names reserved)
\* ----------------------------------------------------------------------
\* Invariance rule: from an invariant I and a step relation S, infer that
\* I holds globally.
InvRule(I, S) == I /\ [S]_<<>> /\ []I

\* Well‑formedness rule: a specification must be a state machine.
WellFormed(Spec) == Spec

\* Strong fairness rule (SF): if an action A is enabled infinitely often,
\* then it occurs infinitely often.
SF(A) == []<>(<>A)

\* Weak fairness rule (WF): if an action A is continuously enabled,
\* then it eventually occurs.
WF(A) == []<>(A)

\* Step simulation rule: relates concrete steps to abstract steps.
StepSim(Conc, Abs) == \A s \in Conc : \E a \in Abs : a = s

\* ----------------------------------------------------------------------
\* Set extensionality theorem (axiom)
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A X, Y : (\A e : e \in X <=> e \in Y) => X = Y

\* No set contains every possible value (for the universe of discourse)
NoUniversalSet ==
  ~\E S : \A e : e \in S

\* ----------------------------------------------------------------------
\* Specification (no state variables, trivially true)
\* ----------------------------------------------------------------------
VARIABLES

\* The universe of discourse: all natural numbers (can be extended)
Universe == Nat

\* Initial predicate (trivially true)
Init == TRUE

\* Stutter step (no state change)
Next == [][TRUE]_<<>>

\* SPECIFICATION combines Init and Next
SPECIFICATION == Init /\ [] [Next]_<<>>

\* Theorems that must be available for model checking
THEOREM SetExtensionality
THEOREM NoUniversalSet

\* ----------------------------------------------------------------------
\* Declarations required by the .cfg (none)
\* ----------------------------------------------------------------------
\* (The .cfg does not require any additional identifiers.)

====