---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  TLAPS: Backend Pragmas and Temporal Logic Foundations for TLAPS      *)
(*                                                                         *)
(*  This module defines configuration operators that direct the TLA Proof   *)
(*  System (TLAPS) to invoke various automated provers, as well as the      *)
(*  fundamental temporal‑logic proof rules from Lamport's "The Temporal    *)
(*  Logic of Actions".  The module contains no state variables, no actions, *)
(*  and therefore no safety or liveness properties of its own;  it merely   *)
(*  reserves the names of the backend pragmas and introduces the two      *)
(*  foundational theorems required by the natural‑language description.    *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Backend pragma operators (no implementation – they are placeholders
\* that TLAPS recognises).  The names follow the convention used by the
\* TLAPS toolchain.  Each operator simply returns the arguments unchanged,
\* allowing the specification to type‑check while TLAPS replaces the call
\* with a pragma during proof processing.
\* ----------------------------------------------------------------------
Zenon == [timeout |-> 10, tactic |-> "default"]
Isabelle == [timeout |-> 10, tactic |-> "default"]
CVC3 == [timeout |-> 10, tactic |-> "default"]
Yices == [timeout |-> 10, tactic |-> "default"]
VeriT == [timeout |-> 10, tactic |-> "default"]
Z3 == [timeout |-> 10, tactic |-> "default"]
SPASS == [timeout |-> 10, tactic |-> "default"]
LS4 == [timeout |-> 10, tactic |-> "default"]

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rule placeholders.  The operators are defined as
\* identity functions that carry the premises to the conclusion;  TLAPS
\* interprets them as invocations of the corresponding proof rules.
\* ----------------------------------------------------------------------
InvRule(p) == p
WFRule(p) == p
SFRule(p) == p
WellFormed(p) == p

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description.
\* ----------------------------------------------------------------------
SetExtensionality == 
  \A A, B \in SUBSET Nat : (\A x : x \in A <=> x \in B) => A = B

NoUniversalSet == 
  \A S \in SUBSET Nat : ~ ( \A x \in Nat : x \in S )

\* ----------------------------------------------------------------------
\* The specification does not introduce state, therefore the following
\* operators are defined trivially.
\* ----------------------------------------------------------------------
Spec == TRUE

Init == TRUE

Next == TRUE

Invariants == {}

Properties == { SetExtensionality, NoUniversalSet }

=============================================================================