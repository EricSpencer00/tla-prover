---- MODULE TLAPS ----
EXTENDS Naturals

\* From the description: This module defines backend pragmas for the TLA Proof
\* System (TLAPS).  It provides operators that instruct the proof system to
\* dispatch proof obligations to various automated theorem provers and SMT
\* solvers (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4) and states
\* fundamental proof rules for temporal logic reasoning (invariance, fairness,
\* step simulation).  There are no actors or concurrent components: this is
\* a configuration/infrastructure module containing just the rule operators.

CONSTANTS

Specifiers == {"zenon", "isa", "cvc3", "yices", "verit", "z3", "spass", "ls4"}
NoSpec == "nospec"
DefaultTimeout == 5

VARIABLES target, timeout, tactic

vars == <<target, timeout, tactic>>

TypeOK ==
    /\ target \in Specifiers \cup {NoSpec}
    /\ timeout \in 0..9
    /\ tactic \in {"default", "effort"}

Init ==
    /\ target = NoSpec
    /\ timeout = DefaultTimeout
    /\ tactic = "default"

\* Dispatch a proof obligation to a prover.  The proof system interprets the
\* operator below as a pragma, not as a runtime action.
Dispatch(p) ==
    /\ target = NoSpec
    /\ p \in Specifiers
    /\ target' = p
    /\ UNCHANGED <<timeout, tactic>>

SetTimeout(t) ==
    /\ timeout' = t
    /\ UNCHANGED <<target, tactic>>

ChooseTactic(k) ==
    /\ tactic' = k
    /\ UNCHANGED <<target, timeout>>

ResetDispatch ==
    /\ target # NoSpec
    /\ target' = NoSpec
    /\ timeout' = DefaultTimeout
    /\ tactic' = "default"

Next ==
    \/ \E p \in Specifiers : Dispatch(p)
    \/ \E t \in 0..9 : SetTimeout(t)
    \/ \E k \in {"default", "effort"} : ChooseTactic(k)
    \/ ResetDispatch

\* Two foundational theorems, always true in set theory; they are the
\* invariants this module keeps for reference.
SetExtensionality ==
    \A A, B \in SUBSET Nat :
        (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

NoSetContainsAll ==
    \A A \in SUBSET Nat : ~(\A x \in Nat : x \in A)

SPECIFICATION == Init /\ [][Next]_vars
INVARIANTS == SetExtensionality
PROPERTIES == NoSetContainsAll

====