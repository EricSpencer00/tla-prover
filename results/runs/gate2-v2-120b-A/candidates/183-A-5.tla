---- MODULE TLAPS ----
EXTENDS Naturals, TLC

(***************************************************************************)
(*  TLAPS Backend Pragmas and Temporal Logic Proof Rules                *)
(*                                                                       *)
(*  This module defines operators that act as configuration pragmas     *)
(*  for the TLA Proof System (TLAPS). These operators do not affect the   *)
(*  execution of the specification; they are only meant to be recognized  *)
(*  by the proof system. In addition, fundamental temporal‑logic proof   *)
(*  rules are provided so that their names are reserved and can be used   *)
(*  in later specifications without naming conflicts.                    *)
(***************************************************************************)

(*-----------------------------------------------------------------------*)
(*  Backend prover configuration operators                               *)
(*-----------------------------------------------------------------------*)

\* Invoke the Zenon prover with an optional timeout (in seconds).
Zenon(timeout) == TRUE

\* Invoke the Isabelle prover with a list of tactics (as a string).
Isabelle(tactics) == TRUE

\* Invoke the CVC3 prover.
CVC3 == TRUE

\* Invoke the Yices prover.
Yices == TRUE

\* Invoke the veriT prover.
VeriT == TRUE

\* Invoke the Z3 prover.
Z3 == TRUE

\* Invoke the SPASS prover.
SPASS == TRUE

\* Invoke the LS4 temporal logic prover.
LS4 == TRUE

(*-----------------------------------------------------------------------*)
(*  Temporal logic proof rule operators                                  *)
(*-----------------------------------------------------------------------*)

\* Invariance rule: if Inv is an invariant of a behavior, then Inv holds
\* in all reachable states.
InvRule(Inv) == ALWAYS Inv

\* Well‑formedness rule: ensures that the next‑state relation respects the
\* type (or structural) constraints specified by the predicate WF.
WellFormedRule(WF) == ALWAYS WF

\* Strong fairness rule for an action A.
StrongFairness(A) == \A s \in Nat : 
    (\E i \in Nat : 
        /\ s <= i
        /\ A(i)) => 
    (\A i \in Nat : s <= i => A(i))

\* Weak fairness rule for an action A.
WeakFairness(A) == \A s \in Nat : 
    (\E i \in Nat : 
        /\ s <= i
        /\ A(i)) => 
    (\E i \in Nat : s <= i /\ A(i))

\* Step‑simulation rule: if every step of Spec1 can be simulated by a step
\* of Spec2, then Spec1 is refined by Spec2.
StepSimRule(Spec1, Spec2) == 
    \A s, t : Spec1(s, t) => \E u : Spec2(s, u)

(*-----------------------------------------------------------------------*)
(*  State variables and initial condition (no specific state required)   *)
(*-----------------------------------------------------------------------*)

VARIABLES dummy

Init == dummy = 0

(*-----------------------------------------------------------------------*)
(*  Next‑state action (trivial, because the module only provides config) *)
(*-----------------------------------------------------------------------*)

Next == dummy' = dummy

(*-----------------------------------------------------------------------*)
(*  SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES as required      *)
(*-----------------------------------------------------------------------)

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INIT == Init

NEXT == Next

INVARIANTS == { InvRule(dummy = 0) }

PROPERTIES == 
    /\ setExtensionality
    /\ noUniversalSet

(*-----------------------------------------------------------------------*)
(*  Foundational theorems required by the description                    *)
(*-----------------------------------------------------------------------)

\* Set extensionality: two sets are equal iff they have the same elements.
setExtensionality == 
    \A A, B : (\A x : x \in A <=> x \in B) => A = B

\* No set contains every possible value.
noUniversalSet == 
    \A S : \E x : x \notin S

====