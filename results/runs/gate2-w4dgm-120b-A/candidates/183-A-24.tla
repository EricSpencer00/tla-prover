---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* Helper module from the standard proof library.  The temporal logic proof  *)
(* rules stated here (invariance, well-formedness, fairness) come from       *)
(* Lamport's "The Temporal Logic of Actions" and are included so their names  *)
(* are reserved and not reclaimed by a later module.                          *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

DispatchOps == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

Spec == "TLAPS specification"
Init == "TLAPS initial state"
Step == "TLAPS step"
Inv == "TLAPS invariants"
Thing == "TLAPS properties"

VARIABLES done, proofLog

vars == <<done, proofLog>>

TypeOK ==
    /\ done \subseteq DispatchOps
    /\ proofLog \subseteq [op : DispatchOps, sat : BOOLEAN]

Init ==
    /\ done = {}
    /\ proofLog = {}

Prove(op, sat) ==
    /\ op \notin done
    /\ done' = done \cup {op}
    /\ proofLog' = proofLog \cup {[op |-> op, sat |-> sat]}
    /\ UNCHANGED <<>>

\* Temporal-logic bookkeeping: an obligation stays active while its prover has
\* not yet answered, and the system never crashes mid-proof, so weak fairness
\* here is the only thing standing between a prover and its discharge.
Active(op) == op \notin done

Next ==
    \/ \E op \in DispatchOps, sat \in BOOLEAN : Prove(op, sat)
    \/ \E op \in DispatchOps : (Active(op) /\ UNCHANGED vars)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E op \in DispatchOps, sat \in BOOLEAN : Prove(op, sat))
    /\ WF_vars(\E op \in DispatchOps : Active(op))

\* Foundational theorems kept in the invariant slot for easy checking.
Extensionality ==
    \A A, B \in SUBSET DispatchOps :
        (\A x \in DispatchOps : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet ==
    \A x \in DispatchOps : x \notin DispatchOps

Invariants == {Extensionality, NoUniversalSet}
Properties == {Thing}
====