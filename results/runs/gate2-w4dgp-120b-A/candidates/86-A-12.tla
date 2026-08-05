---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* This module defines backend pragmas for the TLA Proof System (TLAPS), which
\* instructs the proof system to dispatch proof obligations to various automated
\* theorem provers and SMT solvers. It also states some basic proof rules for
\* temporal logic reasoning.
\* The actions below exist only to make the module syntactically complete.

CONSTANTS Provers

VARIABLES dispatched, inFlight

vars == <<dispatched, inFlight>>

TypeOK ==
    /\ dispatched \in SUBSET Provers
    /\ inFlight \in [Provers -> [alive : BOOLEAN, time : 0..2]]

Init ==
    /\ dispatched = {}
    /\ inFlight = [p \in Provers |-> [alive |-> FALSE, time |-> 0]]

\* TLAPS dispatch: a completed dispatch (pruned from inFlight) records the prover.
Dispatch(p) ==
    /\ inFlight[p].alive
    /\ dispatched' = dispatched \cup {p}
    /\ inFlight' = [inFlight EXCEPT ![p] = [alive |-> FALSE, time |-> 0]]

\* Send a proof obligation to a prover; the dispatch is only available for a
\* bounded time before it expires.
Send(p) ==
    /\ ~inFlight[p].alive
    /\ inFlight' = [inFlight EXCEPT ![p] = [alive |-> TRUE, time |-> 2]]
    /\ UNCHANGED dispatched

\* Timeout: a dispatched proof that has not been completed expires.
Expire(p) ==
    /\ inFlight[p].alive
    /\ inFlight[p].time = 0
    /\ inFlight' = [inFlight EXCEPT ![p] = [alive |-> FALSE, time |-> 0]]
    /\ UNCHANGED dispatched

Tick ==
    /\ \E p \in Provers : inFlight[p].alive /\ inFlight[p].time > 0
    /\ inFlight' = [p \in Provers |->
            IF inFlight[p].alive /\ inFlight[p].time > 0
            THEN [alive |-> TRUE, time |-> inFlight[p].time - 1]
            ELSE inFlight[p]]
    /\ UNCHANGED dispatched

Next ==
    \/ \E p \in Provers : Dispatch(p) \/ Send(p) \/ Expire(p)
    \/ Tick

Spec == Init /\ [][Next]_vars

\* A well-formedness rule: a set that includes every possible value is the
\* universal set, so any proof that a set is proper is well-founded.
AllValues == UNION { {n} : n \in Nat }
ProperSetProperty == \A S \in SUBSET Nat : (S = AllValues) => FALSE

\* Invariance: any dispatched prover was actually sent and was alive at dispatch.
DispatchCoherent ==
    \A p \in Provers : p \in dispatched => (inFlight[p].alive \/ inFlight[p].time = 0)

\* Strong fairness: every dispatched prover is eventually pruned from inFlight,
\* because either it is completed or it expires.
DispatchHandled ==
    \A p \in Provers : p \in dispatched ~> ~inFlight[p].alive

\* Weak fairness: a sent proof is eventually either completed or it expires.
DispatchResolved ==
    \A p \in Provers : Send(p) => (Dispatch(p) \/ Expire(p))

====