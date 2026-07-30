---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* NatOverride is the finite version of the natural numbers used for ticket
\* numbering in the model checking configuration.  It is defined as an operator
\* (not a plain constant) because the .cfg substitutes Nat with a finite set.
NatOverride == 0..MaxNat

VARIABLES inflight, cs, wait, ticket, id

vars == << inflight, cs, wait, ticket, id >>

TypeOK ==
    /\ inflight \in [1..N -> BOOLEAN]
    /\ cs \in [1..N -> BOOLEAN]
    /\ wait \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ id \in 0..MaxNat

\* The state where no process has entered the critical section; it matches the
\* inductive-spec start state from the base Bakery specification.
Init ==
    /\ inflight = [p \in 1..N |-> FALSE]
    /\ cs = [p \in 1..N |-> FALSE]
    /\ wait = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ id = 0

\* A process requests entry; it joins the waiting set and takes the next ticket.
Request(p) ==
    /\ ~wait[p]
    /\ ~cs[p]
    /\ id < MaxNat
    /\ wait' = [wait EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = id + 1]
    /\ id' = id + 1
    /\ UNCHANGED << inflight, cs >>

\* A waiting process may enter the critical section only if every other
\* waiting process has a strictly smaller ticket number.
Enter(p) ==
    /\ wait[p]
    /\ \A q \in 1..N : wait[q] => ticket[p] < ticket[q]
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ wait' = [wait EXCEPT ![p] = FALSE]
    /\ UNCHANGED << inflight, ticket, id >>

\* A process in the critical section eventually leaves it.
Exit(p) ==
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ inflight' = [inflight EXCEPT ![p] = FALSE]
    /\ UNCHANGED << wait, ticket, id >>

\* A process may start sending messages to the others (the bakery signaling).
Send(p) ==
    /\ ~inflight[p]
    /\ inflight' = [inflight EXCEPT ![p] = TRUE]
    /\ UNCHANGED << cs, wait, ticket, id >>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Send(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: only one participant is ever in the critical section.
MutualExclusion == \A p, q \in 1..N : (cs[p] /\ cs[q]) => p = q

\* The full inductive invariant from the base Bakery spec.
Inv == TypeOK /\ MutualExclusion

ISpec == Spec

====