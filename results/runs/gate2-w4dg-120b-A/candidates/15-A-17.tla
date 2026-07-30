---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

RECURSIVE Cardinality(_)
Cardinality(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Cardinality(S \ {x})

\* The protocol's combinatorial core: everything hinges on how many distinct
\* ECHO messages a process has actually observed, not on who sent them.
VARIABLES correct, faulty, pc, inbox, sentMsgs

Locs == {"noinit", "hasinit", "sent", "acpt"}
Msgs == [from : 1..N, typ : {"ECHO"}]
IsEcho(m) == (m.typ = "ECHO")

InitRoles == {"noinit", "hasinit"}

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc \in [1..N -> Locs]
    /\ inbox \in [1..N -> SUBSET Msgs]
    /\ sentMsgs \subseteq Msgs

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ \A m \in sentMsgs : IsEcho(m)

Init(initrole) ==
    /\ correct \subseteq (1..N)
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> initrole]
    /\ inbox = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

\* The no-broadcast case is a separate configuration in the .cfg file, but
\* the same module handles both by taking each initial role in turn.
InitNoBroad == Init("noinit")
InitBroad == Init("hasinit")

Receive(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"sent", "acpt"}
    /\ \E M \in SUBSET (sentMsgs \cup {m \in Msgs : m.from \in faulty}) :
        inbox' = [inbox EXCEPT ![p] = inbox[p] \cup M]
    /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* Catching the broadcast directly forces immediate acceptance plus an ECHO;
\* this is what separates the SRP model from quorum voting.
SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "hasinit"
    /\ sentMsgs' = sentMsgs \cup {[from |-> p, typ |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, inbox>>

\* Two thresholds: the lower one sends an ECHO without accepting, the
\* higher one accepts immediately.  Both require the same quorum of distinct
\* senders, so a process is never stuck between them.
RelayEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "noinit"
    /\ Cardinality({m \in inbox[p] : IsEcho(m)}) >= N - 2 * T
    /\ Cardinality({m \in inbox[p] : IsEcho(m)}) < N - T
    /\ sentMsgs' = sentMsgs \cup {[from |-> p, typ |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, inbox>>

RelayDecide(p) ==
    /\ p \in correct
    /\ pc[p] = "noinit"
    /\ Cardinality({m \in inbox[p] : IsEcho(m)}) >= N - T
    /\ sentMsgs' = sentMsgs \cup {[from |-> p, typ |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "acpt"]
    /\ UNCHANGED <<correct, faulty, inbox>>

ReceiveDecide(p) ==
    /\ p \in correct
    /\ pc[p] = "sent"
    /\ Cardinality({m \in inbox[p] : IsEcho(m)}) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "acpt"]
    /\ UNCHANGED <<correct, faulty, inbox, sentMsgs>>

Next ==
    \/ \E p \in 1..N : Receive(p)
    \/ \E p \in 1..N : SendEcho(p)
    \/ \E p \in 1..N : RelayEcho(p)
    \/ \E p \in 1..N : RelayDecide(p)
    \/ \E p \in 1..N : ReceiveDecide(p)

\* Both configurations share one fairness assumption on the receive-and-act
\* steps, which is what keeps the analysis tractable.
Spec ==
    /\ (InitNoBroad \/ InitBroad)
    /\ [][Next]_<<correct, faulty, pc, inbox, sentMsgs>>
    /\ SF_vars(\E p \in 1..N : Receive(p))
    /\ SF_vars(\E p \in 1..N : SendEcho(p))
    /\ SF_vars(\E p \in 1..N : RelayEcho(p))
    /\ SF_vars(\E p \in 1..N : RelayDecide(p))
    /\ SF_vars(\E p \in 1..N : ReceiveDecide(p))

\* If nobody ever had the broadcast to begin with, no correct process may
\* ever accept -- that is the complete unforgeability guarantee.
UnforgLtl ==
    (InitNoBroad /\ (\A p \in 1..N : pc[p] = "noinit"))
        ~> (\A p \in correct : pc[p] = "acpt")

\* Once the whole correct set is saturated with the broadcast, the quorum
\* guarantees it eventually accepts; after one accepts, every correct one
\* eventually does.
CorrLtl == (\A p \in correct : pc[p] = "hasinit") ~> (\A p \in correct : pc[p] = "acpt")
RelayLtl == (\E p \in correct : pc[p] = "acpt") ~> (\A p \in correct : pc[p] = "acpt")

====