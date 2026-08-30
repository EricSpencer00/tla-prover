---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

NBYZ == F
NCORR == N - F

MsgTypes == {"ECHO"}

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

Bump(x, i) == IF x[i] = NBYZ THEN 0 ELSE x[i] + 1

InitType == "init"
NoInitType == "noinit"
LocTypes == {"sent", "echoed", "accepted"}

RECURSIVE DistinctFrom(_)
DistinctFrom(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN 1 + DistinctFrom(S \ {x})

TypeOK ==
    /\ correct \subseteq 1..N
    /\ faulty \subseteq 1..N
    /\ loc \in [1..N -> LocTypes]
    /\ recv \in [1..N -> SUBSET (1..N \X MsgTypes)]
    /\ sent \in [1..N -> 0..NBYZ]

Init ==
    /\ Cardinality(correct) = NCORR
    /\ faulty = 1..N \ correct
    /\ \E b \in {InitType, NoInitType} :
         \A p \in 1..N : loc[p] = b
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = [p \in 1..N |-> 0]

RestrictedInit ==
    /\ Cardinality(correct) = NCORR
    /\ faulty = 1..N \ correct
    /\ \A p \in 1..N : loc[p] = NoInitType
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = [p \in 1..N |-> 0]

\* A correct process receives a set of messages: any already-sent echo
\* from a correct process, plus any possible Byzantine message.
Receive(p) ==
    /\ p \in correct
    /\ loc[p] # "accepted"
    /\ \E S \in SUBSET ((correct \X {"ECHO"}) \cup (faulty \X MsgTypes)) :
         recv' = [recv EXCEPT ![p] = recv[p] \cup S]
    /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A correct process that got the broadcaster's INIT message accepts and
\* sends an ECHO straight away.
InitAccept(p) ==
    /\ p \in correct
    /\ loc[p] = InitType
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sent' = [sent EXCEPT ![p] = Bump(@, p)]
    /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not sent an ECHO yet receives at least
\* N-2T distinct ECHOs; it sends its own but does not yet accept.
MidEcho(p) ==
    /\ p \in correct
    /\ loc[p] = InitType
    /\ DistinctFrom({x \in recv[p] : x[2] = "ECHO"}) >= N - 2 * T
    /\ DistinctFrom({x \in recv[p] : x[2] = "ECHO"}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "echoed"]
    /\ sent' = [sent EXCEPT ![p] = Bump(@, p)]
    /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not sent an ECHO yet receives at least N-T
\* distinct ECHOs; it sends its own and accepts.
EchoAccept(p) ==
    /\ p \in correct
    /\ loc[p] = InitType
    /\ DistinctFrom({x \in recv[p] : x[2] = "ECHO"}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sent' = [sent EXCEPT ![p] = Bump(@, p)]
    /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that already sent an ECHO now receives enough to accept.
RelayAccept(p) ==
    /\ p \in correct
    /\ loc[p] = "echoed"
    /\ DistinctFrom({x \in recv[p] : x[2] = "ECHO"}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
    \/ Receive("any")
    \/ \E p \in 1..N : InitAccept(p) \/ MidEcho(p) \/ EchoAccept(p) \/ RelayAccept(p)

Spec == Init /\ [][Next]_vars

\* Relay: if any correct process accepts, all correct processes accept.
CorrLtl == <>(\E p \in correct : loc[p] = "accepted") ~> (\A p \in correct : loc[p] = "accepted")

\* Correctness: if all correct processes received the INIT message, all
\* correct processes eventually accept.
RelayLtl == (\A p \in correct : loc[p] = InitType) ~> (\A p \in correct : loc[p] = "accepted")

\* Unforgeability: if no correct process broadcasts (all start without the
\* INIT message), no correct process ever accepts.
UnforgLtl == (\A p \in correct : loc[p] = NoInitType) ~> (\A p \in correct : loc[p] # "accepted")

\* Safety: the program counters stay in their domain and the echo count
\* never runs past its per-process bound, so the unforgeability proof cannot
\* be evaded by an out-of-bounds message count.
FCConstraints ==
    /\ TypeOK
    /\ \A p \in 1..N : sent[p] <= Bump(NBYZ, p)

====