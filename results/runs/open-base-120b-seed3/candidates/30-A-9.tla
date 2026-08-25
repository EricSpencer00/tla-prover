---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,               \* number of processes
    T,               \* tolerated faults
    F,               \* actual crash faults (upper bound)
    Values,          \* finite totally ordered set of proposal values
    Bottom           \* special bottom value not in Values

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Locs == {"broadcast1", "wait1", "broadcast2", "wait2",
         "done", "crashed", "choosing"}

Message == [phase : 1..2,
            value : Values,
            sender : 1..N,
            est    : Values \cup {Bottom}]   \* for phase 1, est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,        \* [i \in 1..N -> Locs]   current control location
    prop,       \* [i \in 1..N -> Values] proposed value
    view,       \* [i \in 1..N -> [j \in 1..N -> Values \cup {Bottom}]]
    est,        \* [i \in 1..N -> Values \cup {Bottom}]   estimated value after phase‑1
    dec,        \* [i \in 1..N -> Values \cup {Bottom}]   decision value
    crashed,    \* SUBSET 1..N                               set of crashed processes
    sent,       \* SUBSET Message                           all messages that have been sent
    recv        \* [i \in 1..N -> SUBSET Message]           messages received by each process

vars == <<loc, view, prop, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DistinctSenders(v) == { j \in 1..N : v[j] # Bottom }

MaxInView(v) ==
    LET S == { v[j] : j \in 1..N /\ v[j] # Bottom } IN
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

MessagesFromPhase(p) == { m \in sent : m.phase = p }

ReceivedFromPhase(p, i) == { m \in recv[i] : m.phase = p }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [i \in 1..N |-> "broadcast1"]
    /\ prop \in [1..N -> Values]                 \* each process proposes a value
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ est = [i \in 1..N |-> Bottom]
    /\ dec = [i \in 1..N |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(i) ==
    /\ loc[i] = "broadcast1"
    /\ UNCHANGED <<view, est, dec, crashed, recv>>
    /\ sent' = sent \cup { [phase |-> 1,
                           value |-> prop[i],
                           sender |-> i,
                           est |-> Bottom] }
    /\ loc' = [loc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED <<prop>>

ReceivePhase1(i, m) ==
    /\ m \in sent
    /\ m.phase = 1
    /\ i \notin crashed
    /\ loc[i] = "wait1"
    /\ m \notin recv[i]
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

ComputeEst(i) ==
    /\ loc[i] = "wait1"
    /\ Cardinality(DistinctSenders(view[i])) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxInView(view[i])]
    /\ loc' = [loc EXCEPT ![i] = "broadcast2"]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

BroadcastPhase2(i) ==
    /\ loc[i] = "broadcast2"
    /\ UNCHANGED <<view, est, dec, crashed, recv>>
    /\ sent' = sent \cup { [phase |-> 2,
                           value |-> prop[i],
                           sender |-> i,
                           est |-> est[i]] }
    /\ loc' = [loc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED <<prop>>

ReceivePhase2(i, m) ==
    /\ m \in sent
    /\ m.phase = 2
    /\ i \notin crashed
    /\ loc[i] = "wait2"
    /\ m \notin recv[i]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<loc, view, prop, est, dec, crashed, sent>>

DecideFromPhase2(i, v) ==
    /\ loc[i] = "wait2"
    /\ v \in Values
    /\ \E S \subseteq ReceivedFromPhase(2, i) :
          /\ Cardinality({ m \in S : m.est = v }) >= N - T
          /\ \A m \in S : m.est = v
    /\ dec' = [dec EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

MoveToChoosing(i) ==
    /\ loc[i] = "wait2"
    /\ \A v \in Values :
         Cardinality({ m \in ReceivedFromPhase(2, i) : m.est = v }) < N - T
    /\ Cardinality({ m \in ReceivedFromPhase(2, i) }) = N
    /\ loc' = [loc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

ChooseAndDecide(i) ==
    /\ loc[i] = "choosing"
    /\ \E v \in Values :
          /\ v \in { view[i][j] : j \in 1..N }
    /\ LET v == CHOOSE w \in Values :
               w \in { view[i][j] : j \in 1..N } IN
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(i) ==
    /\ i \notin crashed
    /\ Cardinality(crashed) < F
    /\ loc' = [loc EXCEPT ![i] = "crashed"]
    /\ crashed' = crashed \cup {i}
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N : BroadcastPhase1(i)
    \/ \E i \in 1..N, m \in Message : ReceivePhase1(i, m)
    \/ \E i \in 1..N : ComputeEst(i)
    \/ \E i \in 1..N : BroadcastPhase2(i)
    \/ \E i \in 1..N, m \in Message : ReceivePhase2(i, m)
    \/ \E i \in 1..N, v \in Values : DecideFromPhase2(i, v)
    \/ \E i \in 1..N : MoveToChoosing(i)
    \/ \E i \in 1..N : ChooseAndDecide(i)
    \/ \E i \in 1..N : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [1..N -> Locs]
    /\ prop \in [1..N -> Values]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ dec \in [1..N -> Values \cup {Bottom}]
    /\ crashed \subseteq 1..N
    /\ sent \subseteq Message
    /\ recv \in [1..N -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A i \in 1..N :
        /\ dec[i] # Bottom
        => /\ dec[i] \in Values
           /\ \E j \in 1..N : prop[j] = dec[i]

Agreement ==
    \A i, j \in 1..N :
        /\ (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* Fairness (weak fairness for all enabled actions)
\* ----------------------------------------------------------------------
\* For brevity we assume weak fairness externally; the following
\* declarations make the actions visible for the model checker.
\* (The actual WF/ SF operators are not required for invariant checking.)

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====