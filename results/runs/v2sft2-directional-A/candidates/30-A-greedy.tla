---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
VARIABLES
    loc,          \* control location of each process
    view,         \* N-by-N matrix of values known to each process
    est,          \* estimated value of each process
    dec,          \* decision value of each process
    crashed,      \* set of crashed processes
    sent,         \* set of messages that have been sent
    recv          \* set of messages that have been received by each process

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Locs == {"Bcast1", "Wait1", "Prepare", "Bcast2", "Wait2", "Done", "Crashed", "Choosing"}

MsgType == {"P1", "P2"}

Msg == [type: MsgType, sender: 1..N, value: Values \cup {Bottom}, est: Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [i \in 1..N |-> "Bcast1"]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ est = [i \in 1..N |-> Bottom]
    /\ dec = [i \in 1..N |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in 1..N |-> {}]
    /\ \A i \in 1..N: \E v \in Values: dec[i] = v -> FALSE   \* no decisions yet

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Phase1Msg(i, v) == [type |-> "P1", sender |-> i, value |-> v, est |-> Bottom]
Phase2Msg(i, v, e) == [type |-> "P2", sender |-> i, value |-> v, est |-> e]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ loc[i] = "Bcast1"
    /\ sent' = sent \cup {Phase1Msg(i, dec[i])}
    /\ loc' = [loc EXCEPT ![i] = "Wait1"]
    /\ UNCHANGED << view, est, dec, crashed, recv >>

Receive1(i, m) ==
    /\ loc[i] \in {"Wait1", "Prepare"}
    /\ m \in sent
    /\ m.type = "P1"
    /\ m.sender \in 1..N
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ UNCHANGED << loc, est, dec, crashed, sent, recv >>

ComputeEst(i) ==
    /\ loc[i] = "Wait1"
    /\ \E s \in 1..N: s \in {j \in 1..N : view[i][j] # Bottom}
    /\ \A j \in 1..N: j \in {j \in 1..N : view[i][j] # Bottom} => view[i][j] \in Values
    /\ est' = [est EXCEPT ![i] = Max({view[i][j] : j \in 1..N})]
    /\ loc' = [loc EXCEPT ![i] = "Bcast2"]
    /\ UNCHANGED << view, dec, crashed, sent, recv >>

Broadcast2(i) ==
    /\ loc[i] = "Bcast2"
    /\ sent' = sent \cup {Phase2Msg(i, dec[i], est[i])}
    /\ loc' = [loc EXCEPT ![i] = "Wait2"]
    /\ UNCHANGED << view, est, dec, crashed, recv >>

Receive2(i, m) ==
    /\ loc[i] \in {"Wait2", "Choosing"}
    /\ m \in sent
    /\ m.type = "P2"
    /\ m.sender \in 1..N
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << loc, view, est, dec, crashed, sent >>

Decide(i, v) ==
    /\ loc[i] = "Wait2"
    /\ \E s \in 1..N: s \in {j \in 1..N : recv[i][j].est = v}
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => recv[i][k].est = v
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ \E k \in 1..N: k \in {j \in 1..N : recv[i][j].est = v} => k \in 1..N
    /\ dec' = [dec EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = "Done"]
    /\ UNCHANGED << view, est, crashed, sent, recv >>

Choose(i) ==
    /\ loc[i] = "Wait2"
    /\ \A j \in 1..N: j \in recv[i] => recv[i][j].est # Bottom
    /\ \E v \in Values: v \in {view[i][j] : j \in 1..N}
    /\ dec' = [dec EXCEPT ![i] = CHOOSE v \in {view[i][j] : j \in 1..N} : TRUE]
    /\ loc' = [loc EXCEPT ![i] = "Choosing"]
    /\ UNCHANGED << view, est, crashed, sent, recv >>

Crash(i) ==
    /\ i \notin crashed
    /\ \E j \in 1..N: j \in crashed => FALSE   \* placeholder to enforce bound on crashes
    /\ crashed' = crashed \cup {i}
    /\ loc' = [loc EXCEPT ![i] = "Crashed"]
    /\ UNCHANGED << view, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N: Broadcast1(i)
    \/ \E i \in 1..N, m \in sent: Receive1(i, m)
    \/ \E i \in 1..N: ComputeEst(i)
    \/ \E i \in 1..N: Broadcast2(i)
    \/ \E i \in 1..N, m \in sent: Receive2(i, m)
    \/ \E i \in 1..N, v \in Values: Decide(i, v)
    \/ \E i \in 1..N: Choose(i)
    \/ \E i \in 1..N: Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [1..N -> Locs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ dec \in [1..N -> Values \cup {Bottom}]
    /\ crashed \subseteq 1..N
    /\ sent \subseteq {Phase1Msg(i, v) : i \in 1..N, v \in Values \cup {Bottom}}
    /\ sent \subseteq {Phase2Msg(i, v, e) : i \in 1..N, v \in Values \cup {Bottom}, e \in Values \cup {Bottom}}
    /\ recv \in [1..N -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A i \in 1..N : dec[i] # Bottom => dec[i] \in Values

Agreement ==
    \A i, j \in 1..N : dec[i] # Bottom /\ dec[j] # Bottom => dec[i] = dec[j]

====