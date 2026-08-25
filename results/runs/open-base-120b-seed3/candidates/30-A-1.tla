---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    N,            \* number of processes
    T,            \* maximum tolerated faults
    F,            \* actual number of faults (≤ T)
    Values,       \* finite totally ordered set of proposal values
    Bottom        \* special bottom value not in Values

ASSUME 
    /\ N > 0
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ Bottom \notin Values
    /\ Values # {}

\* ----------------------------------------------------------------------
\* Process identifiers
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Control locations
PCValues == {"b1", "w1", "b2", "w2", "choose", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message definition
Msg == [type : {"p1","p2"},
        value : Values,
        sender : Proc,
        est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES 
    pc,          \* [i \in Proc -> PCValues]
    view,        \* [i \in Proc, j \in Proc -> Values \cup {Bottom}]
    prop,        \* [i \in Proc -> Values]      (initial proposal)
    est,         \* [i \in Proc -> Values \cup {Bottom}] (estimated value after phase 1)
    dec,         \* [i \in Proc -> Values \cup {Bottom}] (decision)
    crashed,     \* SUBSET Proc
    sent,        \* SUBSET Msg
    recv         \* [i \in Proc -> SUBSET Msg]   (messages already processed by i)

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
ReceivedFrom(i, s) == 
    \E m \in recv[i] : m.type = "p1" /\ m.sender = s

CountPhase2Est(i, v) == 
    Cardinality({ m \in recv[i] : m.type = "p2" /\ m.est = v })

AllPhase2Sent == 
    Cardinality({ m \in sent : m.type = "p2" }) = N

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ pc = [i \in Proc |-> "b1"]
    /\ view = [i \in Proc, j \in Proc |-> Bottom]
    /\ prop \in [Proc -> Values]            \* each process chooses a proposal nondeterministically
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Phase‑1 broadcast
BroadcastPhase1(i) ==
    /\ pc[i] = "b1"
    /\ LET m == [type |-> "p1", value |-> prop[i], sender |-> i, est |-> Bottom] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

\* ----------------------------------------------------------------------
\* Phase‑1 receive
ReceivePhase1(i, m) ==
    /\ pc[i] = "w1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ m \notin recv[i]                         \* not processed yet by i
    /\ LET s == m.sender IN
       view' = [view EXCEPT ![i][s] = m.value]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

\* ----------------------------------------------------------------------
\* Compute estimated value after receiving enough phase‑1 messages
ComputeEst(i) ==
    /\ pc[i] = "w1"
    /\ Cardinality({ s \in Proc : view[i][s] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![i] = 
                 Max({ view[i][s] : s \in Proc })]
    /\ pc' = [pc EXCEPT ![i] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Phase‑2 broadcast
BroadcastPhase2(i) ==
    /\ pc[i] = "b2"
    /\ LET m == [type |-> "p2",
                 value |-> prop[i],
                 sender |-> i,
                 est |-> est[i]] IN
       sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

\* ----------------------------------------------------------------------
\* Phase‑2 receive
ReceivePhase2(i, m) ==
    /\ pc[i] = "w2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ m \notin recv[i]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashed, sent >>

\* ----------------------------------------------------------------------
\* Decide when a value appears in at least N‑T phase‑2 messages
Decide(i, v) ==
    /\ pc[i] = "w2"
    /\ CountPhase2Est(i, v) >= N - T
    /\ dec' = [dec EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Move to choosing state when all phase‑2 messages have been seen
MoveToChoose(i) ==
    /\ pc[i] = "w2"
    /\ AllPhase2Sent
    /\ \A v \in Values : CountPhase2Est(i, v) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Deterministic choosing (pick the maximum value seen in the local view)
Choose(i) ==
    /\ pc[i] = "choose"
    /\ LET vals == { view[i][s] : s \in Proc /\ view[i][s] # Bottom } IN
       /\ vals # {}
    /\ LET v == Max(vals) IN
       dec' = [dec EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Crash action
Crash(i) ==
    /\ i \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \E i \in Proc :
        \/ BroadcastPhase1(i)
        \/ BroadcastPhase2(i)
        \/ ComputeEst(i)
        \/ MoveToChoose(i)
        \/ Choose(i)
        \/ Crash(i)
    \/
    \E i \in Proc, m \in Msg :
        \/ ReceivePhase1(i, m)
        \/ ReceivePhase2(i, m)
    \/
    \E i \in Proc, v \in Values :
        Decide(i, v)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ pc \in [Proc -> PCValues]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety invariants
Validity ==
    \A i \in Proc :
        dec[i] # Bottom => 
            /\ dec[i] \in Values
            /\ \E j \in Proc : prop[j] = dec[i]

Agreement ==
    \A i, j \in Proc :
        /\ dec[i] # Bottom /\ dec[j] # Bottom
        => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* (they are exported with the exact names)
\* Invariants: TypeOK, Validity, Agreement

====