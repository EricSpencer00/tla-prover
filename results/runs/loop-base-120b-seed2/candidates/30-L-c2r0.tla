---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,          \* number of processes
    T,          \* tolerance bound
    F,          \* actual crash bound (≤ T)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special value not in Values, less than every value in Values

ASSUME /\ N > 0
       /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ Bottom \notin Values
       
\* ---------- Types ----------
PC == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Message ==
    [type : {"phase1", "phase2"},
     val  : Values,
     sender : 1..N,
     est  : Values \cup {Bottom}]

Proc == 1..N

\* ---------- Variables ----------
VARIABLES
    pc,          \* [i ∈ Proc -> PC]
    prop,        \* [i ∈ Proc -> Values]      proposed value of i
    view,        \* [i ∈ Proc -> [j ∈ Proc -> Values ∪ {Bottom}]]
    est,         \* [i ∈ Proc -> Values ∪ {Bottom}]
    dec,         \* [i ∈ Proc -> Values ∪ {Bottom}]
    crashed,     \* SUBSET Proc
    sent,        \* SUBSET Message
    recv         \* [i ∈ Proc -> SUBSET Message]

vars == << pc, prop, view, est, dec, crashed, sent, recv >>

\* ---------- Helper definitions ----------
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(i, phase) ==
    { m.sender : m \in recv[i] /\ m.type = phase }

Phase2EstCount(i, v) ==
    Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v })

AllPhase2Senders(i) ==
    { m.sender : m \in recv[i] /\ m.type = "phase2" }

\* ---------- Initial state ----------
Init ==
    /\ pc = [i \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

\* ---------- Actions ----------
BroadcastPhase1(i) ==
    /\ pc[i] = "bcast1"
    /\ LET m == [type |-> "phase1", val |-> prop[i], sender |-> i, est |-> Bottom] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

ReceivePhase1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

ComputeEst(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality(ReceivedFrom(i, "phase1")) >= N - T
    /\ est' = [est EXCEPT ![i] = Max({ view[i][j] : j \in Proc })]
    /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED << prop, view, dec, crashed, sent, recv >>

BroadcastPhase2(i) ==
    /\ pc[i] = "bcast2"
    /\ LET m == [type |-> "phase2", val |-> prop[i], sender |-> i, est |-> est[i]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

ReceivePhase2(i, m) ==
    /\ pc[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, view, est, dec, crashed, sent >>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
          Phase2EstCount(i, v) >= N - T
    /\ LET v == CHOOSE w \in Values : Phase2EstCount(i, w) >= N - T IN
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

Choose(i) ==
    /\ pc[i] = "wait2"
    /\ Cardinality(AllPhase2Senders(i)) = N
    /\ \A v \in Values : Phase2EstCount(i, v) < N - T
    /\ LET candidates == { view[i][j] : j \in Proc } \ {Bottom} IN
       /\ candidates # {}
    /\ dec' = [dec EXCEPT ![i] = CHOOSE x \in candidates : TRUE]  \* deterministic choice
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

Crash(i) ==
    /\ pc[i] \in {"bcast1", "wait1", "bcast2", "wait2", "choosing"}
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED << prop, view, est, dec, sent, recv >>

Next ==
    \E i \in Proc :
        \/ BroadcastPhase1(i)
        \/ \E m \in Message : ReceivePhase1(i, m)
        \/ ComputeEst(i)
        \/ BroadcastPhase2(i)
        \/ \E m \in Message : ReceivePhase2(i, m)
        \/ Decide(i)
        \/ Choose(i)
        \/ Crash(i)

Spec == Init /\ [][Next]_vars

\* ---------- Invariants ----------
TypeOK ==
    /\ pc \in [Proc -> PC]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

Validity ==
    \A i \in Proc :
        /\ dec[i] # Bottom
        => /\ dec[i] \in Values
           /\ \E j \in Proc : prop[j] = dec[i]

Agreement ==
    \A i, j \in Proc :
        /\ dec[i] # Bottom /\ dec[j] # Bottom
        => dec[i] = dec[j]

====