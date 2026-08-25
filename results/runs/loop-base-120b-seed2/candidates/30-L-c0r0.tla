---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N
ValueSet == Values \cup {Bottom}
Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : ValueSet,
            est    : ValueSet]

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : x >= y

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          prop,             \* proposed value of each process
          view,             \* N-by-N matrix of observed values
          est,              \* estimated value after phase 1
          dec,              \* decision value
          crashedCount,     \* number of crashed processes
          sent,             \* set of all sent messages
          recv              \* messages received by each process

vars == << pc, prop, view, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ LET m == [type |-> "phase1", sender |-> i, value |-> prop[i], est |-> Bottom] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin recv[i]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality({ m \in recv[i] : m.type = "phase1" }) >= N - T
    /\ est' = [est EXCEPT ![i] = Max({ view[i][j] : j \in Proc })]
    /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED << prop, view, dec, crashedCount, sent, recv >>

Broadcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ LET m == [type |-> "phase2", sender |-> i,
                 value |-> prop[i], est |-> est[i]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive2(i, m) ==
    /\ pc[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin recv[i]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in ValueSet :
          Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in ValueSet :
                Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = w }) >= N - T
       IN
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

Choose(i) ==
    /\ pc[i] = "wait2"
    /\ Cardinality({ m \in recv[i] : m.type = "phase2" }) = N
    /\ \A v \in ValueSet :
          Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ dec' = [dec EXCEPT ![i] = Max({ view[i][j] : j \in Proc })]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

Crash(i) ==
    /\ crashedCount < F
    /\ pc[i] # "crashed"
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << prop, view, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Proc : Broadcast1(i)
    \/ \E i \in Proc, m \in Message : Receive1(i, m)
    \/ \E i \in Proc : ComputeEst(i)
    \/ \E i \in Proc : Broadcast2(i)
    \/ \E i \in Proc, m \in Message : Receive2(i, m)
    \/ \E i \in Proc : Decide(i)
    \/ \E i \in Proc : Choose(i)
    \/ \E i \in Proc : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","done","crashed","choosing"}]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> ValueSet]]
    /\ est \in [Proc -> ValueSet]
    /\ dec \in [Proc -> ValueSet]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ \A m \in sent :
          (m.type = "phase1" => m.est = Bottom) /\
          (m.type = "phase2" => m.est \in ValueSet)

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A i \in Proc :
        (dec[i] # Bottom) => \E j \in Proc : prop[j] = dec[i]

Agreement ==
    \A i, j \in Proc :
        (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* Assumptions on constants
\* ----------------------------------------------------------------------
ASSUME
    /\ N > 0
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* Invariants list for the model checker
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Validity /\ Agreement

====