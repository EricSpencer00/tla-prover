---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ValueOrBottom == Values \cup {Bottom}

PcState == {"bcast1", "wait1", "bcast2", "wait2", "done",
            "crashed", "choosing"}

Msg == [type : {"p1","p2"},
        sender : 1..N,
        val : ValueOrBottom,
        est : ValueOrBottom]  \* est is used only for phase‑2 messages

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, prop, view, est, dec, crashedCount, msgs, recv

vars == << pc, prop, view, est, dec, crashedCount, msgs, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DistinctSenders(i, ph) == { m.sender : m \in recv[i] /\ m.type = ph }

ReceivedEstCount(i, v) ==
    Cardinality({ m \in recv[i] : m.type = "p2" /\ m.est = v })

MaxInSet(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in 1..N |-> "bcast1"]
    /\ prop \in [1..N -> Values]               \* each process proposes a value
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ est = [i \in 1..N |-> Bottom]
    /\ dec = [i \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ msgs = {}
    /\ recv = [i \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ LET m == [type |-> "p1", sender |-> i,
                val |-> prop[i], est |-> Bottom] IN
          msgs' = msgs \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Broadcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ LET m == [type |-> "p2", sender |-> i,
                val |-> prop[i], est |-> est[i]] IN
          msgs' = msgs \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive(i, m) ==
    /\ m \in msgs
    /\ m.sender # i
    /\ m \notin recv[i]                     \* not received before
    /\ /\ pc[i] = "wait1" => m.type = "p1"
       /\ pc[i] = "wait2" => m.type = "p2"
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, msgs >>

ComputeEst(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality(DistinctSenders(i, "p1")) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ est' = [est EXCEPT ![i] = 
               MaxInSet({ view[i][j] : j \in 1..N })]
    /\ UNCHANGED << prop, view, dec, crashedCount, msgs, recv >>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
          ReceivedEstCount(i, v) >= N - T
    /\ LET v == CHOOSE w \in Values :
            ReceivedEstCount(i, w) >= N - T IN
          /\ dec' = [dec EXCEPT ![i] = v]
          /\ pc'  = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, msgs, recv >>

MoveChoosing(i) ==
    /\ pc[i] = "wait2"
    /\ Cardinality(DistinctSenders(i, "p2")) = N
    /\ \A v \in Values : ReceivedEstCount(i, v) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, msgs, recv >>

Choose(i) ==
    /\ pc[i] = "choosing"
    /\ LET v == MaxInSet({ view[i][j] : j \in 1..N }) IN
          /\ v # Bottom
          /\ dec' = [dec EXCEPT ![i] = v]
          /\ pc'  = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, msgs, recv >>

Crash(i) ==
    /\ pc[i] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << prop, view, est, dec, msgs, recv >>

Next ==
    \/ \E i \in 1..N : Broadcast1(i)
    \/ \E i \in 1..N : Receive(i, m) \* existential over m is implicit in TLC
    \/ \E i \in 1..N : ComputeEst(i)
    \/ \E i \in 1..N : Broadcast2(i)
    \/ \E i \in 1..N : Receive(i, m) \* second phase receives are covered by same action
    \/ \E i \in 1..N : Decide(i)
    \/ \E i \in 1..N : MoveChoosing(i)
    \/ \E i \in 1..N : Choose(i)
    \/ \E i \in 1..N : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [1..N -> PcState]
    /\ prop \in [1..N -> Values]
    /\ view \in [1..N -> [1..N -> ValueOrBottom]]
    /\ est \in [1..N -> ValueOrBottom]
    /\ dec \in [1..N -> ValueOrBottom]
    /\ crashedCount \in Nat
    /\ msgs \subseteq Msg
    /\ recv \in [1..N -> SUBSET Msg]

Validity ==
    \A i \in 1..N :
        /\ dec[i] # Bottom
        => /\ dec[i] \in Values
           /\ \E j \in 1..N : prop[j] = dec[i]

Agreement ==
    \A i, j \in 1..N :
        /\ dec[i] # Bottom /\ dec[j] # Bottom
        => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====