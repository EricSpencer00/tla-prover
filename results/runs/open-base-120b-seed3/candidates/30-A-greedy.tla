---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}
ControlSet == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choosing"}

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : Value,
            est    : Value]   \* for phase1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, prop, view, est, dec, crashedCount, sent, recv

vars == << pc, prop, view, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* nondet. proposal
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           value  |-> prop[p],
                           est    |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ m \in sent : m.type = "phase1" /\ m.sender \in recv[p] }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << prop, view, dec, crashedCount, sent, recv >>

Broadcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> p,
                           value  |-> prop[p],
                           est    |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E e \in Values :
          Cardinality({ m \in sent :
                         m.type = "phase2" /\ m.sender \in recv[p] /\ m.est = e }) >= N - T
    /\ LET e == CHOOSE v \in Values :
                Cardinality({ m \in sent :
                               m.type = "phase2" /\ m.sender \in recv[p] /\ m.est = v }) >= N - T
       IN  /\ dec' = [dec EXCEPT ![p] = e]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ m \in sent : m.type = "phase2" /\ m.sender \in recv[p] }) = N
    /\ \A e \in Values :
          Cardinality({ m \in sent :
                         m.type = "phase2" /\ m.sender \in recv[p] /\ m.est = e }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, sent, recv >>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       \E v \in vals :
          dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << prop, view, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Broadcast1(p)
        \/ \E m \in sent : Receive1(p, m)
        \/ ComputeEst(p)
        \/ Broadcast2(p)
        \/ \E m \in sent : Receive2(p, m)
        \/ Decide(p)
        \/ MoveToChoosing(p)
        \/ Choose(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> ControlSet]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====