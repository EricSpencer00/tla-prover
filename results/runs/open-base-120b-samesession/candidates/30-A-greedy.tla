---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N
PhaseType == {"phase1", "phase2"}
PCState == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : PhaseType,
            sender : Proc,
            value  : Values,
            est    : Values]   \* for phase1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, prop, view, est, dec, crashedCount, sent, recv

vars == << pc, prop, view, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxVal(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

ReceivedSenders(p) == { m.sender : m \in recv[p] }

CountEst(p, v) == Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Bcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ LET m == [type |-> "phase1",
                 sender |-> p,
                 value |-> prop[p],
                 est   |-> Bottom] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin ReceivedSenders(p)
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Phase1To2(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(ReceivedSenders(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << prop, view, dec, crashedCount, sent, recv >>

Bcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ LET m == [type |-> "phase2",
                 sender |-> p,
                 value |-> prop[p],
                 est   |-> est[p]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, recv >>

Receive2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin ReceivedSenders(p)
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, view, est, dec, crashedCount, sent >>

DecideFromEst(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          /\ CountEst(p, v) >= N - T
          /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality(ReceivedSenders(p)) = N
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << prop, view, est, dec, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values :
          /\ v # Bottom
          /\ \E q \in Proc : view[p][q] = v
          /\ dec' = [dec EXCEPT ![p] = v]
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
        \/ Bcast1(p)
        \/ \E m \in sent : Receive1(p, m)
        \/ Phase1To2(p)
        \/ Bcast2(p)
        \/ \E m \in sent : Receive2(p, m)
        \/ DecideFromEst(p)
        \/ MoveToChoosing(p)
        \/ ChooseAndDecide(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> PCState]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ est \in [Proc -> Values]
    /\ dec \in [Proc -> Values]
    /\ crashedCount \in Nat
    /\ crashedCount <= F
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET sent]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => 
            \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====