---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,               \* number of processes
    T,               \* tolerated faults
    F,               \* actual faults bound
    Values,          \* finite totally ordered set of proposed values
    Bottom           \* special bottom value, not in Values

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Loc == {"broadcast1", "wait1", "broadcast2", "wait2",
        "done", "crashed", "choosing"}

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : Values,
            est    : Values]  \* for phase1 messages, est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,    \* [i \in Proc -> Loc]
    view,   \* [i \in Proc, j \in Proc -> Values \cup {Bottom}]
    prop,   \* [i \in Proc -> Values]          (initial proposals)
    est,    \* [i \in Proc -> Values \cup {Bottom}]
    dec,    \* [i \in Proc -> Values \cup {Bottom}]
    crashed,\* subset of Proc
    sent,   \* set of Message
    recv    \* [i \in Proc -> SUBSET Message]

vars == <<loc, view, prop, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ViewVals(i) == { view[i][j] : j \in Proc }

Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE m \in S : \A x \in S : x <= m

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [i \in Proc |-> "broadcast1"]
    /\ prop \in [Proc -> Values]               \* arbitrary proposals
    /\ view = [i \in Proc, j \in Proc |-> Bottom]
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ loc[i] = "broadcast1"
    /\ loc' = [loc EXCEPT ![i] = "wait1"]
    /\ sent' = sent \cup {
          [type |-> "phase1",
           sender |-> i,
           value  |-> prop[i],
           est    |-> Bottom]
       }
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

Receive1(i, m) ==
    /\ loc[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin { mm.sender : mm \in recv[i] }   \* not yet received
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

Phase1To2(i) ==
    /\ loc[i] = "wait1"
    /\ Cardinality({ m \in recv[i] : m.type = "phase1" }) >= N - T
    /\ loc' = [loc EXCEPT ![i] = "broadcast2"]
    /\ est' = [est EXCEPT ![i] = Max(ViewVals(i))]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

Broadcast2(i) ==
    /\ loc[i] = "broadcast2"
    /\ loc' = [loc EXCEPT ![i] = "wait2"]
    /\ sent' = sent \cup {
          [type |-> "phase2",
           sender |-> i,
           value  |-> prop[i],
           est    |-> est[i]]
       }
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

Receive2(i, m) ==
    /\ loc[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin { mm.sender : mm \in recv[i] }
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ view' = [view EXCEPT ![i][m.sender] = m.est]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

DecideFromPhase2(i) ==
    /\ loc[i] = "wait2"
    /\ \E v \in Values :
          Cardinality({ m \in recv[i] :
                         m.type = "phase2" /\ m.est = v }) >= N - T
    /\ let v == CHOOSE w \in Values :
               Cardinality({ m \in recv[i] :
                              m.type = "phase2" /\ m.est = w }) >= N - T
       in
          /\ dec' = [dec EXCEPT ![i] = v]
          /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

MoveToChoosing(i) ==
    /\ loc[i] = "wait2"
    /\ Cardinality({ m \in recv[i] : m.type = "phase2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ loc' = [loc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

Choosing(i) ==
    /\ loc[i] = "choosing"
    /\ LET candidates == ViewVals(i) \ {Bottom} IN
          candidates # {}
    /\ let v == Max(candidates) in
          /\ dec' = [dec EXCEPT ![i] = v]
          /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(i) ==
    /\ i \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ loc' = [loc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Proc : Broadcast1(i)
    \/ \E i \in Proc, m \in Message : Receive1(i, m)
    \/ \E i \in Proc : Phase1To2(i)
    \/ \E i \in Proc : Broadcast2(i)
    \/ \E i \in Proc, m \in Message : Receive2(i, m)
    \/ \E i \in Proc : DecideFromPhase2(i)
    \/ \E i \in Proc : MoveToChoosing(i)
    \/ \E i \in Proc : Choosing(i)
    \/ \E i \in Proc : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
       /\ WF_vars(Broadcast1)
       /\ WF_vars(Receive1)
       /\ WF_vars(Phase1To2)
       /\ WF_vars(Broadcast2)
       /\ WF_vars(Receive2)
       /\ WF_vars(DecideFromPhase2)
       /\ WF_vars(MoveToChoosing)
       /\ WF_vars(Choosing)
       /\ WF_vars(Crash)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Loc]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ \A m \in sent :
          /\ m.type \in {"phase1","phase2"}
          /\ m.sender \in Proc
          /\ m.value \in Values
          /\ (m.type = "phase1" => m.est = Bottom)
          /\ (m.type = "phase2" => m.est \in Values)

Validity ==
    \A i \in Proc :
        IF dec[i] # Bottom
        THEN /\ dec[i] \in Values
             /\ \E j \in Proc : prop[j] = dec[i]
        ELSE TRUE

Agreement ==
    \A i, j \in Proc :
        (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
THEOREM SpecIsWellFormed == Spec

====