---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : Values,
            est    : Values]

Phase1Msg(p) == [type |-> "phase1", sender |-> p,
                value |-> prop[p], est |-> Bottom]

Phase2Msg(p) == [type |-> "phase2", sender |-> p,
                value |-> prop[p], est |-> est[p]]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, prop, view, est, decision, crashed, sent, recv

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]          \* each process proposes a value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

Phase1Received(p) == { m \in recv[p] : m.type = "phase1" }
Phase2Received(p) == { m \in recv[p] : m.type = "phase2" }

Senders(set) == { m.sender : m \in set }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ sent' = sent \cup { Phase1Msg(p) }
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, recv>>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED <<pc, prop, est, decision, crashed, sent>>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(Senders(Phase1Received(p))) >= N - T
    /\ est' = [est EXCEPT ![p] = Max( { prop[p] } \cup { m.value : m \in Phase1Received(p) } )]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<prop, view, decision, crashed, sent, recv>>

Broadcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ sent' = sent \cup { Phase2Msg(p) }
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, recv>>

Receive2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ UNCHANGED <<pc, prop, est, decision, crashed, sent>>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
         Cardinality({ m \in Phase2Received(p) : m.est = v }) >= N - T
    /\ LET v == CHOOSE v \in Values :
                Cardinality({ m \in Phase2Received(p) : m.est = v }) >= N - T
       IN  /\ decision' = [decision EXCEPT ![p] = v]
           /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality(Senders(Phase2Received(p))) = N
    /\ \A v \in Values :
         Cardinality({ m \in Phase2Received(p) : m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, sent, recv>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }
           v == IF candidates = {} THEN Bottom ELSE Max(candidates)
       IN  /\ decision' = [decision EXCEPT ![p] = v]
           /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

Crash(p) ==
    /\ pc[p] # "crashed"
    /\ Cardinality(crashed) < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<prop, view, est, decision, sent, recv>>

Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc, m \in Message : Receive1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc, m \in Message : Receive2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<pc, prop, view, est, decision, crashed, sent, recv>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
ControlLocs == {"bcast1","wait1","bcast2","wait2","done","crashed","choosing"}

TypeOK ==
    /\ pc \in [Proc -> ControlLocs]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ est \in [Proc -> Values]
    /\ decision \in [Proc -> Values]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in { prop[q] : q \in Proc }

Agreement ==
    \A p, q \in Proc :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Assumptions about constants
\* ----------------------------------------------------------------------
ASSUME /\ 0 < N
       /\ 2 * T < N
       /\ 0 <= F
       /\ F <= T
       /\ Bottom \notin Values

====