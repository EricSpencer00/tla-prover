---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

PCVals == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* local view matrix: view[i][j] = value of j as seen by i
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          decision,         \* decision value (Bottom if not decided)
          crashedSet,       \* set of crashed processes
          sent,             \* set of messages that have been broadcast
          recv              \* messages received so far by each process

vars == << pc, view, prop, est, decision, crashedSet, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Phase1Received(i) == { m \in recv[i] : m.type = "phase1" }
Phase2Received(i) == { m \in recv[i] : m.type = "phase2" }

Senders( msgs ) == { m.sender : m \in msgs }

HasEnoughPhase1(i) ==
    Cardinality( Senders( Phase1Received(i) ) ) >= N - T

HasEnoughPhase2(i) ==
    \E v \in Values :
        Cardinality( { m \in Phase2Received(i) : m.est = v } ) >= N - T

AllPhase2Received(i) ==
    Cardinality( Senders( Phase2Received(i) ) ) = N

ComputeEst(i) ==
    LET vals == { view[i][j] : j \in Proc } \cup {Bottom} IN
    IF vals = {} THEN Bottom
    ELSE CHOOSE v \in vals : \A w \in vals : w <= v

ChooseFromView(i) ==
    CHOOSE v \in Values :
        \E j \in Proc : view[i][j] = v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "bcast1"]
    /\ prop \in [Proc -> Values]               \* each process proposes a value
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [i \in Proc |-> Bottom]
    /\ decision = [i \in Proc |-> Bottom]
    /\ crashedSet = {}
    /\ sent = {}
    /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ LET m == [type |-> "phase1",
                 sender |-> i,
                 value  |-> prop[i],
                 est    |-> Bottom] IN
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED << view, prop, est, decision, crashedSet, recv >>

Receive1(i,m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ pc[i] = "wait1"
    /\ m \notin recv[i]
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision, crashedSet, sent >>

Phase1Done(i) ==
    /\ pc[i] = "wait1"
    /\ HasEnoughPhase1(i)
    /\ est' = [est EXCEPT ![i] = ComputeEst(i)]
    /\ pc'  = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED << view, prop, decision, crashedSet, sent, recv >>

Broadcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ LET m == [type |-> "phase2",
                 sender |-> i,
                 value  |-> prop[i],
                 est    |-> est[i]] IN
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED << view, prop, est, decision, crashedSet, recv >>

Receive2(i,m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ pc[i] = "wait2"
    /\ m \notin recv[i]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, decision, crashedSet, sent >>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
          Cardinality( { m \in Phase2Received(i) : m.est = v } ) >= N - T
    /\ LET v == CHOOSE w \in Values :
                Cardinality( { m \in Phase2Received(i) : m.est = w } ) >= N - T
       IN
       /\ decision' = [decision EXCEPT ![i] = v]
       /\ pc'       = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashedSet, sent, recv >>

MoveChoosing(i) ==
    /\ pc[i] = "wait2"
    /\ AllPhase2Received(i)
    /\ ~HasEnoughPhase2(i)
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED << view, prop, est, decision, crashedSet, sent, recv >>

Choose(i) ==
    /\ pc[i] = "choosing"
    /\ LET v == ChooseFromView(i) IN
       /\ decision' = [decision EXCEPT ![i] = v]
       /\ pc'       = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashedSet, sent, recv >>

Crash(i) ==
    /\ i \notin crashedSet
    /\ Cardinality(crashedSet) < F
    /\ crashedSet' = crashedSet \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED << view, prop, est, decision, sent, recv >>

Next ==
    \/ \E i \in Proc : Broadcast1(i)
    \/ \E i \in Proc, m \in Message : Receive1(i,m)
    \/ \E i \in Proc : Phase1Done(i)
    \/ \E i \in Proc : Broadcast2(i)
    \/ \E i \in Proc, m \in Message : Receive2(i,m)
    \/ \E i \in Proc : Decide(i)
    \/ \E i \in Proc : MoveChoosing(i)
    \/ \E i \in Proc : Choose(i)
    \/ \E i \in Proc : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> PCVals]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ decision \in [Proc -> Values \cup {Bottom}]
    /\ crashedSet \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ Cardinality(crashedSet) = Cardinality({ i \in Proc : pc[i] = "crashed" })

Validity ==
    \A i \in Proc :
        decision[i] # Bottom =>
            decision[i] \in Values /\ \E j \in Proc : prop[j] = decision[i]

Agreement ==
    \A i, j \in Proc :
        /\ decision[i] # Bottom
        /\ decision[j] # Bottom
        => decision[i] = decision[j]

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* INVARIANTS
\* (listed in the .cfg file)
\* ----------------------------------------------------------------------
====