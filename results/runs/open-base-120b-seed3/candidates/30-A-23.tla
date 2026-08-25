---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"p1", "p2"},
            sender : Proc,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          prop,             \* proposed value of each process
          view,             \* N-by-N matrix of received values (bottom if unknown)
          est,              \* estimated value after phase 1
          decision,         \* decided value (Bottom if undecided)
          crashed,          \* set of crashed processes
          sent,             \* set of all messages ever sent
          recv               \* messages received by each process

vars == <<pc, prop, view, est, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : v >= w

ReceivedFrom(p, mtype) ==
    { m \in recv[p] : m.type = mtype }

ReceivedFromWithEst(p, v) ==
    { m \in recv[p] : m.type = "p2" /\ m.est = v }

DistinctSenders(p) ==
    { m.sender : m \in recv[p] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]                \* broadcast phase 1
    /\ prop \in [Proc -> Values]                 \* each process proposes a value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastP1(p) ==
    /\ pc[p] = "b1"
    /\ sent' = sent \cup { [type |-> "p1", sender |-> p,
                           value |-> prop[p], est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, recv>>

ReceiveP1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ m.sender \notin DistinctSenders(p)      \* ignore duplicates
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashed, sent>>

ReadyToP2(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(DistinctSenders(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED <<prop, view, decision, crashed, sent, recv>>

BroadcastP2(p) ==
    /\ pc[p] = "b2"
    /\ sent' = sent \cup { [type |-> "p2", sender |-> p,
                           value |-> prop[p], est |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, recv>>

ReceiveP2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ m.sender \notin DistinctSenders(p)      \* ignore duplicates
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, view, est, decision, crashed, sent>>

DecideFromEst(p, v) ==
    /\ pc[p] = "w2"
    /\ v \in Values
    /\ Cardinality(ReceivedFromWithEst(p, v)) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality(ReceivedFrom(p, "p2")) = N
    /\ \A v \in Values : Cardinality(ReceivedFromWithEst(p, v)) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, view, est, decision, crashed, sent, recv>>

Choose(p) ==
    /\ pc[p] = "choosing"
    /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       /\ vals # {}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in vals : TRUE]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, crashed, sent, recv>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<prop, view, est, decision, sent, recv>>

Next ==
    \/ \E p \in Proc : BroadcastP1(p)
    \/ \E p \in Proc, m \in sent : ReceiveP1(p, m)
    \/ \E p \in Proc : ReadyToP2(p)
    \/ \E p \in Proc : BroadcastP2(p)
    \/ \E p \in Proc, m \in sent : ReceiveP2(p, m)
    \/ \E p \in Proc, v \in Values : DecideFromEst(p, v)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

Validity ==
    \A p \in Proc :
        decision[p] # Bottom => 
            decision[p] \in Values /\ 
            \E q \in Proc : prop[q] = decision[p]

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* (named exactly as required by the .cfg)
\* Already defined above as Spec

\* INVARIANTS (named as required)
\* TypeOK, Validity, Agreement

====