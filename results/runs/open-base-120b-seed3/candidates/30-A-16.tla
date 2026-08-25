---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic assumptions
\* ----------------------------------------------------------------------
ASSUME 
    /\ N > 0
    /\ 2 * T < N
    /\ 0 <= F
    /\ F <= T
    /\ Bottom \\in Values = FALSE
    /\ Values # {}

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type   : {"phase1", "phase2"},
            sender : Proc,
            value  : Values,
            est    : Values \cup {Bottom}]  \* est = Bottom for phase1 messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* [p \in Proc -> {"b1","w1","b2","w2","choosing","done","crashed"}]
          prop,             \* [p \in Proc -> Values]
          view,             \* [p \in Proc -> [q \in Proc -> Values]]
          est,              \* [p \in Proc -> Values]
          dec,              \* [p \in Proc -> Values]
          crashed,          \* SUBSET Proc
          sent,             \* SUBSET Message
          recv               \* [p \in Proc -> SUBSET Message]

vars == << pc, prop, view, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxVal(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

Phase1Msgs(p) == { m \in recv[p] : m.type = "phase1" }
Phase2Msgs(p) == { m \in recv[p] : m.type = "phase2" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ prop \in [Proc -> Values]                \* each process chooses an initial proposal
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> Bottom] }
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin crashed
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

ReadyForPhase2(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality( Phase1Msgs(p) ) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ est' = [est EXCEPT ![p] = MaxVal( { view[p][q] : q \in Proc } )]
    /\ UNCHANGED << prop, view, dec, crashed, sent, recv >>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> est[p]] }
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin crashed
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, view, est, dec, crashed, sent >>

Decide(p, v) ==
    /\ pc[p] = "w2"
    /\ v \in Values
    /\ Cardinality( { m \in Phase2Msgs(p) : m.est = v } ) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality( { m \in Phase2Msgs(p) : TRUE } ) = N   \* received from all distinct senders
    /\ \A v \in Values : Cardinality( { m \in Phase2Msgs(p) : m.est = v } ) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << prop, view, est, dec, crashed, sent, recv >>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ let vals == { view[p][q] : q \in Proc } \* values seen in the view
       in dec' = [dec EXCEPT ![p] = MaxVal(vals)]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED << prop, view, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ BroadcastPhase1(p)
        \/ ReceivePhase1(p, m)   \* m quantified below
        \/ ReadyForPhase2(p)
        \/ BroadcastPhase2(p)
        \/ ReceivePhase2(p, m)
        \/ \E v \in Values : Decide(p, v)
        \/ MoveToChoosing(p)
        \/ ChooseAndDecide(p)
        \/ Crash(p)

\* The quantifications over messages are hidden inside the actions:
ReceivePhase1(p, m) == 
    /\ \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \notin crashed
        /\ m \notin recv[p]
        /\ (* body as defined above *)

ReceivePhase2(p, m) ==
    /\ \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \notin crashed
        /\ m \notin recv[p]
        /\ (* body as defined above *)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","choosing","done","crashed"}]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ est \in [Proc -> Values]
    /\ dec \in [Proc -> Values]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

Validity ==
    \A p \in Proc :
        (dec[p] # Bottom) => (\E q \in Proc : prop[q] = dec[p])

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====