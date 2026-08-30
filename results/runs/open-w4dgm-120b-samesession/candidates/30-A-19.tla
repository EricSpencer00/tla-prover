---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Processes == 1 .. N
MsgTypes == {"p1", "p2"}
Recipients(S) == {m.from : m \in S}

VARIABLES pc, view, prop, est, decision, crashed, sent, got

vars == <<pc, view, prop, est, decision, crashed, sent, got>>

RECURSIVE MaxVal(_, _)
MaxVal(f, S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \cup MaxVal(f, S \ {x})

\* A process may only move on from phase 2 once at least N-T processes agree
\* on the single estimated value it is going to adopt.
ClosedOnValue(p) == Cardinality({m \in got[p] : m.type = "p2" /\ m.val = est[p]}) >= N - T

TypeOK ==
    /\ pc \in [Processes -> {"broadcast1", "wait1", "prepare", "broadcast2",
                             "wait2", "done", "crashed", "choosing"}]
    /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
    /\ prop \in [Processes -> Values]
    /\ est \in [Processes -> Values \cup {Bottom}]
    /\ decision \in [Processes -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ sent \subseteq [type : MsgTypes, val : Values, from : Processes,
                       est : Values \cup {Bottom}]
    /\ got \in [Processes -> SUBSET [type : MsgTypes, val : Values, from : Processes,
                          est : Values \cup {Bottom}]]

Init ==
    /\ pc = [p \in Processes |-> "broadcast1"]
    /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
    /\ prop \in [Processes -> Values]
    /\ est = [p \in Processes |-> Bottom]
    /\ decision = [p \in Processes |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ got = [p \in Processes |-> {}]

Broadcast1(p) ==
    /\ pc[p] = "broadcast1"
    /\ sent' = sent \cup {[type |-> "p1", val |-> prop[p], from |-> p, est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, got>>

Receive1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ view[p][m.from] = Bottom
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ got' = [got EXCEPT ![p] = got[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashed, sent>>

\* The estimate is the maximum the process has learned from its peers.
Broadcast2(p) ==
    /\ pc[p] = "wait1"
    /\ Recipients(got[p]) \supseteq (1..N) \ {p}
    /\ est' = [est EXCEPT ![p] = MaxVal(view[p], 1..N)]
    /\ sent' = sent \cup {[type |-> "p2", val |-> prop[p], from |-> p, est |-> est[p]]}
    /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, decision, crashed, got>>

Receive2(p, m) ==
    /\ pc[p] \in {"broadcast2", "wait2"}
    /\ m \in sent
    /\ m.type = "p2"
    /\ view[p][m.from] = Bottom
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ got' = [got EXCEPT ![p] = got[p] \cup {m}]
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, est, decision, crashed, sent>>

Decide(p) ==
    /\ pc[p] = "wait2"
    /\ ClosedOnValue(p)
    /\ decision' = [decision EXCEPT ![p] = est[p]]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, got>>

Choose(p) ==
    /\ pc[p] = "wait2"
    /\ Recipients(got[p]) = 1..N
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, sent, got>>

ChooseValue(p) ==
    /\ pc[p] = "choosing"
    /\ decision' = [decision EXCEPT ![p] = MaxVal(view[p], 1..N)]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, got>>

Crash(p) ==
    /\ crashed < F
    /\ pc[p] \notin {"crashed", "done"}
    /\ crashed' = crashed + 1
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, est, decision, sent, got>>

Next ==
    \/ \E p \in Processes : Broadcast1(p) \/ Broadcast2(p) \/ Decide(p)
                          \/ Choose(p) \/ ChooseValue(p) \/ Crash(p)
    \/ \E p \in Processes, m \in sent : Receive1(p, m) \/ Receive2(p, m)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in Processes : Receive1(p))
    /\ WF_vars(\E p \in Processes : Receive2(p))
    /\ WF_vars(\E p \in Processes : Decide(p))
    /\ WF_vars(\E p \in Processes : Choose(p))
    /\ WF_vars(\E p \in Processes : ChooseValue(p))

\* Agreement is pairwise: no two processes may ever decide different values.
Agreement ==
    \A p, q \in Processes :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Validity ==
    \A p \in Processes : decision[p] # Bottom => \E q \in Processes : prop[q] = decision[p]

\* Every process either crashes silently or eventually decides.
Termination ==
    \A p \in Processes : (pc[p] # "crashed") ~> (pc[p] \in {"done", "crashed"})

\* Under the strong (but not always satisfied) Condition C1 the run always ends.
ConditionalTermination ==
    (\A p \in Processes : prop[p] = MaxVal(prop, 1..N)) => Termination

====