---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ T >= F
       /\ 2 * T < N

Locations == {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}

VARIABLES loc, view, prop, est, decision, crashed, sent, received
vars == <<loc, view, prop, est, decision, crashed, sent, received>>

TypeOK ==
  /\ loc \in [ 1 .. N -> Locations ]
  /\ view \in [ 1 .. N -> [ 1 .. N -> Values \cup { Bottom } ] ]
  /\ prop \in [ 1 .. N -> Values ]
  /\ est \in [ 1 .. N -> Values \cup { Bottom } ]
  /\ decision \in [ 1 .. N -> Values \cup { Bottom } ]
  /\ crashed \in Nat
  /\ sent \in SUBSET [ type : {"phase1", "phase2"}, val : Values, sender : 1 .. N, est : Values \cup { Bottom } ]
  /\ received \in [ 1 .. N -> SUBSET [ type : {"phase1", "phase2"}, val : Values, sender : 1 .. N, est : Values \cup { Bottom } ] ]

Init ==
  /\ loc = [ p \in 1 .. N |-> "bcast1" ]
  /\ view = [ p \in 1 .. N |-> [ q \in 1 .. N |-> Bottom ] ]
  /\ prop \in [ 1 .. N -> Values ]
  /\ est = [ p \in 1 .. N |-> Bottom ]
  /\ decision = [ p \in 1 .. N |-> Bottom ]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [ p \in 1 .. N |-> {} ]

MaxInView(p) ==
  LET values == { view[p][q] : q \in 1 .. N } \ { Bottom } IN
    IF values = {} THEN Bottom ELSE CHOOSE m \in values : \A x \in values : x <= m

Bcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ loc' = [ loc EXCEPT ![p] = "wait1" ]
  /\ sent' = sent \cup { [ type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom ] }
  /\ UNCHANGED << view, prop, est, decision, crashed, received >>

Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in received[p]
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [ view EXCEPT ![p][m.sender] = m.val ]
  /\ UNCHANGED << loc, prop, est, decision, crashed, sent, received >>

Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({ m \in received[p] : m.type = "phase1" }) >= N - T
  /\ est' = [ est EXCEPT ![p] = MaxInView(p) ]
  /\ loc' = [ loc EXCEPT ![p] = "bcast2" ]
  /\ UNCHANGED << view, prop, decision, crashed, sent, received >>

Bcast2(p) ==
  /\ loc[p] = "bcast2"
  /\ loc' = [ loc EXCEPT ![p] = "wait2" ]
  /\ sent' = sent \cup { [ type |-> "phase2", val |-> prop[p], sender |-> p, est |-> est[p] ] }
  /\ UNCHANGED << view, prop, est, decision, crashed, received >>

Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in received[p]
  /\ m.type = "phase2"
  /\ view[p][m.sender] = Bottom
  /\ est[p] = Bottom
  /\ view' = [ view EXCEPT ![p][m.sender] = m.est ]
  /\ UNCHANGED << loc, prop, est, decision, crashed, sent, received >>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({ m \in received[p] : m.type = "phase2" /\ m.est = est[p] }) >= N - T
  /\ decision' = [ decision EXCEPT ![p] = est[p] ]
  /\ loc' = [ loc EXCEPT ![p] = "done" ]
  /\ UNCHANGED << view, prop, est, crashed, sent, received >>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({ m \in received[p] : m.type = "phase2" }) = N
  /\ loc' = [ loc EXCEPT ![p] = "choosing" ]
  /\ UNCHANGED << view, prop, est, decision, crashed, sent, received >>

Select(p) ==
  /\ loc[p] = "choosing"
  /\ decision[p] = Bottom
  /\ \E v \in Values :
       /\ v \in { view[p][q] : q \in 1 .. N } \cup { prop[p] }
       /\ decision' = [ decision EXCEPT ![p] = v ]
  /\ loc' = [ loc EXCEPT ![p] = "done" ]
  /\ UNCHANGED << view, prop, est, crashed, sent, received >>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [ loc EXCEPT ![p] = "crashed" ]
  /\ crashed' = crashed + 1
  /\ UNCHANGED << view, prop, est, decision, sent, received >>

Next ==
  \/ \E p \in 1 .. N : Bcast1(p)
  \/ \E p \in 1 .. N, m \in sent : Receive1(p, m)
  \/ \E p \in 1 .. N : Prepare(p)
  \/ \E p \in 1 .. N : Bcast2(p)
  \/ \E p \in 1 .. N, m \in sent : Receive2(p, m)
  \/ \E p \in 1 .. N : Decide(p)
  \/ \E p \in 1 .. N : Choose(p)
  \/ \E p \in 1 .. N : Select(p)
  \/ \E p \in 1 .. N : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1 .. N : Bcast1(p))
        /\ WF_vars(\E p \in 1 .. N, m \in sent : Receive1(p, m))
        /\ WF_vars(\E p \in 1 .. N : Prepare(p))
        /\ WF_vars(\E p \in 1 .. N : Bcast2(p))
        /\ WF_vars(\E p \in 1 .. N, m \in sent : Receive2(p, m))
        /\ WF_vars(\E p \in 1 .. N : Decide(p))
        /\ WF_vars(\E p \in 1 .. N : Choose(p))
        /\ WF_vars(\E p \in 1 .. N : Select(p))

Validity == \A p \in 1 .. N : decision[p] # Bottom => (\E q \in 1 .. N : prop[q] = decision[p])

Agreement == \A p, q \in 1 .. N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1 .. N : loc[p] \in {"done", "crashed"})

MaxVal == CHOOSE m \in Values : \A v \in Values : v <= m

C1 == \E S \in SUBSET (1 .. N) : Cardinality(S) >= F + 1 /\ \A p \in S : prop[p] = MaxVal

ConditionalTermination == C1 ~> Termination

====