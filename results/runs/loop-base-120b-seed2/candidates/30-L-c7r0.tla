---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

PhaseTypes == {"phase1", "phase2"}

Msg ==
  [type : PhaseTypes,
   sender : Proc,
   val   : Values,
   est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,          \* control location of each process
          view,        \* local view matrix: view[p][q] is p's view of q's value
          prop,        \* proposed value of each process
          est,         \* estimated value after phase 1
          dec,         \* decision value
          crashed,     \* set of crashed processes
          sent,        \* set of all messages that have been broadcast
          recv         \* messages received by each process

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NonBottomVals(p) == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

MaxNonBottom(p) ==
  IF NonBottomVals(p) = {} THEN Bottom
  ELSE
    CHOOSE v \in NonBottomVals(p) :
      \A w \in NonBottomVals(p) : w <= v

Phase1Msgs(p) == { m \in recv[p] : m.type = "phase1" }
Phase2Msgs(p) == { m \in recv[p] : m.type = "phase2" }

EstCount(p, v) == Cardinality({ m \in Phase2Msgs(p) : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [p \in Proc |-> Values]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "b1"
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>
  /\ let m == [type |-> "phase1", sender |-> p,
               val   |-> prop[p], est |-> Bottom] in
     sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w1"]

Receive1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m \notin recv[p]
  /\ UNCHANGED << view, prop, est, dec, crashed, sent >>
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ pc' = pc

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(Phase1Msgs(p)) >= N - T
  /\ UNCHANGED << prop, dec, crashed, sent, recv >>
  /\ est' = [est EXCEPT ![p] = MaxNonBottom(p)]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ view' = view

Broadcast2(p) ==
  /\ pc[p] = "b2"
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>
  /\ let m == [type |-> "phase2", sender |-> p,
               val   |-> prop[p], est |-> est[p]] in
     sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w2"]

Receive2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m \notin recv[p]
  /\ UNCHANGED << view, prop, est, dec, crashed, sent >>
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ pc' = pc

Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        EstCount(p, v) >= N - T
  /\ LET v == CHOOSE w \in Values : EstCount(p, w) >= N - T IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

Choose(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality(Phase2Msgs(p)) = N
  /\ \A v \in Values : EstCount(p, v) < N - T
  /\ NonBottomVals(p) # {}
  /\ LET v == CHOOSE w \in NonBottomVals(p) IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

Crash(p) ==
  /\ p \in Proc
  /\ pc[p] # "crashed"
  /\ pc[p] # "done"
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc, m \in Msg : Receive1(p, m)
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc, m \in Msg : Receive2(p, m)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
  /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values \cup {Bottom}]
  /\ dec \in [Proc -> Values \cup {Bottom}]
  /\ crashed \subseteq Proc
  /\ sent \subseteq Msg
  /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => dec[p] \in Values

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Assumptions on parameters
\* ----------------------------------------------------------------------
ASSUME ==
  /\ N > 0
  /\ 2 * T < N
  /\ 0 <= F
  /\ F <= T
  /\ Bottom \notin Values

====