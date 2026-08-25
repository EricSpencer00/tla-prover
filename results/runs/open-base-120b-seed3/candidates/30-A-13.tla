---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and auxiliary definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

LocType == {"broadcast1", "wait1", "broadcast2", "wait2", "done", "crashed", "choosing"}

Message == [type : {"phase1", "phase2"},
            value: Values,
            sender: Proc,
            est   : (Values \cup {Bottom})]

MaxVal(S) ==
  CHOOSE v \in Values : \A w \in S : w <= v

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, decision, crashedCount, sent, recv

vars == << loc, view, prop, est, decision, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "broadcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* arbitrary proposal
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ LET m == [type |-> "phase1",
               value |-> prop[p],
               sender |-> p,
               est |-> Bottom] IN
        sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, prop, est, decision, crashedCount, sent >>

Phase1Ready(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({ s \in Proc : view[p][s] # Bottom }) >= N - T
  /\ LET vals == { view[p][s] : s \in Proc /\ view[p][s] # Bottom } IN
        est' = [est EXCEPT ![p] = MaxVal(vals)]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED << view, prop, decision, crashedCount, sent, recv >>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ LET m == [type |-> "phase2",
               value |-> prop[p],
               sender |-> p,
               est   |-> est[p]] IN
        sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, view, prop, est, decision, crashedCount, sent >>

DecisionByEst(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
        /\ Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

ChoosingReady(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({ m \in recv[p] : m.type = "phase2" }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, decision, crashedCount, sent, recv >>

Choose(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
        /\ \E q \in Proc : view[p][q] = v
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, decision, sent, recv >>

Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc, m \in sent : Receive1(p, m)
  \/ \E p \in Proc : Phase1Ready(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc, m \in sent : Receive2(p, m)
  \/ \E p \in Proc : DecisionByEst(p)
  \/ \E p \in Proc : ChoosingReady(p)
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
  /\ loc \in [Proc -> LocType]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ decision \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

Validity ==
  \A p \in Proc :
    decision[p] # Bottom =>
      /\ decision[p] \in Values
      /\ \E q \in Proc : prop[q] = decision[p]

Agreement ==
  \A p, q \in Proc :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

====