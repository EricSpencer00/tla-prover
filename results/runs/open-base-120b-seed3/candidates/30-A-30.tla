---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME /\ 0 <= F
       /\ F <= T
ASSUME N > 0
ASSUME Bottom \notin Values

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value : Values,
            est : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, decision, Crashed, Sent, recv

vars == << pc, view, prop, est, decision, Crashed, Sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ReceivedFrom(p) == { s \in Proc : view[p][s] # Bottom }

ReceivedPhase2From(p) == { s \in Proc :
                            \E m \in recv[p] : /\ m.type = "phase2"
                                              /\ m.sender = s }

EstimatesSeen(p) == { m.est : m \in recv[p] /\ m.type = "phase2" }

MaxInView(p) ==
  LET vals == { v \in Values : \E s \in Proc : view[p][s] = v } IN
  IF vals = {} THEN Bottom
  ELSE CHOOSE v \in vals : \A w \in vals : w <= v

MinInView(p) ==
  LET vals == { v \in Values : \E s \in Proc : view[p][s] = v } IN
  IF vals = {} THEN Bottom
  ELSE CHOOSE v \in vals : \A w \in vals : v <= w

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
/\ pc = [p \in Proc |-> "b1"]
/\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
/\ prop \in [Proc -> Values]            \* each process proposes a value
/\ est = [p \in Proc |-> Bottom]
/\ decision = [p \in Proc |-> Bottom]
/\ Crashed = {}
/\ Sent = {}
/\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "b1"
/\ LET m == [type |-> "phase1", sender |-> p, value |-> prop[p], est |-> Bottom] IN
   Sent' = Sent \cup {m}
/\ pc' = [pc EXCEPT ![p] = "w1"]
/\ UNCHANGED << view, prop, est, decision, Crashed, recv >>

ReceivePhase1(p, m) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "w1"
/\ m \in Sent
/\ m.type = "phase1"
/\ view' = [view EXCEPT ![p][m.sender] = m.value]
/\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
/\ UNCHANGED << pc, prop, est, decision, Crashed, Sent >>

Phase1ToPhase2(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "w1"
/\ Cardinality(ReceivedFrom(p)) >= N - T
/\ est' = [est EXCEPT ![p] = MaxInView(p)]
/\ pc' = [pc EXCEPT ![p] = "b2"]
/\ UNCHANGED << view, prop, decision, Crashed, Sent, recv >>

BroadcastPhase2(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "b2"
/\ LET m == [type |-> "phase2", sender |-> p, value |-> prop[p], est |-> est[p]] IN
   Sent' = Sent \cup {m}
/\ pc' = [pc EXCEPT ![p] = "w2"]
/\ UNCHANGED << view, prop, est, decision, Crashed, recv >>

ReceivePhase2(p, m) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "w2"
/\ m \in Sent
/\ m.type = "phase2"
/\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
/\ UNCHANGED << pc, view, prop, est, decision, Crashed, Sent >>

DecideFromEst(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "w2"
/\ \E v \in Values :
      Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
/\ LET v == CHOOSE w \in Values :
            Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = w }) >= N - T
   IN
   decision' = [decision EXCEPT ![p] = v]
/\ pc' = [pc EXCEPT ![p] = "done"]
/\ UNCHANGED << view, prop, est, Crashed, Sent, recv >>

MoveToChoose(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "w2"
/\ Cardinality(ReceivedPhase2From(p)) = N
/\ \A v \in Values :
      Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
/\ pc' = [pc EXCEPT ![p] = "choose"]
/\ UNCHANGED << view, prop, est, decision, Crashed, Sent, recv >>

ChooseAndDecide(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ pc[p] = "choose"
/\ decision' = [decision EXCEPT ![p] = MinInView(p)]
/\ pc' = [pc EXCEPT ![p] = "done"]
/\ UNCHANGED << view, prop, est, Crashed, Sent, recv >>

Crash(p) ==
/\ p \in Proc
/\ p \notin Crashed
/\ Cardinality(Crashed) < F
/\ Crashed' = Crashed \cup {p}
/\ pc' = [pc EXCEPT ![p] = "crashed"]
/\ UNCHANGED << view, prop, est, decision, Sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : BroadcastPhase1(p)
  \/ \E p \in Proc : \E m \in Sent : ReceivePhase1(p, m)
  \/ \E p \in Proc : Phase1ToPhase2(p)
  \/ \E p \in Proc : BroadcastPhase2(p)
  \/ \E p \in Proc : \E m \in Sent : ReceivePhase2(p, m)
  \/ \E p \in Proc : DecideFromEst(p)
  \/ \E p \in Proc : MoveToChoose(p)
  \/ \E p \in Proc : ChooseAndDecide(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choose"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ decision \in [Proc -> (Values \cup {Bottom})]
  /\ Crashed \subseteq Proc
  /\ Sent \subseteq Message
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

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====