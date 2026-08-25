---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets and definitions
\* ----------------------------------------------------------------------
Proc == 1..N
States == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choosing"}

ValuesUbottom == Values \cup {Bottom}

\* Message definition
Message == [type : {"phase1", "phase2"},
            sender : Proc,
            value  : ValuesUbottom,
            est    : ValuesUbottom]   \* est is Bottom for phase1 messages

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc,               \* Proc -> States
          prop,              \* Proc -> Values
          view,              \* Proc -> [Proc -> ValuesUbottom]
          est,               \* Proc -> ValuesUbottom
          decision,          \* Proc -> ValuesUbottom
          crashedCount,      \* Nat
          sent,              \* SUBSET Message
          recv               \* [Proc -> SUBSET Message]

vars == << loc, prop, view, est, decision, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(p, mtype) ==
  { m.sender : m \in recv[p] /\ m.type = mtype }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "bcast1"]
  /\ prop \in [Proc -> Values]                \* each process proposes a value
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ loc[p] = "bcast1"
  /\ UNCHANGED << prop, view, est, decision, crashedCount, recv >>
  /\ let m == [type |-> "phase1",
               sender |-> p,
               value  |-> prop[p],
               est    |-> Bottom] 
     in sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]

ReceivePhase1(p) ==
  /\ loc[p] = "wait1"
  /\ \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \notin ReceivedFrom(p, "phase1")
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << loc, prop, est, decision, crashedCount, sent >>
  /\ UNCHANGED << view, recv >>  \* the existential picks one such m

Phase1ToPhase2(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(ReceivedFrom(p, "phase1")) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ loc' = [loc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << prop, view, decision, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
  /\ loc[p] = "bcast2"
  /\ UNCHANGED << prop, view, est, decision, crashedCount, recv >>
  /\ let m == [type |-> "phase2",
               sender |-> p,
               value  |-> prop[p],
               est    |-> est[p]]
     in sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]

ReceivePhase2(p) ==
  /\ loc[p] = "wait2"
  /\ \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \notin ReceivedFrom(p, "phase2")
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << loc, prop, view, est, decision, crashedCount, sent, view >>
  /\ UNCHANGED << recv >>   \* the existential picks one such m

DecideFromEst(p) ==
  /\ loc[p] = "wait2"
  /\ \E e \in ValuesUbottom :
        /\ Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e }) >= N - T
        /\ decision' = [decision EXCEPT ![p] = e]
        /\ loc' = [loc EXCEPT ![p] = "done"]
        /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality(ReceivedFrom(p, "phase2")) = N
  /\ \A e \in ValuesUbottom :
        Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e }) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << prop, view, est, decision, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
  /\ loc[p] = "choosing"
  /\ let candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } in
        candidates # {}
  /\ decision' = [decision EXCEPT ![p] = Max(candidates)]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ loc[p] # "crashed"
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << prop, view, est, decision, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
     \/ BroadcastPhase1(p)
     \/ ReceivePhase1(p)
     \/ Phase1ToPhase2(p)
     \/ BroadcastPhase2(p)
     \/ ReceivePhase2(p)
     \/ DecideFromEst(p)
     \/ MoveToChoosing(p)
     \/ ChooseAndDecide(p)
     \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> States]
  /\ prop \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> ValuesUbottom]]
  /\ est \in [Proc -> ValuesUbottom]
  /\ decision \in [Proc -> ValuesUbottom]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    decision[p] # Bottom => decision[p] \in { prop[q] : q \in Proc }

Agreement ==
  \A p,q \in Proc :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====