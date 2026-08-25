---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N
Loc  == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choose"}

MsgType == {"phase1", "phase2"}

Message == [type : MsgType,
            sender : Proc,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, received

vars == << loc, view, prop, est, dec, crashedCount, sent, received >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllSenders(vs) == { m.sender : m \in vs }

Phase1Msgs(p) == { m \in received[p] : m.type = "phase1" }
Phase2Msgs(p) == { m \in received[p] : m.type = "phase2" }

Count(vs) == Cardinality(vs)

MaxValue(vs) ==
  IF vs = {} THEN Bottom
  ELSE
    CHOOSE v \in vs :
      \A w \in vs : w <= v

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "bcast1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]            \* each process proposes a value
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ LET m == [type |-> "phase1", sender |-> p, value |-> prop[p], est |-> Bottom] IN
        /\ sent' = sent \cup {m}
        /\ loc' = [loc EXCEPT ![p] = "wait1"]
        /\ UNCHANGED << view, prop, est, dec, crashedCount, received >>

Receive1(p, m) ==
  /\ m \in sent
  /\ m.type = "phase1"
  /\ loc[p] = "wait1"
  /\ m.sender \notin AllSenders(received[p])
  /\ LET newRecv == received[p] \cup {m} IN
        /\ received' = [received EXCEPT ![p] = newRecv]
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

Phase1To2(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({ s \in Proc : s \in AllSenders(Phase1Msgs(p)) }) >= N - T
  /\ LET vals == { view[p][q] : q \in Proc } IN
        /\ est' = [est EXCEPT ![p] = MaxValue(vals)]
        /\ loc' = [loc EXCEPT ![p] = "bcast2"]
        /\ UNCHANGED << view, prop, dec, crashedCount, sent, received >>

Broadcast2(p) ==
  /\ loc[p] = "bcast2"
  /\ LET m == [type |-> "phase2",
               sender |-> p,
               value |-> prop[p],
               est   |-> est[p]] IN
        /\ sent' = sent \cup {m}
        /\ loc' = [loc EXCEPT ![p] = "wait2"]
        /\ UNCHANGED << view, prop, est, dec, crashedCount, received >>

Receive2(p, m) ==
  /\ m \in sent
  /\ m.type = "phase2"
  /\ loc[p] = "wait2"
  /\ m.sender \notin AllSenders(received[p])
  /\ LET newRecv == received[p] \cup {m} IN
        /\ received' = [received EXCEPT ![p] = newRecv]
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
        Cardinality({ m \in Phase2Msgs(p) : m.est = v }) >= N - T
  /\ LET v == CHOOSE v \in Values :
                Cardinality({ m \in Phase2Msgs(p) : m.est = v }) >= N - T IN
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, received >>

MoveToChoose(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality(AllSenders(Phase2Msgs(p))) = N
  /\ \A v \in Values :
        Cardinality({ m \in Phase2Msgs(p) : m.est = v }) < N - T
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
        /\ dec' = [dec EXCEPT ![p] = CHOOSE c \in candidates : TRUE]
        /\ loc' = [loc EXCEPT ![p] = "done"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, received >>

Crash(p) ==
  /\ loc[p] # "crashed"
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, received >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ Broadcast1(p)
    \/ \E m \in Message : Receive1(p, m)
    \/ Phase1To2(p)
    \/ Broadcast2(p)
    \/ \E m \in Message : Receive2(p, m)
    \/ Decide(p)
    \/ MoveToChoose(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> Loc]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ received \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    (dec[p] # Bottom) => (\E q \in Proc : prop[q] = dec[p])

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* List of invariants for the model checker
\* ----------------------------------------------------------------------
\* (the .cfg file will refer to these names)
\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====