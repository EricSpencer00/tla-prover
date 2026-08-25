---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc  == 1..N
Val   == Values \cup {Bottom}
Msg   == 
        [type : {"phase1", "phase2"},
         sender : Proc,
         value  : Val,
         est    : Val]  \* for phase1 messages the field |est| is ignored

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashedCount, sent, recv

vars == <<pc, view, prop, est, dec, crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

Min(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : x <= y

Phase1Received(p) == { m \in recv[p] : m.type = "phase1" }
Phase2Received(p) == { m \in recv[p] : m.type = "phase2" }

SameEstCount(p, v) == Cardinality({ m \in Phase2Received(p) : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "bcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* each process proposes an arbitrary value in Values
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "bcast1"
  /\ LET m == [type |-> "phase1", sender |-> p, value |-> prop[p], est |-> Bottom] IN
       sent' = sent \/ {m}
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

Receive1(p, m) ==
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, est, dec, crashedCount, sent>>

Transition1(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality(Phase1Received(p)) >= N - T
  /\ LET maxv == Max({ view[p][q] : q \in Proc }) IN
       est' = [est EXCEPT ![p] = maxv]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, recv>>

Broadcast2(p) ==
  /\ pc[p] = "bcast2"
  /\ LET m == [type |-> "phase2", sender |-> p, value |-> prop[p], est |-> est[p]] IN
       sent' = sent \/ {m}
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

Receive2(p, m) ==
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, view, prop, est, dec, crashedCount, sent>>

Decide(p) ==
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        SameEstCount(p, v) >= N - T
  /\ LET d == CHOOSE v \in Values : SameEstCount(p, v) >= N - T IN
       dec' = [dec EXCEPT ![p] = d]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Choose(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality(Phase2Received(p)) = N
  /\ \A v \in Values : SameEstCount(p, v) < N - T
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       /\ candidates # {}
  /\ dec' = [dec EXCEPT ![p] = Min(candidates)]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Crash(p) ==
  /\ crashedCount < F
  /\ pc[p] # "crashed"
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ Broadcast1(p)
    \/ \E m \in Msg : Receive1(p, m)
    \/ Transition1(p)
    \/ Broadcast2(p)
    \/ \E m \in Msg : Receive2(p, m)
    \/ Decide(p)
    \/ Choose(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","choosing","done","crashed"}]
  /\ view \in [Proc -> [Proc -> Val]]
  /\ prop \in [Proc -> Val] /\ \A p \in Proc : prop[p] \in Values
  /\ est \in [Proc -> Val]
  /\ dec \in [Proc -> Val]
  /\ crashedCount \in Nat
  /\ sent \subseteq Msg
  /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

=============================================================================