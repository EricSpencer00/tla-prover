---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PC == {"bcast1", "wait1", "bcast2", "wait2",
       "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
MsgType == {"phase1", "phase2"}

Msg == [type : MsgType,
        sender : Proc,
        val : Values,
        est : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* [p \in Proc -> PC]
          view,             \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
          prop,             \* [p \in Proc -> Values]
          est,              \* [p \in Proc -> Values \cup {Bottom}]
          dec,              \* [p \in Proc -> Values \cup {Bottom}]
          crashed,          \* SUBSET Proc
          msgs,             \* SUBSET Msg
          recv2             \* [p \in Proc -> [Proc ->> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum of a (possibly empty) set of Values (assumes a total order on Values)
MaxVal(S) ==
   IF S = {} THEN Bottom
   ELSE CHOOSE v \in S : \A w \in S : v >= w

\* Number of distinct senders from which p has received a phase‑1 message
Recv1Count(p) ==
   Cardinality({ q \in Proc : view[p][q] # Bottom })

\* Number of distinct senders from which p has received a phase‑2 message
Recv2Senders(p) ==
   DOMAIN(recv2[p])

\* Number of distinct senders that sent estimated value v to p in phase‑2
EstCount(p, v) ==
   Cardinality({ s \in Proc :
                 s \in DOMAIN(recv2[p]) /\ recv2[p][s] = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
   /\ pc = [p \in Proc |-> "bcast1"]
   /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
   /\ prop \in [Proc -> Values]           \* each process proposes a value
   /\ est = [p \in Proc |-> Bottom]
   /\ dec = [p \in Proc |-> Bottom]
   /\ crashed = {}
   /\ msgs = {}
   /\ recv2 = [p \in Proc |-> [sender \in {} |-> Bottom]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
   /\ pc[p] = "bcast1"
   /\ LET m == [type |-> "phase1",
                sender |-> p,
                val |-> prop[p],
                est |-> Bottom] IN
          msgs' = msgs \cup {m}
   /\ pc' = [pc EXCEPT ![p] = "wait1"]
   /\ UNCHANGED <<view, prop, est, dec, crashed, recv2>>

ReceivePhase1(p, m) ==
   /\ m \in msgs
   /\ m.type = "phase1"
   /\ pc[p] = "wait1"
   /\ view' = [view EXCEPT ![p][m.sender] = m.val]
   /\ msgs' = msgs \ {m}
   /\ UNCHANGED <<pc, prop, est, dec, crashed, recv2>>

ComputeEst(p) ==
   /\ pc[p] = "wait1"
   /\ Recv1Count(p) >= N - T
   /\ LET max == MaxVal({ view[p][q] : q \in Proc }) IN
          /\ est' = [est EXCEPT ![p] = max]
          /\ pc' = [pc EXCEPT ![p] = "bcast2"]
   /\ UNCHANGED <<view, prop, dec, crashed, msgs, recv2>>

BroadcastPhase2(p) ==
   /\ pc[p] = "bcast2"
   /\ LET m == [type |-> "phase2",
                sender |-> p,
                val |-> prop[p],
                est |-> est[p]] IN
          msgs' = msgs \cup {m}
   /\ pc' = [pc EXCEPT ![p] = "wait2"]
   /\ UNCHANGED <<view, prop, est, dec, crashed, recv2>>

ReceivePhase2(p, m) ==
   /\ m \in msgs
   /\ m.type = "phase2"
   /\ pc[p] = "wait2"
   /\ recv2' = [recv2 EXCEPT ![p][m.sender] = m.est]
   /\ msgs' = msgs \ {m}
   /\ UNCHANGED <<pc, view, prop, est, dec, crashed>>

DecideByEst(p, v) ==
   /\ pc[p] = "wait2"
   /\ v \in Values
   /\ EstCount(p, v) >= N - T
   /\ dec' = [dec EXCEPT ![p] = v]
   /\ pc' = [pc EXCEPT ![p] = "done"]
   /\ UNCHANGED <<view, prop, est, crashed, msgs, recv2>>

MoveToChoosing(p) ==
   /\ pc[p] = "wait2"
   /\ DOMAIN(recv2[p]) = Proc
   /\ \A v \in Values : EstCount(p, v) < N - T
   /\ pc' = [pc EXCEPT ![p] = "choosing"]
   /\ UNCHANGED <<view, prop, est, dec, crashed, msgs, recv2>>

Choose(p) ==
   /\ pc[p] = "choosing"
   /\ LET candidates == { view[p][q] :
                           q \in Proc /\ view[p][q] # Bottom } IN
          /\ candidates # {}
   /\ LET v == CHOOSE x \in candidates : TRUE IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
   /\ UNCHANGED <<view, prop, est, crashed, msgs, recv2>>

Crash(p) ==
   /\ p \notin crashed
   /\ Cardinality(crashed) < F
   /\ crashed' = crashed \cup {p}
   /\ pc' = [pc EXCEPT ![p] = "crashed"]
   /\ UNCHANGED <<view, prop, est, dec, msgs, recv2>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
   \E p \in Proc :
        \/ BroadcastPhase1(p)
        \/ \E m \in Msg : ReceivePhase1(p, m)
        \/ ComputeEst(p)
        \/ BroadcastPhase2(p)
        \/ \E m \in Msg : ReceivePhase2(p, m)
        \/ \E v \in Values : DecideByEst(p, v)
        \/ MoveToChoosing(p)
        \/ Choose(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, view, prop, est, dec, crashed, msgs, recv2>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
   /\ pc \in [Proc -> PC]
   /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
   /\ prop \in [Proc -> Values]
   /\ est \in [Proc -> Values \cup {Bottom}]
   /\ dec \in [Proc -> Values \cup {Bottom}]
   /\ crashed \subseteq Proc
   /\ msgs \subseteq Msg
   /\ recv2 \in [Proc -> [Proc ->> Values \cup {Bottom}]]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
   \A p \in Proc :
      IF dec[p] # Bottom
      THEN \E q \in Proc : prop[q] = dec[p]
      ELSE TRUE

Agreement ==
   \A p, q \in Proc :
      (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Validity /\ Agreement

====