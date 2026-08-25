---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\*   Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N
Val  == Values \cup {Bottom}
Loc  == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

Message == [type : {"phase1", "phase2"},
            sender : Proc,
            v : Val,
            est : Val]   \* for phase1 messages, est = Bottom

\* ----------------------------------------------------------------------
\*   Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, recv

\* ----------------------------------------------------------------------
\*   Helper definitions
\* ----------------------------------------------------------------------
\* maximum of a non‑empty set of totally ordered values
MaxVal(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* number of elements in a set
Cardinality(S) == Cardinality(S)

\* messages of a given type received by a process
Phase1Rcv(p) == { m \in recv[p] : m.type = "phase1" }
Phase2Rcv(p) == { m \in recv[p] : m.type = "phase2" }

\* ----------------------------------------------------------------------
\*   Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "bcast1"]
  /\ prop \in [Proc -> Values]                \* any proposal per process
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est  = [p \in Proc |-> Bottom]
  /\ dec  = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\*   Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ loc[p] = "bcast1"
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>
  /\ sent' = sent \cup { [type |-> "phase1",
                         sender |-> p,
                         v |-> prop[p],
                         est |-> Bottom] }
  /\ loc' = [loc EXCEPT ![p] = "wait1"]

ReceivePhase1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.v]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

ComputeEst(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(Phase1Rcv(p)) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in Proc })]
  /\ loc' = [loc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "bcast2"
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>
  /\ sent' = sent \cup { [type |-> "phase2",
                         sender |-> p,
                         v |-> prop[p],
                         est |-> est[p]] }
  /\ loc' = [loc EXCEPT ![p] = "wait2"]

ReceivePhase2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.v]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent>>

DecideFromEst(p) ==
  /\ loc[p] = "wait2"
  /\ \E ev \in Values :
        /\ Cardinality({ m \in Phase2Rcv(p) : m.est = ev }) >= N - T
        /\ dec' = [dec EXCEPT ![p] = ev]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

MoveToChoosing(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality(Phase2Rcv(p)) = N
  /\ \A ev \in Values :
        Cardinality({ m \in Phase2Rcv(p) : m.est = ev }) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, sent, recv>>

ChooseAndDecide(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in { view[p][q] : q \in Proc } :
        /\ v # Bottom
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Crash(p) ==
  /\ loc[p] # "crashed"
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\*   Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ BroadcastPhase1(p)
    \/ BroadcastPhase2(p)
    \/ ComputeEst(p)
    \/ MoveToChoosing(p)
    \/ ChooseAndDecide(p)
    \/ Crash(p)
  \/ \E p \in Proc, m \in Message :
        \/ ReceivePhase1(p, m)
        \/ ReceivePhase2(p, m)
  \/ \E p \in Proc : DecideFromEst(p)

\* ----------------------------------------------------------------------
\*   Specification
\* ----------------------------------------------------------------------
Vars == <<loc, view, prop, est, dec, crashedCount, sent, recv>>
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\*   Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> Loc]
  /\ view \in [Proc -> [Proc -> Val]]
  /\ prop \in [Proc -> Values]
  /\ est  \in [Proc -> Val]
  /\ dec  \in [Proc -> Val]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\*   Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    /\ dec[p] # Bottom
    => /\ dec[p] \in Values
       /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\*   End of module
\* ----------------------------------------------------------------------
====