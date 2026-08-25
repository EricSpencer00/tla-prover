---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N
Phase1 == "p1"
Phase2 == "p2"

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"p1","p2"},
            val  : Values,
            sender: Proc,
            est  : Values]   \* for phase‑1 messages est = Bottom

MessageSet == { m \in Message :
                 (m.type = "p1" /\ m.est = Bottom) \/
                 (m.type = "p2") }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc,           \* process location
          view,          \* local view of proposals  (Proc -> [Proc->Values])
          prop,          \* proposed value (Proc -> Values)
          est,           \* estimated value after phase‑1 (Proc -> Values)
          dec,           \* decision value (Proc -> Values)
          crashedCount,  \* number of crashed processes
          sent,          \* set of messages that have been sent
          estRecv        \* estimated values received in phase‑2
          
vars == << loc, view, prop, est, dec, crashedCount, sent, estRecv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxInView(p) ==
  LET S == { view[p][q] : q \in Proc } \ { Bottom } IN
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]          \* each process proposes a value
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ estRecv = [p \in Proc |-> [q \in Proc |-> Bottom]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ loc[p] = "b1"
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ sent' = sent \cup {
        [type |-> "p1",
         val  |-> prop[p],
         sender |-> p,
         est  |-> Bottom]
      }
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, estRecv>>

Receive1(p, m) ==
  /\ loc[p] = "w1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, sent, estRecv>>

AfterPhase1(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({s \in Proc : view[p][s] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxInView(p)]
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, estRecv>>

Broadcast2(p) ==
  /\ loc[p] = "b2"
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ sent' = sent \cup {
        [type |-> "p2",
         val  |-> prop[p],
         sender |-> p,
         est  |-> est[p]]
      }
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, estRecv>>

Receive2(p, m) ==
  /\ loc[p] = "w2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ estRecv' = [estRecv EXCEPT ![p][m.sender] = m.est]
  /\ UNCHANGED <<loc, view, prop, est, dec, crashedCount, sent>>

Decide(p) ==
  /\ loc[p] = "w2"
  /\ \E v \in Values :
        /\ Cardinality({s \in Proc : estRecv[p][s] = v}) >= N - T
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, estRecv>>

MoveToChoosing(p) ==
  /\ loc[p] = "w2"
  /\ \A s \in Proc : estRecv[p][s] # Bottom      \* all N phase‑2 messages received
  /\ \A v \in Values :
        Cardinality({s \in Proc : estRecv[p][s] = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, sent, estRecv>>

Choose(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
        /\ \E s \in Proc : view[p][s] = v
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, estRecv>>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] # "crashed"
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, estRecv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc, m \in sent : Receive1(p, m)
  \/ \E p \in Proc : AfterPhase1(p)
  \/ \E p \in Proc : Broadcast2(p)
  \/ \E p \in Proc, m \in sent : Receive2(p, m)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars
    /\ WF_vars(Crash)               \* weak fairness for crashing
    /\ WF_vars(Broadcast1)          \* weak fairness for broadcasting phase‑1
    /\ WF_vars(Receive1)            \* weak fairness for receiving phase‑1
    /\ WF_vars(AfterPhase1)         \* weak fairness for phase‑1 transition
    /\ WF_vars(Broadcast2)          \* weak fairness for broadcasting phase‑2
    /\ WF_vars(Receive2)            \* weak fairness for receiving phase‑2
    /\ WF_vars(Decide)              \* weak fairness for decision
    /\ WF_vars(Choose)              \* weak fairness for choosing

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
  /\ view \in [Proc -> [Proc -> Values]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values]
  /\ dec \in [Proc -> Values]
  /\ crashedCount \in Nat
  /\ sent \subseteq MessageSet
  /\ estRecv \in [Proc -> [Proc -> Values]]
  /\ Bottom \notin Values

Validity ==
  \A p \in Proc :
    dec[p] # Bottom => dec[p] \in { prop[q] : q \in Proc }

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====