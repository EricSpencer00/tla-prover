---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message == 
    [ typ : {"phase1", "phase2"},
      sender : Proc,
      val : Values,
      est : Values \cup {Bottom} ]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, recv

vars == << loc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Locs == {"broadcast1", "wait1", "broadcast2", "wait2",
         "choosing", "done", "crashed"}

ReceivedFrom(p) == { m.sender : m \in recv[p] }

ReceivedPhase1(p) == { m : m \in recv[p] /\ m.typ = "phase1" }

ReceivedPhase2(p) == { m : m \in recv[p] /\ m.typ = "phase2" }

ViewValues(p) == { view[p][s] : s \in Proc /\ view[p][s] # Bottom }

Phase2EstVals(p) == { m.est : m \in recv[p] /\ m.typ = "phase2" }

CountDistinct1(p) == Cardinality({ s \in Proc : view[p][s] # Bottom })

EnoughPhase1(p) == CountDistinct1(p) >= N - T

EnoughPhase2SameEst(p) == 
   \E v \in Values :
        Cardinality({ m \in recv[p] : m.typ = "phase2" /\ m.est = v }) >= N - T

AllPhase2FromAll(p) ==
    \A s \in Proc : \E m \in recv[p] : m.typ = "phase2" /\ m.sender = s

MaxInSet(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

MaxInView(p) == MaxInSet(ViewValues(p))

MaxEstInRecv(p) == MaxInSet(Phase2EstVals(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "broadcast1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ sent' = sent \cup { [typ |-> "phase1",
                           sender |-> p,
                           val |-> prop[p],
                           est |-> Bottom] }
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase1(p) ==
    /\ loc[p] = "wait1"
    /\ \E m \in sent :
          /\ m.typ = "phase1"
          /\ m \notin recv[p]
    /\ LET m == CHOOSE mm \in sent :
                /\ mm.typ = "phase1"
                /\ mm \notin recv[p] IN
       /\ view' = [view EXCEPT ![p][m.sender] = m.val]
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

Estimate(p) ==
    /\ loc[p] = "wait1"
    /\ EnoughPhase1(p)
    /\ est' = [est EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ sent' = sent \cup { [typ |-> "phase2",
                           sender |-> p,
                           val |-> prop[p],
                           est |-> est[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase2(p) ==
    /\ loc[p] = "wait2"
    /\ \E m \in sent :
          /\ m.typ = "phase2"
          /\ m \notin recv[p]
    /\ LET m == CHOOSE mm \in sent :
                /\ mm.typ = "phase2"
                /\ mm \notin recv[p] IN
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << loc, view, prop, est, dec, crashedCount, sent >>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ EnoughPhase2SameEst(p)
    /\ \E v \in Values :
          /\ Cardinality({ m \in recv[p] : m.typ = "phase2" /\ m.est = v }) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ \~EnoughPhase2SameEst(p)
    /\ AllPhase2FromAll(p)
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

Choose(p) ==
    /\ loc[p] = "choosing"
    /\ dec' = [dec EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
    /\ loc[p] # "crashed"
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>

Next ==
    \E p \in Proc :
        \/ Broadcast1(p)
        \/ ReceivePhase1(p)
        \/ Estimate(p)
        \/ Broadcast2(p)
        \/ ReceivePhase2(p)
        \/ Decide(p)
        \/ MoveToChoosing(p)
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
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => 
            /\ dec[p] \in Values
            /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

====