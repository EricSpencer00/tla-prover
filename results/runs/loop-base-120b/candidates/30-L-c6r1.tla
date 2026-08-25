---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set and locations
\* ----------------------------------------------------------------------
PROC == 1..N
Locs == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choosing"}

\* ----------------------------------------------------------------------
\* Message definitions
\* ----------------------------------------------------------------------
Phase1Msg == [type : "phase1", sender : PROC, value : Values]
Phase2Msg == [type : "phase2", sender : PROC, prop : Values, est : Values]
Msg == Phase1Msg \cup Phase2Msg

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashed, sent, recv

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in PROC |-> "bcast1"]
    /\ view = [p \in PROC |-> [q \in PROC |-> Bottom]]
    /\ prop \in [PROC -> Values]
    /\ est = [p \in PROC |-> Bottom]
    /\ dec = [p \in PROC |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in PROC |-> {}]

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

Ready1(p) ==
    Cardinality({ q \in PROC : view[p][q] # Bottom }) >= N - T

EnoughEst(p) ==
    \E e \in Values :
        Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e }) >= N - T

AllPhase2(p) ==
    Cardinality({ m \in recv[p] : m.type = "phase2" }) = N

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "bcast1"
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>
    /\ sent' = sent \cup { [type |-> "phase1", sender |-> p, value |-> prop[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait1"]

ReceivePhase1(p, m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ loc[p] \in {"wait1", "bcast1", "bcast2", "wait2", "choosing"}
    /\ m \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Ready1(p)
    /\ est' = [est EXCEPT ![p] = MaxVal({ view[p][q] : q \in PROC })]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

BroadcastPhase2(p) ==
    /\ loc[p] = "bcast2"
    /\ sent' = sent \cup { [type |-> "phase2", sender |-> p,
                           prop |-> prop[p], est |-> est[p]] }
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

ReceivePhase2(p, m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ loc[p] = "wait2"
    /\ m \notin recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, view, prop, est, dec, crashed, sent>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E e \in Values :
          /\ Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e }) >= N - T
          /\ dec' = [dec EXCEPT ![p] = e]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Choose(p) ==
    /\ loc[p] = "wait2"
    /\ AllPhase2(p)
    /\ \A e \in Values :
          Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e }) < N - T
    /\ \E v \in { view[p][q] : q \in PROC, view[p][q] # Bottom } :
          dec' = [dec EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

Next ==
    \E p \in PROC :
        \/ BroadcastPhase1(p)
        \/ \E m \in Msg : ReceivePhase1(p, m)
        \/ ComputeEst(p)
        \/ BroadcastPhase2(p)
        \/ \E m \in Msg : ReceivePhase2(p, m)
        \/ Decide(p)
        \/ Choose(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [PROC -> Locs]
    /\ view \in [PROC -> [PROC -> (Values \cup {Bottom})]]
    /\ prop \in [PROC -> Values]
    /\ est \in [PROC -> (Values \cup {Bottom})]
    /\ dec \in [PROC -> (Values \cup {Bottom})]
    /\ crashed \subseteq PROC
    /\ sent \subseteq Msg
    /\ recv \in [PROC -> SUBSET Msg]

Validity ==
    \A p \in PROC :
        dec[p] # Bottom => 
            /\ dec[p] \in Values
            /\ \E q \in PROC : prop[q] = dec[p]

Agreement ==
    \A p, q \in PROC :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

====