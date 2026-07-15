---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ProcSet == 1..N
Phase1Msg == [type : "Phase1", sender : ProcSet, value : VALUES_EXCL_BOTTOM]
Phase2Msg == [type : "Phase2", sender : ProcSet, proposal : VALUES_EXCL_BOTTOM,
              estimate : VALUES_EXCL_BOTTOM]
Msg == Phase1Msg \cup Phase2Msg

\* Helper to exclude Bottom from the value domain
VALUES_EXCL_BOTTOM == Values \ {Bottom}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,        \* control location of each process
    localViews, \* matrix: proc -> proc -> value
    proposal,   \* each process's initial proposal
    estimate,   \* each process's estimated value (max after phase1)
    decision,   \* each process's decided value
    crashed,    \* number of crashed processes
    sent,       \* set of messages that have been broadcast
    recv        \* map: proc -> set of messages received by that proc

\* ----------------------------------------------------------------------
\* Enumerated locations
\* ----------------------------------------------------------------------
Locs == {"Broadcast1", "Wait1", "Broadcast2", "Wait2",
         "Done", "Crashed", "Choosing"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in ProcSet |-> "Broadcast1"]
    /\ proposal = [p \in ProcSet |-> CHOOSE v \in VALUES_EXCL_BOTTOM : TRUE]
    /\ estimate = [p \in ProcSet |-> Bottom]
    /\ decision = [p \in ProcSet |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [p \in ProcSet |-> {}]
    /\ localViews = [i \in ProcSet |-> [j \in ProcSet |-> Bottom]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxInView(p) ==
    LET vals == { localViews[p][q] : q \in ProcSet } \ {Bottom} IN
    IF vals = {} THEN Bottom ELSE Max(vals)

CountCrashed == crashed

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "Broadcast1"
    /\ sent' = sent \cup { [type |-> "Phase1", sender |-> p,
                           value |-> proposal[p]] }
    /\ loc' = [loc EXCEPT ![p] = "Wait1"]
    /\ UNCHANGED <<proposal, estimate, decision, crashed,
                    recv, localViews>>

ReceivePhase1(p) ==
    \E m \in sent :
        /\ m.type = "Phase1"
        /\ m.sender \in ProcSet
        /\ m.value \in VALUES_EXCL_BOTTOM
        /\ m \notin recv[p]
        /\ loc[p] = "Wait1"
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ localViews' = [localViews EXCEPT ![p][m.sender] = m.value]
        /\ UNCHANGED <<proposal, estimate, decision, crashed,
                    sent, loc>>

ComputeEstimate(p) ==
    /\ loc[p] = "Wait1"
    /\ Cardinality({ m \in recv[p] : m.type = "Phase1" }) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "Broadcast2"]
    /\ UNCHANGED <<proposal, decision, crashed, sent,
                    recv, localViews>>

BroadcastPhase2(p) ==
    /\ loc[p] = "Broadcast2"
    /\ sent' = sent \cup { [type |-> "Phase2", sender |-> p,
                           proposal |-> proposal[p],
                           estimate |-> estimate[p]] }
    /\ loc' = [loc EXCEPT ![p] = "Wait2"]
    /\ UNCHANGED <<proposal, estimate, decision, crashed,
                    recv, localViews>>

ReceivePhase2(p) ==
    \E m \in sent :
        /\ m.type = "Phase2"
        /\ m.sender \in ProcSet
        /\ m \notin recv[p]
        /\ loc[p] = "Wait2"
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED <<proposal, estimate, decision,
                    crashed, sent, loc, localViews>>

DecideWithThreshold(p) ==
    /\ loc[p] = "Wait2"
    /\ \E v \in VALUES_EXCL_BOTTOM :
          Cardinality({ m \in recv[p] : m.type = "Phase2"
                                         /\ m.estimate = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<proposal, estimate, crashed,
                    sent, recv, localViews>>

MoveToChoosing(p) ==
    /\ loc[p] = "Wait2"
    /\ \A v \in VALUES_EXCL_BOTTOM :
          Cardinality({ m \in recv[p] : m.type = "Phase2"
                                         /\ m.estimate = v }) < N - T
    /\ Cardinality({ m \in recv[p] : m.type = "Phase2" }) = N
    /\ loc' = [loc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<proposal, estimate, decision,
                    crashed, sent, recv, localViews>>

Choosing(p) ==
    /\ loc[p] = "Choosing"
    /\ \E v \in VALUES_EXCL_BOTTOM :
          v \in { localViews[p][q] : q \in ProcSet }
    /\ decision' = [decision EXCEPT ![p] = 
                     CHOOSE v \in VALUES_EXCL_BOTTOM :
                         v \in { localViews[p][q] : q \in ProcSet }]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<proposal, estimate, crashed,
                    sent, recv, localViews>>

Crash(p) ==
    /\ loc[p] \notin {"Done", "Crashed"}
    /\ crashed < F
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "Crashed"]
    /\ UNCHANGED <<proposal, estimate, decision,
                    sent, recv, localViews>>

Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet : ReceivePhase1(p)
    \/ \E p \in ProcSet : ComputeEstimate(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet : ReceivePhase2(p)
    \/ \E p \in ProcSet : DecideWithThreshold(p)
    \/ \E p \in ProcSet : MoveToChoosing(p)
    \/ \E p \in ProcSet : Choosing(p)
    \/ \E p \in ProcSet : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, proposal, estimate, decision,
                     crashed, sent, recv, localViews>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [ProcSet -> Locs]
    /\ proposal \in [ProcSet -> VALUES_EXCL_BOTTOM]
    /\ estimate \in [ProcSet -> (VALUES_EXCL_BOTTOM \cup {Bottom})]
    /\ decision \in [ProcSet -> (VALUES_EXCL_BOTTOM \cup {Bottom})]
    /\ crashed \in Nat /\ crashed <= F
    /\ sent \subseteq Msg
    /\ recv \in [ProcSet -> SUBSET Msg]
    /\ localViews \in [ProcSet -> [ProcSet -> (VALUES_EXCL_BOTTOM \cup {Bottom})]]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in ProcSet :
        decision[p] # Bottom => 
            \E q \in ProcSet : proposal[q] = decision[p]

Agreement ==
    \A p, q \in ProcSet :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Theorems (optional, but kept for completeness)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====