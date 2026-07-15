---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,               \* number of processes
    T,               \* max tolerated faults
    F,               \* max actual crashes
    Values,          \* finite totally ordered set of proposal values
    Bottom           \* special value not in Values

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"Phase1", "Phase2"},
            sender : Proc,
            prop   : Values \cup {Bottom},
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,            \* control location of each process
    view,           \* local view matrix: view[p][q] is value from q known to p
    propVal,        \* proposed value of each process
    est,            \* estimated value after Phase1
    decide,         \* decision value of each process
    crashed,        \* number of crashed processes (0..F)
    sent,           \* set of all sent messages
    recv            \* received messages per process

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Locs == {"Bcast1", "Wait1", "Bcast2", "Wait2",
         "Done", "Crashed", "Choosing"}

InitLoc(p) == IF p \in Proc THEN "Bcast1" ELSE "Done"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc   = [p \in Proc |-> InitLoc(p)]
    /\ propVal = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* nondeterministic choice
    /\ view  = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est   = [p \in Proc |-> Bottom]
    /\ decide= [p \in Proc |-> Bottom]
    /\ crashed = 0
    /\ sent  = {}
    /\ recv  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BcastPhase1(p) ==
    /\ loc[p] = "Bcast1"
    /\ let m == [type |-> "Phase1",
                sender |-> p,
                prop   |-> propVal[p],
                est    |-> Bottom] in
       /\ sent' = sent \cup {m}
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ loc'  = [loc EXCEPT ![p] = "Wait1"]
    /\ UNCHANGED <<view, est, decide, crashed, propVal>>

ReceivePhase1(p) ==
    /\ loc[p] = "Wait1"
    /\ \E m \in sent :
         /\ m.type = "Phase1"
         /\ m.prop # Bottom
         /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, est, decide, crashed, propVal, sent>>

ComputeEst(p) ==
    /\ loc[p] = "Wait1"
    /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ loc' = [loc EXCEPT ![p] = "Bcast2"]
    /\ UNCHANGED <<view, decide, crashed, propVal, sent, recv>>

BcastPhase2(p) ==
    /\ loc[p] = "Bcast2"
    /\ let m == [type |-> "Phase2",
                sender |-> p,
                prop   |-> propVal[p],
                est    |-> est[p]] in
       /\ sent' = sent \cup {m}
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ loc'  = [loc EXCEPT ![p] = "Wait2"]
    /\ UNCHANGED <<view, est, decide, crashed, propVal>>

ReceivePhase2(p) ==
    /\ loc[p] = "Wait2"
    /\ \E m \in sent :
         /\ m.type = "Phase2"
         /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, est, decide, crashed, propVal, sent>>

DecideFromThreshold(p) ==
    /\ loc[p] = "Wait2"
    /\ \E v \in Values :
         /\ Cardinality({ m \in recv[p] :
                         m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ decide' = [decide EXCEPT ![p] = v]
    /\ loc'    = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<view, est, crashed, propVal, sent, recv>>

MoveToChoosing(p) ==
    /\ loc[p] = "Wait2"
    /\ Cardinality({ m \in recv[p] : m.type = "Phase2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[p] :
                         m.type = "Phase2" /\ m.est = v }) < N - T
    /\ loc' = [loc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<view, est, decide, crashed, propVal, sent, recv>>

Choosing(p) ==
    /\ loc[p] = "Choosing"
    /\ \E v \in Values :
         /\ v \in { view[p][q] : q \in Proc }
    /\ decide' = [decide EXCEPT ![p] = v]
    /\ loc'    = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<view, est, crashed, propVal, sent, recv>>

Crash(p) ==
    /\ loc[p] # "Crashed"
    /\ crashed < F
    /\ loc'    = [loc EXCEPT ![p] = "Crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, est, decide, propVal, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : DecideFromThreshold(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choosing(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, propVal, est, decide, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ propVal \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decide \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \in 0..F
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decide[p] # Bottom => decide[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decide[p] # Bottom
        /\ decide[q] # Bottom
        => decide[p] = decide[q]

=============================================================================