---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (as required by the .cfg)
\* ----------------------------------------------------------------------
CONSTANT N
CONSTANT T
CONSTANT F
CONSTANT Values
CONSTANT Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ProcSet == 1..N
MsgTypes == {"phase1", "phase2"}

\* ----------------------------------------------------------------------
\* Message record
\*   type : "phase1" or "phase2"
\*   sender : process identifier
\*   prop   : proposed value (always present)
\*   est    : estimated value (only meaningful for phase2)
\* ----------------------------------------------------------------------
Message == [type : MsgTypes,
            sender : ProcSet,
            prop   : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,       \* control location of each process
    prop,      \* proposed value of each process
    view,      \* N-by-N matrix: view[p][q] = value of q known by p
    est,       \* estimated value of each process (after phase1)
    dec,       \* decision value of each process (Bottom if not decided)
    msgsSent,  \* set of all messages that have been broadcast
    msgsRecv   \* msgsRecv[p] = set of messages received by p

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Locs == {"bcast1", "wait1", "bcast2", "wait2",
         "choose", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
OtherProcs(p) == ProcSet \ {p}

MaxOrBottom(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in ProcSet |-> "bcast1"]
    /\ prop = [p \in ProcSet |-> CHOOSE v \in Values : TRUE]
    /\ view = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ est = [p \in ProcSet |-> Bottom]
    /\ dec = [p \in ProcSet |-> Bottom]
    /\ msgsSent = {}
    /\ msgsRecv = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Broadcast phase-1 message
Bcast1(p) ==
    /\ loc[p] = "bcast1"
    /\ let m == [type |-> "phase1",
                sender |-> p,
                prop   |-> prop[p],
                est    |-> Bottom] in
       /\ msgsSent' = msgsSent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<prop, view, est, dec, msgsRecv>>

\* 2. Receive a phase-1 message
Recv1(p) ==
    /\ loc[p] = "wait1"
    /\ \E m \in msgsSent :
          /\ m.type = "phase1"
          /\ view[p][m.sender] = Bottom
          /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ msgsRecv' = [msgsRecv EXCEPT ![p] = msgsRecv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, msgsSent>>

\* 3. Transition from wait1 to bcast2 after receiving N-T distinct msgs
ReadyForBcast2(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({ m \in msgsRecv[p] : m.type = "phase1" }) >= N - T
    /\ view[p][p] = Bottom
    /\ view' = [view EXCEPT ![p][p] = prop[p]]
    /\ est' = [est EXCEPT ![p] = MaxOrBottom({ view[p][q] : q \in ProcSet })]
    /\ loc' = [loc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<msgsSent, msgsRecv, prop, dec>>

\* 4. Broadcast phase-2 message
Bcast2(p) ==
    /\ loc[p] = "bcast2"
    /\ let m == [type |-> "phase2",
                sender |-> p,
                prop   |-> prop[p],
                est    |-> est[p]] in
       /\ msgsSent' = msgsSent \cup {m}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, view, est, dec, msgsRecv>>

\* 5. Receive a phase-2 message
Recv2(p) ==
    /\ loc[p] = "wait2"
    /\ \E m \in msgsSent :
          /\ m.type = "phase2"
          /\ view[p][m.sender] = Bottom
          /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ msgsRecv' = [msgsRecv EXCEPT ![p] = msgsRecv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, msgsSent>>

\* 6. Decide after seeing N-T identical estimated values
DecideFromEst(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in msgsRecv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, msgsSent, msgsRecv>>

\* 7. Move to choosing state when all N phase‑2 msgs received without a quorum
ToChoose(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({ m \in msgsRecv[p] : m.type = "phase2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in msgsRecv[p] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<prop, view, est, dec, msgsSent, msgsRecv>>

\* 8. Choose a value from the local view and decide
ChooseAndDecide(p) ==
    /\ loc[p] = "choose"
    /\ \E v \in Values :
          /\ (\E q \in ProcSet : view[p][q] = v)
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, msgsSent, msgsRecv>>

\* 9. Crash (weakly), allowed while fewer than F have crashed so far
Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ Cardinality({ q \in ProcSet : loc[q] = "crashed" }) < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<prop, view, est, dec, msgsSent, msgsRecv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet : Bcast1(p)
    \/ \E p \in ProcSet : Recv1(p)
    \/ \E p \in ProcSet : ReadyForBcast2(p)
    \/ \E p \in ProcSet : Bcast2(p)
    \/ \E p \in ProcSet : Recv2(p)
    \/ \E p \in ProcSet : DecideFromEst(p)
    \/ \E p \in ProcSet : ToChoose(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, prop, view, est, dec, msgsSent, msgsRecv>>

\* ----------------------------------------------------------------------
\* Type correctness (useful for debugging, not part of the required invariants)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [ProcSet -> Locs]
    /\ prop \in [ProcSet -> Values]
    /\ view \in [ProcSet -> [ProcSet -> (Values \cup {Bottom})]]
    /\ est \in [ProcSet -> (Values \cup {Bottom})]
    /\ dec \in [ProcSet -> (Values \cup {Bottom})]
    /\ msgsSent \subseteq Message
    /\ msgsRecv \in [ProcSet -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg
\* ----------------------------------------------------------------------
Validity ==
    \A p \in ProcSet :
        /\ dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in ProcSet :
        /\ (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====