---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Constants (must match those in the .cfg)
\* -------------------------------------------------
CONSTANT participants
CONSTANT yes, no
CONSTANT undecided, commit, abort
CONSTANT waiting, notsent

\* -------------------------------------------------
\* Type definitions
\* -------------------------------------------------
VoteSet   == {yes, no}
Decision  == {undecided, commit, abort}
Status    == {"alive", "faulty"}
ReqState  == {"notrequested", "requested"}
RecvState == {"waiting", "received"}
BcastState == {"notsent", "sent"}
DecisionSet == {undecided, commit, abort}

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES
    coordAlive, coordFaulty,          \* coordinator liveness
    coordDecision,                    \* coordinator's decision (undecided/commit/abort)
    coordReq,                         \* map: participant -> "notrequested" or "requested"
    coordRecv,                        \* map: participant -> "waiting" or "received"
    coordBcast,                       \* map: participant -> "notsent" or "sent"
    partAlive,                        \* map: participant -> "alive" or "faulty"
    partVote,                         \* map: participant -> yes/no
    partSent,                         \* map: participant -> BOOLEAN (has sent vote)
    partDecision                      \* map: participant -> undecided/commit/abort

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Participants == participants

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordReq = [p \in Participants |-> "notrequested"]
    /\ coordRecv = [p \in Participants |-> waiting]
    /\ coordBcast = [p \in Participants |-> notsent]
    /\ partAlive = [p \in Participants |-> "alive"]
    /\ partVote = [p \in Participants |-> IF RandomChoice({yes, no}) = 1 THEN yes ELSE no]
    /\ partSent = [p \in Participants |-> FALSE]
    /\ partDecision = [p \in Participants |-> undecided]

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive = TRUE
    /\ coordReq[p] = "notrequested"
    /\ coordReq' = [coordReq EXCEPT ![p] = "requested"]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordRecv, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

CoordReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordReq[p] = "requested"
    /\ coordRecv[p] = waiting
    /\ partSent[p] = TRUE
    /\ coordRecv' = [coordRecv EXCEPT ![p] = "received"]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

CoordDetectFault(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordReq[p] = "requested"
    /\ coordRecv[p] = waiting
    /\ partAlive[p] = "faulty"
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq,
                    coordRecv, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in Participants: coordRecv[p] = "received"
    /\ IF \A p \in Participants: partVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq,
                    coordRecv, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

CoordBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ coordBcast[p] = notsent
    /\ coordBcast' = [coordBcast EXCEPT ![p] = sent]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv,
                    partAlive, partVote, partSent, partDecision>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

PartSendVote(p) ==
    /\ partAlive[p] = "alive"
    /\ coordReq[p] = "requested"
    /\ partSent[p] = FALSE
    /\ partSent' = [partSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partDecision>>

PartAbortOnVote(p) ==
    /\ partAlive[p] = "alive"
    /\ partDecision[p] = undecided
    /\ partSent[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partSent>>

PartAbortOnCoordDie(p) ==
    /\ partAlive[p] = "alive"
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partSent>>

PartDecideFromBroadcast(p) ==
    /\ partAlive[p] = "alive"
    /\ partDecision[p] = undecided
    /\ coordBcast[p] = sent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partSent>>

PartDie(p) ==
    /\ partAlive[p] = "alive"
    /\ partAlive' = [partAlive EXCEPT ![p] = "faulty"]
    /\ partDecision' = [partDecision EXCEPT ![p] = partDecision[p]] \* decision unchanged
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partVote, partSent>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ \E p \in Participants: CoordSendReq(p)
    \/ \E p \in Participants: CoordReceiveVote(p)
    \/ \E p \in Participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in Participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in Participants: PartSendVote(p)
    \/ \E p \in Participants: PartAbortOnVote(p)
    \/ \E p \in Participants: PartAbortOnCoordDie(p)
    \/ \E p \in Participants: PartDecideFromBroadcast(p)
    \/ \E p \in Participants: PartDie(p)

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                    coordReq, coordRecv, coordBcast,
                    partAlive, partVote, partSent, partDecision>>

\* -------------------------------------------------
\* Type invariant (required by the cfg)
\* -------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision
    /\ coordReq \in [Participants -> {"notrequested", "requested"}]
    /\ coordRecv \in [Participants -> {"waiting", "received"}]
    /\ coordBcast \in [Participants -> {"notsent", "sent"}]
    /\ partAlive \in [Participants -> Status]
    /\ partVote \in [Participants -> VoteSet]
    /\ partSent \in [Participants -> BOOLEAN]
    /\ partDecision \in [Participants -> Decision]

\* -------------------------------------------------
\* Safety predicates (optional, but useful)
\* -------------------------------------------------
Agreement ==
    ~(\E p, q \in Participants :
        partDecision[p] = commit /\ partDecision[q] = abort)

CommitValidity ==
    ~(\E p \in Participants :
        partDecision[p] = commit /\ partVote[p] = no)

AbortValidity ==
    ~(\E p \in Participants :
        partDecision[p] = abort /\
        /\ partVote[p] = yes
        /\ coordFaulty = FALSE
        /\ \A q \in Participants: partAlive[q] = "alive")

Irrevocability ==
    \A p \in Participants :
        (partDecision[p] = commit => [] (partDecision[p] = commit)) /\
        (partDecision[p] = abort  => [] (partDecision[p] = abort))

\* -------------------------------------------------
\* The module exports the required identifiers
\* -------------------------------------------------
THEOREM Spec => []TypeInv

====