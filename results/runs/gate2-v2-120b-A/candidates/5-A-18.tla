---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

***************************************************************************
(*  Constants (to be instantiated in the .cfg file)                     *)
***************************************************************************
CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort,   \* Decision values
    waiting, notsent            \* Special markers for messages

***************************************************************************
(*  Derived sets                                                        *)
***************************************************************************
VoteVals == {yes, no}
DecVals  == {undecided, commit, abort}
MsgVals  == {waiting, notsent} \cup DecVals

***************************************************************************
(*  Variables                                                          *)
***************************************************************************
VARIABLES
    alive,          \* [proc -> BOOLEAN]  true iff proc (coordinator or participant) is alive
    faulty,         \* [proc -> BOOLEAN]  true iff proc has crashed
    vote,           \* [participant -> VoteVals]
    sentVote,       \* [participant -> BOOLEAN]  true iff participant has sent its vote
    coordReq,       \* [participant -> BOOLEAN]  true iff coordinator has sent a vote request
    coordRecv,      \* [participant -> VoteVals \cup {waiting}]
    coordDecision, \* one of {undecided, commit, abort}
    broadcasted,    \* [participant -> MsgVals]   notsent or the decision value
    partDecision    \* [participant -> DecVals]

\* For convenience we treat the coordinator as the special identifier "c"
Coordinator == "c"
ProcSet == participants \cup {Coordinator}

\* State predicate describing the current snapshot
vars == << alive, faulty, vote, sentVote,
          coordReq, coordRecv, coordDecision,
          broadcasted, partDecision >>

***************************************************************************
(*  Initial predicate                                                   *)
***************************************************************************
Init ==
    /\ alive[Coordinator] = TRUE
    /\ faulty[Coordinator] = FALSE
    /\ coordDecision = undecided
    /\ \A p \in participants:
         /\ vote[p] \in VoteVals
         /\ alive[p] = TRUE
         /\ faulty[p] = FALSE
         /\ sentVote[p] = FALSE
         /\ coordReq[p] = FALSE
         /\ coordRecv[p] = waiting
         /\ broadcasted[p] = notsent
         /\ partDecision[p] = undecided

***************************************************************************
(*  Helper definitions                                                  *)
***************************************************************************
AllRequestsSent ==
    \A p \in participants: coordReq[p] = TRUE

AllVotesReceived ==
    \A p \in participants: coordRecv[p] # waiting

AllBroadcasted :=
    \A p \in participants: broadcasted[p] # notsent

AllDecided ==
    \A p \in participants: partDecision[p] # undecided

AllVotesYes ==
    \A p \in participants: vote[p] = yes

AtLeastOneNoVote ==
    \E p \in participants: vote[p] = no

AtLeastOneFaultyParticipant ==
    \E p \in participants: faulty[p] = TRUE

CoordinatorFaulty ==
    faulty[Coordinator] = TRUE

***************************************************************************
(*  Actions                                                             *)
***************************************************************************
CoordSendReq ==
    /\ alive[Coordinator] = TRUE
    /\ coordDecision = undecided
    /\ \E p \in participants:
          /\ coordReq[p] = FALSE
          /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
          /\ UNCHANGED << alive, faulty, vote, sentVote,
                         coordRecv, coordDecision,
                         broadcasted, partDecision >>

CoordReceiveVote ==
    /\ alive[Coordinator] = TRUE
    /\ coordDecision = undecided
    /\ AllRequestsSent
    /\ \E p \in participants:
          /\ coordRecv[p] = waiting
          /\ sentVote[p] = TRUE
          /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
          /\ UNCHANGED << alive, faulty, vote, sentVote,
                         coordReq, coordDecision,
                         broadcasted, partDecision >>

CoordDetectFault ==
    /\ alive[Coordinator] = TRUE
    /\ coordDecision = undecided
    /\ AllRequestsSent
    /\ \E p \in participants:
          /\ coordRecv[p] = waiting
          /\ faulty[p] = TRUE
          /\ coordDecision' = abort
          /\ UNCHANGED << alive, faulty, vote, sentVote,
                         coordReq, coordRecv,
                         broadcasted, partDecision >>

CoordMakeDecision ==
    /\ alive[Coordinator] = TRUE
    /\ coordDecision = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants: vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << alive, faulty, vote, sentVote,
                   coordReq, coordRecv,
                   broadcasted, partDecision >>

CoordBroadcast ==
    /\ alive[Coordinator] = TRUE
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants:
          /\ broadcasted[p] = notsent
          /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
          /\ UNCHANGED << alive, faulty, vote, sentVote,
                         coordReq, coordRecv, coordDecision,
                         partDecision >>

CoordDie ==
    /\ alive[Coordinator] = TRUE
    /\ faulty[Coordinator] = FALSE
    /\ faulty' = [faulty EXCEPT ![Coordinator] = TRUE]
    /\ alive' = [alive EXCEPT ![Coordinator] = FALSE]
    /\ UNCHANGED << vote, sentVote,
                   coordReq, coordRecv, coordDecision,
                   broadcasted, partDecision >>

PartSendVote ==
    /\ \E p \in participants:
          /\ alive[p] = TRUE
          /\ sentVote[p] = FALSE
          /\ coordReq[p] = TRUE
          /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
          /\ UNCHANGED << alive, faulty, vote,
                         coordReq, coordRecv, coordDecision,
                         broadcasted, partDecision >>

PartAbortOnVote ==
    /\ \E p \in participants:
          /\ alive[p] = TRUE
          /\ partDecision[p] = undecided
          /\ sentVote[p] = TRUE
          /\ vote[p] = no
          /\ partDecision' = [partDecision EXCEPT ![p] = abort]
          /\ UNCHANGED << alive, faulty, vote,
                         sentVote, coordReq, coordRecv,
                         coordDecision, broadcasted >>

PartAbortOnTimeout ==
    /\ \E p \in participants:
          /\ alive[p] = TRUE
          /\ partDecision[p] = undecided
          /\ coordReq[p] = FALSE
          /\ faulty[Coordinator] = TRUE
          /\ partDecision' = [partDecision EXCEPT ![p] = abort]
          /\ UNCHANGED << alive, faulty, vote,
                         sentVote, coordReq, coordRecv,
                         coordDecision, broadcasted >>

PartDecideFromBroadcast ==
    /\ \E p \in participants:
          /\ alive[p] = TRUE
          /\ partDecision[p] = undecided
          /\ broadcasted[p] \in {commit, abort}
          /\ partDecision' = [partDecision EXCEPT ![p] = broadcasted[p]]
          /\ UNCHANGED << alive, faulty, vote,
                         sentVote, coordReq, coordRecv,
                         coordDecision, broadcasted >>

PartDie ==
    /\ \E p \in participants:
          /\ alive[p] = TRUE
          /\ faulty[p] = FALSE
          /\ alive' = [alive EXCEPT ![p] = FALSE]
          /\ faulty' = [faulty EXCEPT ![p] = TRUE]
          /\ UNCHANGED << vote, sentVote,
                         coordReq, coordRecv, coordDecision,
                         broadcasted, partDecision >>

\* Stuttering step to avoid deadlock
Stutter ==
    UNCHANGED vars

Next ==
    \/ CoordSendReq
    \/ CoordReceiveVote
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ PartSendVote
    \/ PartAbortOnVote
    \/ PartAbortOnTimeout
    \/ PartDecideFromBroadcast
    \/ PartDie
    \/ Stutter

Spec == Init /\ [][Next]_vars

***************************************************************************
(*  Safety invariant (type-correctness)                                 *)
***************************************************************************
TypeOk ==
    /\ alive[Coordinator] \in BOOLEAN
    /\ faulty[Coordinator] \in BOOLEAN
    /\ coordDecision \in DecVals
    /\ \A p \in participants:
         /\ vote[p] \in VoteVals
         /\ sentVote[p] \in BOOLEAN
         /\ coordReq[p] \in BOOLEAN
         /\ coordRecv[p] \in VoteVals \cup {waiting}
         /\ broadcasted[p] \in MsgVals
         /\ partDecision[p] \in DecVals
         /\ alive[p] \in BOOLEAN
         /\ faulty[p] \in BOOLEAN

\* AC1: Agreement – no two participants decide differently
Agreement ==
    \A p,q \in participants:
        (partDecision[p] = commit) => (partDecision[q] = commit)

\* AC2: Commit validity – if any commits then all voted yes
CommitValidity ==
    \A p \in participants:
        (partDecision[p] = commit) => AllVotesYes

\* AC3: Abort validity – if any aborts then a no‑vote or a fault occurred
AbortValidity ==
    \A p \in participants:
        (partDecision[p] = abort) =>
            (AtLeastOneNoVote \/ AtLeastOneFaultyParticipant \/ CoordinatorFaulty)

\* AC4: Irrevocability – decision never changes once made
Irrevocability ==
    \A p \in participants:
        /\ (partDecision[p] = commit) => (partDecision[p]' = commit)
        /\ (partDecision[p] = abort)  => (partDecision[p]' = abort)

\* Full safety invariant required by the description
SafetyInv == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

\* The .cfg file expects the name TypeInv, so we alias it
TypeInv == TypeOk

=============================================================================