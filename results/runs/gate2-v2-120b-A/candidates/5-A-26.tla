---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----- Constants -------------------------------------------------
CONSTANTS participants, yes, no,
          undecided, commit, abort,
          waiting, notsent

\* ----- State variables -------------------------------------------
\* Coordinator state
VarCoordAlive      \* TRUE = alive, FALSE = dead
VarCoordFaulty     \* TRUE = faulty (crashed), FALSE = not faulty
CoordDecision      \* one of {undecided, commit, abort}
CoordSentRequest   \* [p \in participants |-> BOOLEAN]
CoordVoteReceived  \* [p \in participants |-> {yes,no,waiting}]
CoordSentDecision  \* [p \in participants |-> {sent, notsent}]

\* Participants state (functions indexed by participants)
PartAlive          \* [p \in participants |-> BOOLEAN]
PartFaulty         \* [p \in participants |-> BOOLEAN]
PartVote           \* [p \in participants |-> {yes,no}]
PartDecision       \* [p \in participants |-> {undecided, commit, abort}]
PartSentVote       \* [p \in participants |-> BOOLEAN]

\* ----- Initial state ---------------------------------------------
Init ==
  /\ VarCoordAlive = TRUE
  /\ VarCoordFaulty = FALSE
  /\ CoordDecision = undecided
  /\ CoordSentRequest = [p \in participants |-> FALSE]
  /\ CoordVoteReceived = [p \in participants |-> waiting]
  /\ CoordSentDecision = [p \in participants |-> notsent]
  /\ PartAlive = [p \in participants |-> TRUE]
  /\ PartFaulty = [p \in participants |-> FALSE]
  /\ PartDecision = [p \in participants |-> undecided]
  /\ PartSentVote = [p \in participants |-> FALSE]
  /\ \A p \in participants: PartVote[p] \in {yes, no}

\* ----- Helper predicates ------------------------------------------
AllVotesReceived ==
  \A p \in participants: CoordVoteReceived[p] # waiting

AllDecisionsSent ==
  \A p \in participants: CoordSentDecision[p] = sent

AllParticipantsDecided ==
  \A p \in participants: PartDecision[p] # undecided

AtLeastOneYes ==
  \E p \in participants: PartVote[p] = yes

AtLeastOneNo ==
  \E p \in participants: PartVote[p] = no

AnyParticipantFaulty ==
  \E p \in participants: PartFaulty[p] = TRUE

CoordinatorFaulty ==
  VarCoordFaulty = TRUE

\* ----- Actions ----------------------------------------------------
\* Coordinator actions
Coordinator_SendRequest(p) ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ ~CoordSentRequest[p]
  /\ CoordSentRequest' = [CoordSentRequest EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordVoteReceived,
                CoordSentDecision, PartAlive,
                PartFaulty, PartVote, PartDecision,
                PartSentVote>>

Coordinator_ReceiveVote(p) ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ CoordSentRequest[p]
  /\ CoordVoteReceived[p] = waiting
  /\ PartSentVote[p]
  /\ CoordVoteReceived' =
        [CoordVoteReceived EXCEPT ![p] = PartVote[p]]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordSentDecision, PartAlive,
                PartFaulty, PartVote, PartDecision,
                PartSentVote>>

Coordinator_DetectFault(p) ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ CoordSentRequest[p]
  /\ CoordVoteReceived[p] = waiting
  /\ ~PartAlive[p]
  /\ ~PartSentVote[p]
  /\ CoordDecision' = abort
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordSentRequest, CoordVoteReceived,
                CoordSentDecision, PartAlive,
                PartFaulty, PartVote, PartDecision,
                PartSentVote>>

Coordinator_Decide ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ CoordDecision = undecided
  /\ AllVotesReceived
  /\ IF \A p \in participants: CoordVoteReceived[p] = yes
        THEN CoordDecision' = commit
        ELSE CoordDecision' = abort
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordSentRequest, CoordVoteReceived,
                CoordSentDecision, PartAlive,
                PartFaulty, PartVote, PartDecision,
                PartSentVote>>

Coordinator_Broadcast(p) ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ CoordDecision # undecided
  /\ CoordSentDecision[p] = notsent
  /\ CoordSentDecision' = [CoordSentDecision EXCEPT ![p] = sent]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, PartAlive,
                PartFaulty, PartVote, PartDecision,
                PartSentVote>>

Coordinator_Die ==
  /\ VarCoordAlive
  /\ ~VarCoordFaulty
  /\ VarCoordAlive' = FALSE
  /\ VarCoordFaulty' = TRUE
  /\ UNCHANGED <<CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartAlive, PartFaulty, PartVote,
                PartDecision, PartSentVote>>

\* Participant actions
Participant_SendVote(p) ==
  /\ PartAlive[p]
  /\ ~PartFaulty[p]
  /\ CoordSentRequest[p]
  /\ ~PartSentVote[p]
  /\ PartSentVote' = [PartSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartAlive, PartFaulty, PartVote,
                PartDecision>>

Participant_AbortOnNo(p) ==
  /\ PartAlive[p]
  /\ ~PartFaulty[p]
  /\ PartDecision[p] = undecided
  /\ PartSentVote[p]
  /\ PartVote[p] = no
  /\ PartDecision' = [PartDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartAlive, PartFaulty, PartVote,
                PartSentVote>>

Participant_AbortOnTimeout(p) ==
  /\ PartAlive[p]
  /\ ~PartFaulty[p]
  /\ PartDecision[p] = undecided
  /\ ~CoordSentRequest[p]
  /\ VarCoordFaulty
  /\ PartDecision' = [PartDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartAlive, PartFaulty, PartVote,
                PartSentVote>>

Participant_AdoptDecision(p) ==
  /\ PartAlive[p]
  /\ ~PartFaulty[p]
  /\ PartDecision[p] = undecided
  /\ CoordSentDecision[p] = sent
  /\ PartDecision' = [PartDecision EXCEPT ![p] = CoordDecision]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartAlive, PartFaulty, PartVote,
                PartSentVote>>

Participant_Die(p) ==
  /\ PartAlive[p]
  /\ ~PartFaulty[p]
  /\ PartAlive' = [PartAlive EXCEPT ![p] = FALSE]
  /\ PartFaulty' = [PartFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<VarCoordAlive, VarCoordFaulty,
                CoordDecision, CoordSentRequest,
                CoordVoteReceived, CoordSentDecision,
                PartVote, PartDecision, PartSentVote>>

\* ----- Next-state relation ----------------------------------------
Next ==
  \/ \E p \in participants: Coordinator_SendRequest(p)
  \/ \E p \in participants: Coordinator_ReceiveVote(p)
  \/ \E p \in participants: Coordinator_DetectFault(p)
  \/ Coordinator_Decide
  \/ \E p \in participants: Coordinator_Broadcast(p)
  \/ Coordinator_Die
  \/ \E p \in participants: Participant_SendVote(p)
  \/ \E p \in participants: Participant_AbortOnNo(p)
  \/ \E p \in participants: Participant_AbortOnTimeout(p)
  \/ \E p \in participants: Participant_AdoptDecision(p)
  \/ \E p \in participants: Participant_Die(p)

\* ----- Specification -----------------------------------------------
Spec == Init /\ [][Next]_<<VarCoordAlive, VarCoordFaulty,
                        CoordDecision, CoordSentRequest,
                        CoordVoteReceived, CoordSentDecision,
                        PartAlive, PartFaulty,
                        PartVote, PartDecision,
                        PartSentVote>>

\* ----- Type correctness invariant ----------------------------------
CoordDecisionSet == {undecided, commit, abort}
PartDecisionSet == {undecided, commit, abort}
VoteSet == {yes, no}
SentState == {sent, notsent}
BoolSet == BOOLEAN

TypeInv ==
  /\ VarCoordAlive \in BoolSet
  /\ VarCoordFaulty \in BoolSet
  /\ CoordDecision \in CoordDecisionSet
  /\ CoordSentRequest \in [participants -> BoolSet]
  /\ CoordVoteReceived \in [participants -> {yes, no, waiting}]
  /\ CoordSentDecision \in [participants -> SentState]
  /\ PartAlive \in [participants -> BoolSet]
  /\ PartFaulty \in [participants -> BoolSet]
  /\ PartVote \in [participants -> VoteSet]
  /\ PartDecision \in [participants -> PartDecisionSet]
  /\ PartSentVote \in [participants -> BoolSet]

\* ----- Safety invariants -------------------------------------------
\* AC1: No two participants decide differently
CA1 ==
  \A p, q \in participants:
    (PartDecision[p] = commit => PartDecision[q] = commit) /\
    (PartDecision[p] = abort  => PartDecision[q] = abort)   /\
    (PartDecision[p] = undecided \/ PartDecision[q] = undecided)

\* AC2: Commit validity
CA2 ==
  \A p \in participants:
    (PartDecision[p] = commit => \A q \in participants: PartVote[q] = yes)

\* AC3: Abort validity
CA3 ==
  \A p \in participants:
    (PartDecision[p] = abort =>
        ( \E q \in participants: PartVote[q] = no )
        \/ AnyParticipantFaulty
        \/ CoordinatorFaulty)

\* AC4: Irrevocability
CA4 ==
  \A p \in participants:
    (PartDecision[p] = commit => 
        [] (PartDecision[p] = commit))
    /\ (PartDecision[p] = abort =>
        [] (PartDecision[p] = abort))

\* ----- Liveness component (optional) --------------------------------
\* The liveness property is not part of the required invariants but is
\* defined here for completeness.
Liveness ==
  <> ( AllParticipantsDecided \/ AnyParticipantFaulty \/ CoordinatorFaulty )

=============================================================================