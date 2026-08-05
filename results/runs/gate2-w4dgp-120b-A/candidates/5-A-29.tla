---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-SB: the coordinator collects votes, decides commit iff all votes are yes,
\* otherwise aborts, and then broadcasts its decision one participant at a time
\* (simple broadcast). A coordinator crash during broadcast is what makes this
\* variant blocking: some participants may be left undecided forever.

VARIABLES coordAlive, coordFaulty, coordDecision, coordRequested, coordVote,
          coordSent, vote, participantAlive, participantFaulty,
          participantDecision, participantSent

vars == <<coordAlive, coordFaulty, coordDecision, coordRequested, coordVote,
          coordSent, vote, participantAlive, participantFaulty,
          participantDecision, participantSent>>

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ vote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantSent \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ vote = [p \in participants |-> yes]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantSent = [p \in participants |-> FALSE]

\* Coordinator actions (require the coordinator to be alive):
RequestVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVote,
                 coordSent, vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: coordRequested[q]
  /\ coordVote[p] = waiting
  /\ participantSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordSent, vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

\* Failure detection is modelled as immediate: if a participant is dead and
\* never sent its vote, the coordinator detects the fault without waiting.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~participantAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordVote,
                 coordSent, vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: coordVote[p] /= waiting
  /\ coordDecision' = (IF \A p \in participants: coordVote[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordVote,
                 coordSent, vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordRequested, coordVote, coordSent,
                 vote, participantAlive, participantFaulty,
                 participantDecision, participantSent>>

\* Participant actions (require the participant to be alive):
SendVote(p) ==
  /\ participantAlive[p]
  /\ coordRequested[p]
  /\ ~participantSent[p]
  /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, coordSent, vote, participantAlive, participantFaulty,
                 participantDecision>>

AbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSent[p]
  /\ vote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, coordSent, vote, participantAlive, participantFaulty,
                 participantSent>>

AbortOnTimeout(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordAlive
  /\ coordRequested[p] = FALSE
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, coordSent, vote, participantAlive, participantFaulty,
                 participantSent>>

DecideFromBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, coordSent, vote, participantAlive, participantFaulty,
                 participantSent>>

ParticipantDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested,
                 coordVote, coordSent, vote, participantDecision, participantSent>>

Next ==
  \/ \E p \in participants: RequestVote(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideFromBroadcast(p)
  \/ \E p \in participants: ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SendVote('p1'))
        /\ WF_vars(AbortOnVote('p1'))
        /\ WF_vars(DecideFromBroadcast('p1'))
        /\ WF_vars(RequestVote('p1'))
        /\ WF_vars(ReceiveVote('p1'))
        /\ WF_vars(DetectFault('p1'))
        /\ WF_vars(MakeDecision)
        /\ WF_vars(BroadcastDecision('p1'))

\* No two participants decide differently: the coordinator's single decision
\* is distributed, so participants cannot disagree.
AC1 == \A p, q \in participants: ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

\* A commit is only possible if everyone voted yes.
AC2 == (\E p \in participants: participantDecision[p] = commit) => (\A p \in participants: vote[p] = yes)

\* An abort is caused by a no vote or a failure (participant or coordinator).
AC3 == (\E p \in participants: participantDecision[p] = abort) =>
         (\E p \in participants: vote[p] = no) \/ (\E p \in participants: participantFaulty[p]) \/ coordFaulty

\* Decisions are irrevocable: a participant decides at most once.
AC4 == (\A p \in participants: participantDecision[p] = commit) ~> (\A p \in participants: participantDecision[p] = commit)
       /\ (\A p \in participants: participantDecision[p] = abort) ~> (\A p \in participants: participantDecision[p] = abort)

\* Bounded termination: either everyone decides, or a failure is present.
AC3b == (\A p \in participants: participantDecision[p] # undecided) \/ (\E p \in participants: participantFaulty[p]) \/ coordFaulty

====