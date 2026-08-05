---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantVoted, participantOrder, coordinatorState, coordinatorFaulty,
          lastDecided, forwarding

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
          participantVoted, participantOrder, coordinatorState, coordinatorFaulty,
          lastDecided, forwarding>>

Candidate == (participants \cup {coordinatorState})
Decision == {commit, abort}

AllVoted == \A p \in participants : participantVote[p] # undecided

ReachedBroadcast == \E p \in participants :
  coordinatorState = lastDecided /\ coordinatorState # waiting /\ participantAlive[p] /\
  forwarding[p][p] = notsent

RECURSIVE AllForwarded(_)
AllForwarded(S) ==
  IF S = {} THEN TRUE
  ELSE LET p == CHOOSE x \in S : TRUE IN \A q \in participants :
       forwarding[p][q] # notsent /\ AllForwarded(S \ {p})

TypeInvNB ==
  /\ participantVote \in [participants -> {yes, no, undecided}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> Decision \cup {undecided}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantVoted \in [participants -> BOOLEAN]
  /\ participantOrder \in [participants -> 0..Cardinality(participants)]
  /\ coordinatorState \in Candidate
  /\ coordinatorFaulty \in BOOLEAN
  /\ lastDecided \in Decision
  /\ forwarding \in [participants -> [participants -> Decision \cup {notsent}]]

Init ==
  /\ participantVote = [p \in participants |-> undecided]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantVoted = [p \in participants |-> FALSE]
  /\ participantOrder = [p \in participants |-> 0]
  /\ coordinatorState = waiting
  /\ coordinatorFaulty = FALSE
  /\ lastDecided = commit
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordinatorState = waiting
  /\ coordinatorState' = waiting
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorFaulty, lastDecided, forwarding>>

GetVote(p) ==
  /\ coordinatorState = waiting
  /\ participantAlive[p] /\ ~participantVoted[p]
  /\ \E v \in {yes, no} : participantVote' = [participantVote EXCEPT ![p] = v]
  /\ participantVoted' = [participantVoted EXCEPT ![p] = TRUE]
  /\ participantOrder' = [participantOrder EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<coordinatorState, participantDecision, participantFaulty,
                coordinatorFaulty, lastDecided, forwarding>>

DetectFault ==
  /\ coordinatorState = waiting
  /\ \E p \in participants :
       participantAlive[p] /\ participantVoted[p] /\ participantVote[p] = no
  /\ coordinatorState' = waiting /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                lastDecided, forwarding>>

MakeDecision ==
  /\ coordinatorState = waiting /\ coordinatorFaulty = FALSE
  /\ AllVoted
  /\ coordinatorState' = lastDecided
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorFaulty, lastDecided, forwarding>>

BroadcastDecision ==
  /\ coordinatorState \in Decision
  /\ \E p \in participants : participantAlive[p]
  /\ coordinatorState' = waiting
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorFaulty, lastDecided, forwarding>>

CoordDie ==
  /\ coordinatorState # waiting
  /\ coordinatorState' = waiting
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                lastDecided, forwarding>>

SendVote == \E p \in participants : GetVote(p)

\* A participant adopts the coordinator's pre-decision into its own forwarding entry.
PredecideFromCoordinator(p) ==
  /\ participantAlive[p]
  /\ forwarding[p][p] = notsent
  /\ coordinatorState \in Decision
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordinatorState]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorState, coordinatorFaulty, lastDecided>>

\* A participant adopts a pre-decision that another participant has forwarded to it.
PredecideFromForwarding(p) ==
  /\ participantAlive[p]
  /\ forwarding[p][p] = notsent
  /\ coordinatorState \in Decision
  /\ \E q \in participants :
       q # p /\ forwarding[q][p] = coordinatorState
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordinatorState]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorState, coordinatorFaulty, lastDecided>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ participantAlive[p] /\ forwarding[p][p] \in Decision
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorState, coordinatorFaulty, lastDecided>>

Decide(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ forwarding[p][p] \in Decision
  /\ \A q \in participants : forwarding[p][q] = forwarding[p][p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                participantVoted, participantOrder, coordinatorState,
                coordinatorFaulty, lastDecided, forwarding>>

AbortOnTimeout(p) ==
  /\ participantAlive[p] /\ participantDecision[p] = undecided
  /\ coordinatorState = waiting /\ coordinatorFaulty = TRUE
  /\ ~(\E q \in participants : coordinatorState = lastDecided /\ participantAlive[q])
  /\ ~(\E q \in participants :
        participantFaulty[q] /\ \E r \in participants : forwarding[q][r] \in Decision)
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                participantVoted, participantOrder, coordinatorState,
                coordinatorFaulty, lastDecided, forwarding>>

AbortOnVote ==
  \E p \in participants : participantAlive[p] /\ participantVote[p] = no /\
     participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                participantVoted, participantOrder, coordinatorState,
                coordinatorFaulty, lastDecided, forwarding>>

Die(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantDecision, participantVoted,
                participantOrder, coordinatorState, coordinatorFaulty,
                lastDecided, forwarding>>

SendVoteOrAbort == SendVote \/ AbortOnVote

DecideOrForwardStep ==
  \E p \in participants :
    \/ Decide(p)
    \/ AbortOnTimeout(p)
    \/ \E q \in participants : Forward(p, q)

CoordStep == SendRequest \/ DetectFault \/ BroadcastDecision \/ CoordDie

Next ==
  \/ CoordStep
  \/ SendVoteOrAbort
  \/ \E p \in participants :
       \/ PredecideFromCoordinator(p)
       \/ PredecideFromForwarding(p)
       \/ Decide(p)
       \/ AbortOnTimeout(p)
       \/ Die(p)

MakeDecisionStep ==
  /\ coordinatorState = waiting /\ coordinatorFaulty = FALSE
  /\ \A p \in participants : participantAlive[p]
  /\ coordinatorState' = lastDecided
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                participantFaulty, participantVoted, participantOrder,
                coordinatorFaulty, lastDecided, forwarding>>

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DecideOrForwardStep)
  /\ WF_vars(SendVoteOrAbort)
  /\ WF_vars(CoordStep)
  /\ WF_vars(MakeDecisionStep)

\* AC1: No two participants can ever decide differently (agreement).
Agreement ==
  ~(\E p \in participants, q \in participants :
       p # q /\ participantDecision[p] = commit /\ participantDecision[q] = abort)

\* AC2: A commit implies a unanimous yes vote.
CommitImpliesAllYes ==
  (commit \in {participantDecision[p] : p \in participants})
    => (\A p \in participants : participantVote[p] = yes)

\* AC3: An abort means some participant voted no or some participant crashed, or
\* the coordinator crashed.
AbortImpliesNoCoordination ==
  (abort \in {participantDecision[p] : p \in participants})
    => ((\E p \in participants : participantVote[p] = no) \/ (\E p \in participants : participantFaulty[p]) \/ coordinatorFaulty)

\* AC4: Once a participant decides, its decision never changes (irrevocability).
Irrevocability ==
  \A p \in participants :
    /\ (participantDecision[p] = commit => [][participantDecision[p] = commit]_vars)
    /\ (participantDecision[p] = abort => [][participantDecision[p] = abort]_vars)

\* AC3 liveness: the system eventually decides or some process crashes.
EventualDecisionOrCrash ==
  <>(\A p \in participants : participantDecision[p] # undecided) \/ (\E p \in participants : participantFaulty[p]) \/ coordinatorFaulty

\* AC5: every non-faulty participant eventually decides -- the non-blocking
\* guarantee that simple broadcast (ACP-SB) does not provide.
EventuallyDecide ==
  \A p \in participants : (participantAlive[p] /\ participantDecision[p] = undecided) ~> (participantDecision[p] # undecided)

====