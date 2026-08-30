---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The Atomic Commitment Protocol with Simple Broadcast (ACP-SB) models a
\* coordinator collecting votes from participants and broadcasting a commit
\* or abort decision. The simple broadcast variant can block if the
\* coordinator crashes mid-broadcast, so it does not guarantee termination.
\* Safety properties (agreement, commit/abort validity, irrevocability) are
\* always satisfied; the liveness property is only partial (it does not
\* require every non-faulty participant to eventually decide).

VARIABLES vote, alive, decision, faulty, sentVote, coordSentReq,
          coordVote, coordSentDecision, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, coordSentReq,
           coordVote, coordSentDecision, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordSentReq \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordSentReq = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions: send vote requests, collect votes, detect faults,
\* decide, broadcast the decision, or die.
SendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordSentReq[p]
  /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSentReq[p]
  /\ coordVote[p] = waiting
  /\ sentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordSentReq,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSentReq[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordSentReq,
                 coordVote, coordSentDecision, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordSentReq[p]
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordSentReq,
                 coordVote, coordSentDecision, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSentDecision[p] = notsent
  /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordSentReq,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordSentReq,
                 coordVote, coordSentDecision, coordDecision, coordFaulty>>

\* Participant actions: send vote, unilaterally abort on a no vote, abort
\* on timeout when the coordinator dies, adopt the coordinator's broadcast,
\* or die.
SendVote(p) ==
  /\ alive[p]
  /\ coordSentReq[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordSentReq, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordSentReq, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordSentReq[p]
  /\ coordFaulty
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordSentReq, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordSentReq, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordSentReq, coordVote,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                            \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                            \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p) \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(DecideFromBroadcast(p))
  /\ \A p \in participants : WF_vars(AbortOnTimeout(p))

\* Safety: no two participants ever decide differently, and a commit can
\* only happen if every vote was yes.
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q])
        \/ coordFaulty

Irrevocability ==
  \A p \in participants :
    /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
    /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])

\* Liveness: either everyone decides, or some participant is faulty, or the
\* coordinator is faulty. The simple broadcast variant does NOT guarantee
\* that every non-faulty participant eventually decides.
EventualDecision ==
  <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)

====