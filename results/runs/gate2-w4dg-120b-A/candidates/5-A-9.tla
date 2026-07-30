---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants,
  yes,
  no,
  undecided,
  commit,
  abort,
  waiting,
  notsent

ASSUME yes # no
ASSUME undecided # commit /\ undecided # abort

VARIABLES
  vote,
  alive,
  decision,
  faulty,
  sentVote,
  coordRequested,
  coordRecv,
  coordBroadcast,
  coordDecision,
  coordAlive,
  coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {yes, no, waiting}]
  /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> IF CHOOSE x \in {yes, no} : TRUE THEN yes ELSE no]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

RecieveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ ~sentVote[p]
  /\ coordRecv[p] = waiting
  /\ sentVote[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequested, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequested, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordRequested, coordRecv, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p)
  \/ \E p \in participants : RecieveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromBroadcast(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : AbortVote(p))
        /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))
        /\ WF_vars(\E p \in participants : SendRequest(p))
        /\ WF_vars(\E p \in participants : RecieveVote(p))
        /\ WF_vars(\E p \in participants : Broadcast(p))
        /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ coordFaulty

DecideOnce ==
  \A p \in participants :
    (decision[p] = commit => \A s \in [participants -> {undecided, commit, abort}] : decision[p] = s) /\
    (decision[p] = abort => \A s \in [participants -> {undecided, commit, abort}] : decision[p] = s)

EventuallyDecide == <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)

====