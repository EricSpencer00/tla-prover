---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coordReq \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {waiting, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coordReq = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteReq(c) ==
  /\ coordAlive
  /\ ~coordReq[c]
  /\ coordReq' = [coordReq EXCEPT ![c] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote, coordSent, coordDecision, coordFaulty>>

ReceiveVote(c) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A d \in participants : coordReq[d]
  /\ coordVote[c] = waiting
  /\ sent[c]
  /\ coordVote' = [coordVote EXCEPT ![c] = vote[c]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordSent, coordDecision, coordFaulty>>

DetectFault(c) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A d \in participants : coordReq[d]
  /\ coordVote[c] = waiting
  /\ ~alive[c]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordSent, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A d \in participants : coordVote[d] # waiting
  /\ coordDecision' = IF \A d \in participants : coordVote[d] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(c) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[c] = notsent
  /\ coordSent' = [coordSent EXCEPT ![c] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordSent, coordDecision>>

CoordProgress == MakeDecision \/ CoordDie

SendVote(p) ==
  /\ alive[p]
  /\ coordReq[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReq[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coordReq, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantProgress(p) == SendVote(p) \/ AbortOnVote(p) \/ AbortTimeout(p) \/ DecideOnBroadcast(p)

Next ==
  \/ \E c \in participants : SendVoteReq(c)
  \/ \E c \in participants : ReceiveVote(c)
  \/ \E c \in participants : DetectFault(c)
  \/ MakeDecision
  \/ \E c \in participants : BroadcastDecision(c)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ TRUE
        /\ WF_vars(CoordProgress)
        /\ \A p \in participants : WF_vars(ParticipantProgress(p))

Agreement ==
  \A p1, p2 \in participants : (decision[p1] = commit /\ decision[p2] = abort) => FALSE

CommitValidity ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
  \A p \in participants : decision[p] = abort => ( (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty)

Irreversibility ==
  \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
                         /\ (decision[p] = abort) ~> (decision[p] = abort)

DecideOrFaulty ==
  (\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

TypeInv == TypeOK

====