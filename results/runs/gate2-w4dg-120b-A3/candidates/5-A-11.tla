---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote, alive, decision, faulty, voteSent,
  reqSent, rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voteSent,
          reqSent, rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

MaxVote == 3
MaxState == 3

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ rxVote \in [participants -> {yes, no, waiting}]
  /\ broadcastSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> TRUE]
  /\ decision \in [participants -> undecided]
  /\ faulty \in [participants -> FALSE]
  /\ voteSent \in [participants -> FALSE]
  /\ reqSent \in [participants -> FALSE]
  /\ rxVote \in [participants -> waiting]
  /\ broadcastSent \in [participants -> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteRequest(p) ==
  /\ coordAlive
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                rxVote, broadcastSent, coordDecision, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : reqSent[q]
  /\ rxVote[p] = waiting
  /\ voteSent[p]
  /\ rxVote' = [rxVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, broadcastSent, coordDecision, coordAlive, coordFaulty>>

DetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : reqSent[q]
  /\ rxVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, rxVote, broadcastSent, coordAlive>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : rxVote[q] # waiting
  /\ IF \A q \in participants : rxVote[q] = yes
        THEN coordDecision' = commit
        ELSE coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, rxVote, broadcastSent, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, rxVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                reqSent, rxVote, broadcastSent, coordDecision>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, reqSent,
                rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voteSent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent,
                reqSent, rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~reqSent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, voteSent, reqSent,
                rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcastSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent,
                reqSent, rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent,
                reqSent, rxVote, broadcastSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteRequest(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectParticipantFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants : ParticipantSendVote(p)
  \/ \E p \in participants : ParticipantAbortOnVote(p)
  \/ \E p \in participants : ParticipantAbortOnTimeout(p)
  \/ \E p \in participants : ParticipantDecide(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendVoteRequest(p))
        /\ WF_vars(\E p \in participants : ReceiveVote(p))
        /\ WF_vars(\E p \in participants : BroadcastDecision(p))
        /\ WF_vars(\E p \in participants : ParticipantSendVote(p))
        /\ WF_vars(\E p \in participants : ParticipantAbortOnVote(p))
        /\ WF_vars(\E p \in participants : ParticipantDecide(p))

AC1 == \A a, b \in participants : (decision[a] = commit) => (decision[b] = commit)
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes
AC3 == \A p \in participants : decision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty
AC4 == \A p \in participants :
        /\ decision[p] = commit => TRUE
        /\ decision[p] = abort => TRUE
\* Irreversibility is enforced by stuttering once decided: no action ever changes decision[p] once it is commit or abort.

DecideEventual ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p]) \/ coordFaulty

====