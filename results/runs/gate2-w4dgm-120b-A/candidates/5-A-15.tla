---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault

vars == <<vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decided \in [participants -> {undecided, commit, abort}]
    /\ fault \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordReqSent \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordDecided \in {commit, abort, undecided}
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordAlive \in BOOLEAN
    /\ coordFault \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
    /\ alive = [p \in participants |-> TRUE]
    /\ decided = [p \in participants |-> undecided]
    /\ fault = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordReqSent = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordDecided = undecided
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordAlive = TRUE
    /\ coordFault = FALSE

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordReqSent[p]
    /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

CoordRecv(p) ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ coordReqSent[p]
    /\ coordVote[p] = waiting
    /\ sentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordReqSent, coordDecided, coordSent, coordAlive, coordFault>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ coordReqSent[p]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ ~sentVote[p]
    /\ coordDecided' = abort
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordSent, coordAlive, coordFault>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecided = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecided' = (IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort)
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordSent, coordAlive, coordFault>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecided # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecided]
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordDecided, coordAlive, coordFault>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFault' = TRUE
    /\ UNCHANGED <<vote, alive, decided, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive>>

ParticipantSendVote(p) ==
    /\ alive[p]
    /\ coordReqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decided, fault, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

ParticipantAbortOnVote(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

ParticipantAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ ~coordReqSent[p]
    /\ coordAlive = FALSE
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

ParticipantDecide(p) ==
    /\ alive[p]
    /\ decided[p] = undecided
    /\ coordSent[p] # notsent
    /\ decided' = [decided EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, fault, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ fault' = [fault EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decided, sentVote, coordReqSent, coordVote, coordDecided, coordSent, coordAlive, coordFault>>

Next ==
    \/ \E p \in participants : CoordSendReq(p) \/ CoordRecv(p) \/ CoordDetectFault(p) \/ CoordBroadcast(p)
                            \/ ParticipantSendVote(p) \/ ParticipantAbortOnVote(p) \/ ParticipantAbortOnTimeout(p)
                            \/ ParticipantDecide(p) \/ ParticipantDie(p)
    \/ CoordDecide
    \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants :
        /\ TRUE
        /\ WF_vars(ParticipantSendVote(p))
        /\ WF_vars(ParticipantAbortOnVote(p))
        /\ WF_vars(ParticipantDecide(p))
    /\ WF_vars(CoordDecide)

Agreement ==
    \A p, q \in participants : (decided[p] = commit) => (decided[q] # abort)

CommitValid == \A p \in participants : decided[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
    \A p \in participants : decided[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : fault[q]
        \/ coordFault

DecideOnce ==
    \A p \in participants :
        /\ (decided[p] = commit) ~> (decided[p] = commit)
        /\ (decided[p] = abort) ~> (decided[p] = abort)

EventualDecision ==
    \A p \in participants :
        (decided[p] = undecided) ~> (decided[p] # undecided)

AC3Liveness == DecideOnce /\ EventualDecision

====