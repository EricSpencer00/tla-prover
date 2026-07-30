---- MODULE ACP_NB ----
EXTENDS Integers

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentvote, coordReq,
          coordVote, coordBroadcast, coordDecision, coordAlive,
          coordFaulty, forward

vars == <<vote, alive, decision, faulty, sentvote, coordReq,
          coordVote, coordBroadcast, coordDecision, coordAlive,
          coordFaulty, forward>>

None == "none"
NoVote == "novote"
TypeOK ==
    /\ vote \in [participants -> {yes, no, NoVote}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentvote \in [participants -> BOOLEAN]
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {yes, no, NoVote}
    /\ coordBroadcast \in {None, commit, abort}
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> NoVote]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentvote = [p \in participants |-> FALSE]
    /\ coordReq = waiting
    /\ coordVote = NoVote
    /\ coordBroadcast = None
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

CoordRequest ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ \E v \in {yes, no} : coordReq' = v
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

CoordGetVote(p) ==
    /\ coordAlive
    /\ coordReq # waiting
    /\ alive[p]
    /\ ~sentvote[p]
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ vote' = [vote EXCEPT ![p] = coordReq]
    /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

CoordDetect ==
    /\ coordAlive
    /\ coordVote = NoVote
    /\ \E p \in participants :
         /\ sentvote[p]
         /\ coordVote' = vote[p]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

CoordDecide ==
    /\ coordAlive
    /\ coordVote # NoVote
    /\ coordDecision = undecided
    /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
    /\ coordBroadcast' = IF coordVote = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordVote, coordAlive, coordFaulty, forward>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, forward>>

PredecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[p][p] = notsent
    /\ coordBroadcast # None
    /\ forward' = [forward EXCEPT ![p][p] = coordBroadcast]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive,
                   coordFaulty>>

PredecideFromForward(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[p][p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ forward[q][p] # notsent
         /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive,
                   coordFaulty>>

Forward(p, q) ==
    /\ alive[p]
    /\ forward[p][p] # notsent
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive,
                   coordFaulty>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : forward[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive,
                   coordFaulty, forward>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : forward[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive,
                   coordFaulty, forward>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentvote, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty,
                   forward>>

Next ==
    \/ CoordRequest
    \/ \E p \in participants : CoordGetVote(p)
    \/ CoordDetect
    \/ CoordDecide
    \/ CoordDie
    \/ \E p \in participants : PredecideFromCoord(p)
    \/ \E p \in participants : PredecideFromForward(p)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ SF_vars(\E p \in participants : PredecideFromCoord(p))
    /\ SF_vars(\E p \in participants : PredecideFromForward(p))
    /\ WF_vars(\E p \in participants : Decide(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

TypeInvNB == TypeOK

Agreement ==
    \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
    \A p \in participants :
        (decision[p] = commit) =>
            \A q \in participants : vote[q] = yes

AbortValid ==
    \A p \in participants :
        (decision[p] = abort) =>
            (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)

Irreversible ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort) =>
            (decision[p] = [x \in [participants -> {commit, abort}] |-> x[p]])

AllDecide == \A p \in participants : decision[p] # undecided

Termination ==
    AllDecide \/ (\E p \in participants : faulty[p]) \/ coordFaulty

NoBlock == \A p \in participants : (alive[p] => (decision[p] # undecided))

Properties == Termination /\ NoBlock

====