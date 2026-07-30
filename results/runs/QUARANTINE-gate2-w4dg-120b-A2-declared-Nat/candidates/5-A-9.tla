---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent, coordVote,
         coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, reqSent, coordVote,
          coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote = [p \in participants |-> IF nondeterministic THEN yes ELSE no]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendReq(p) ==
    /\ coordAlive
    /\ ~reqSent[p]
    /\ coordSent = notsent
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ coordVote[p] = waiting
    /\ sentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : reqSent[q]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = no]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent,
                    coordSent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent,
                    coordVote, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent,
                    coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, reqSent,
                    coordVote, coordSent, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~reqSent[p]
    /\ ~coordAlive
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent, coordVote,
                    coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
                           \/ BroadcastDecision(p)
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
                           \/ DecideOnBroadcast(p) \/ ParticipantDie(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendReq(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))

AC1 == \A p, q \in participants :
           (decision[p] = commit /\ decision[q] = abort) => FALSE
AC2 == (\E p \in participants : decision[p] = commit)
           => \A p \in participants : vote[p] = yes
AC3 == (\E p \in participants : decision[p] = abort)
           => (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty
AC4 == (\A p \in participants :
           (decision[p] = commit) ~> (decision[p] = commit) /\ (decision[p] = abort) ~> (decision[p] = abort))

EventualDecision ==
    (\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====