---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo
VARIABLES alive, faulty, vote, pdecision, sentVote

vars == <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
          alive, faulty, vote, pdecision, sentVote>>

TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentReq \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSentTo \in [participants -> {notsent, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSentReq = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSentTo = [p \in participants |-> notsent]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]

SendReq ==
    /\ coordAlive
    /\ \E p \in participants :
         /\ ~coordSentReq[p]
         /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRecv, coordSentTo,
                  alive, faulty, vote, pdecision, sentVote>>

ReceiveVote ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordSentReq[p]
    /\ \E p \in participants :
         /\ coordRecv[p] = waiting
         /\ sentVote[p]
         /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordSentTo,
                  alive, faulty, vote, pdecision, sentVote>>

DetectFault ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordSentReq[p]
    /\ \E p \in participants :
         /\ coordRecv[p] = waiting
         /\ ~alive[p]
         /\ ~sentVote[p]
         /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, pdecision, sentVote>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRecv[p] \in {yes, no}
    /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, pdecision, sentVote>>

Broadcast ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
         /\ coordSentTo[p] = notsent
         /\ coordSentTo' = [coordSentTo EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv,
                  alive, faulty, vote, pdecision, sentVote>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, pdecision, sentVote>>

SendVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ coordSentReq[p]
         /\ ~sentVote[p]
         /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, pdecision>>

AbortOnNo ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pdecision[p] = undecided
         /\ sentVote[p]
         /\ vote[p] = no
         /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, sentVote>>

AbortNoReq ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pdecision[p] = undecided
         /\ ~coordSentReq[p]
         /\ coordFaulty
         /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, sentVote>>

DecideBroadcast ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pdecision[p] = undecided
         /\ coordSentTo[p] \in {commit, abort}
         /\ pdecision' = [pdecision EXCEPT ![p] = coordSentTo[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
                  alive, faulty, vote, sentVote>>

Die ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSentReq, coordRecv, coordSentTo,
                  vote, pdecision, sentVote>>

Next ==
    \/ SendReq \/ ReceiveVote \/ DetectFault \/ MakeDecision \/ Broadcast \/ CoordDie
    \/ SendVote \/ AbortOnNo \/ AbortNoReq \/ DecideBroadcast \/ Die

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SendReq) /\ WF_vars(ReceiveVote) /\ WF_vars(MakeDecision)
        /\ WF_vars(Broadcast) /\ WF_vars(SendVote) /\ WF_vars(AbortOnNo)
        /\ WF_vars(DecideBroadcast)

AC1 ==
    \A p \in participants, q \in participants :
        (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

AC2 ==
    \E p \in participants : pdecision[p] = commit =>
        \A q \in participants : vote[q] = yes

AC3 ==
    \E p \in participants : pdecision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty

AC4 ==
    \A p \in participants :
        /\ (pdecision[p] = commit => (pdecision' [p] = commit))
        /\ (pdecision[p] = abort => (pdecision' [p] = abort))

EventualDecision ==
    (\A p \in participants : pdecision[p] \in {commit, abort})
        \/ (\E p \in participants : faulty[p])
        \/ coordFaulty

====