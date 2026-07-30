---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordRequest, coordVote, coordCast,
          coordDecision, coordAlive, coordFaulty, fwd

vars == << vote, alive, decision, faulty, voted, coordRequest, coordVote,
           coordCast, coordDecision, coordAlive, coordFaulty, fwd >>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ coordRequest \in {waiting, yes, no}
    /\ coordVote \in {waiting, yes, no}
    /\ coordCast \subseteq participants
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> yes]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ coordRequest = waiting
    /\ coordVote = waiting
    /\ coordCast = {}
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordAlive
    /\ coordRequest = waiting
    /\ coordRequest' = yes
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordVote, coordCast,
                    coordDecision, coordAlive, coordFaulty, fwd >>

SendVote(p) ==
    /\ alive[p]
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty, coordRequest, coordVote,
                    coordCast, coordDecision, coordAlive, coordFaulty, fwd >>

DetectCoordFault ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest,
                    coordVote, coordCast, coordDecision, fwd >>

MakeDecision ==
    /\ coordAlive
    /\ coordVote # waiting
    /\ coordCast = participants
    /\ coordDecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest, coordVote,
                    coordCast, coordAlive, coordFaulty, fwd >>

BroadcastCoord(c) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ c \notin coordCast
    /\ coordCast' = coordCast \cup {c}
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest, coordVote,
                    coordDecision, coordAlive, coordFaulty, fwd >>

PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordDecision # undecided
    /\ p \in coordCast
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest,
                    coordVote, coordCast, coordDecision, coordAlive, coordFaulty >>

PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
         /\ fwd[q][p] # notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest,
                    coordVote, coordCast, coordDecision, coordAlive, coordFaulty >>

Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest,
                    coordVote, coordCast, coordDecision, coordAlive, coordFaulty >>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] = fwd[p][p]
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << vote, alive, faulty, voted, coordRequest, coordVote,
                    coordCast, coordDecision, coordAlive, coordFaulty, fwd >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ ~voted[p]
    /\ coordAlive
    /\ coordVote = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, voted, coordRequest, coordVote,
                    coordCast, coordDecision, coordAlive, coordFaulty, fwd >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : q \notin coordCast
    /\ \A q \in participants : \A r \in participants :
         ~(~alive[q] /\ fwd[q][r] # notsent /\ r \in participants)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, voted, coordRequest, coordVote,
                    coordCast, coordDecision, coordAlive, coordFaulty, fwd >>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, voted, coordRequest, coordVote, coordCast,
                    coordDecision, coordAlive, coordFaulty, fwd >>

CoordDie == /\ coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
            /\ UNCHANGED << vote, alive, decision, faulty, voted, coordRequest,
                            coordVote, coordCast, coordDecision, fwd >>

Next ==
    \/ SendRequest
    \/ \E p \in participants : SendVote(p)
    \/ DetectCoordFault
    \/ MakeDecision
    \/ \E c \in participants : BroadcastCoord(c)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordDie

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
    (\E p \in participants : decision[p] = commit) =>
        (\A p \in participants : vote[p] = yes)

AC3 ==
    (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

AC4 ==
    \A p \in participants :
        (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

AC3Liveness ==
    <>(\A p \in participants : decision[p] # undecided \/ faulty[p]) \/ coordFaulty

AC5 ==
    \A p \in participants : (decision[p] # undecided) ~> TRUE

====