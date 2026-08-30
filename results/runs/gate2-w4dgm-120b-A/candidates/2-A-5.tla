-------------------------- MODULE ACP_NB --------------------------
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

NoVote == "novote"

VARIABLES coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive,
          coordFaulty, pstate, alive, decision, faulty, voteSent, forwarded

vars == <<coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive,
          coordFaulty, pstate, alive, decision, faulty, voteSent, forwarded>>

TypeOK ==
    /\ coordRequest \in {waiting, yes, no}
    /\ coordVote \in [participants -> {NoVote, yes, no}]
    /\ coordBroadcast \in [participants -> {yes, no}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ pstate \in [participants -> {"preparing", "decided"}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ coordRequest = waiting
    /\ coordVote = [p \in participants |-> NoVote]
    /\ coordBroadcast = [p \in participants |-> no]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ pstate = [p \in participants |-> "preparing"]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordAlive
    /\ coordRequest = waiting
    /\ coordRequest' = yes
    /\ UNCHANGED <<coordVote, coordBroadcast, coordDecision, coordAlive,
                    coordFaulty, pstate, alive, decision, faulty, voteSent,
                    forwarded>>

GetVote(p) ==
    /\ coordAlive
    /\ alive[p]
    /\ coordRequest # waiting
    /\ coordVote[p] = NoVote
    /\ coordVote' = [coordVote EXCEPT ![p] = yes]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordRequest, coordBroadcast, coordDecision, coordAlive,
                    coordFaulty, pstate, alive, decision, faulty, forwarded>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordRequest # waiting
    /\ coordVote[p] = NoVote
    /\ coordVote' = [coordVote EXCEPT ![p] = no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordRequest, coordBroadcast, coordDecision, coordAlive,
                    coordFaulty, pstate, alive, decision, faulty, forwarded>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # NoVote
    /\ coordDecision' = IF (\A p \in participants : coordVote[p] = yes)
                          THEN commit ELSE abort
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                    coordFaulty, pstate, alive, decision, faulty, voteSent,
                    forwarded>>

Broadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast = [p \in participants |-> no]
    /\ coordBroadcast' = [p \in participants |-> coordDecision]
    /\ UNCHANGED <<coordRequest, coordVote, coordDecision, coordAlive,
                    coordFaulty, pstate, alive, decision, faulty, voteSent,
                    forwarded>>

Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    pstate, alive, decision, faulty, voteSent, forwarded>>

SendVote(p) == GetVote(p) \/ DetectFault(p)

PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pstate[p] = "preparing"
    /\ coordBroadcast[p] # no
    /\ forwarded[p][p] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = coordBroadcast[p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty, pstate, alive, decision,
                    faulty, voteSent>>

PreDecideFromForward(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pstate[p] = "preparing"
    /\ forwarded[p][p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ alive[q]
         /\ forwarded[q][p] # notsent
         /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty, pstate, alive, decision,
                    faulty, voteSent>>

Forward(p, q) ==
    /\ alive[p]
    /\ forwarded[p][p] # notsent
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty, pstate, alive, decision,
                    faulty, voteSent>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ pstate[p] = "preparing"
    /\ forwarded[p][p] # notsent
    /\ \A q \in participants : forwarded[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ pstate' = [pstate EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty, alive, faulty, voteSent,
                    forwarded>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordFaulty
    /\ coordAlive
    /\ \A q \in participants : coordBroadcast[q] = no
    /\ \A q \in participants : (q # p) => (faulty[q] \/ forwarded[q][p] = no)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ pstate' = [pstate EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordDecision,
                    coordAlive, coordFaulty, alive, faulty, voteSent,
                    forwarded>>

AbortOnTimeoutAny == \E p \in participants : AbortOnTimeout(p)

DecideAny == \E p \in participants : Decide(p)

DieAny == \E p \in participants : Die

Next ==
    \/ SendRequest \/ MakeDecision \/ Broadcast \/ DieAny \/ AbortOnTimeoutAny
    \/ DecideAny
    \/ \E p \in participants :
         \/ SendVote(p)
         \/ PreDecideFromCoord(p)
         \/ PreDecideFromForward(p)
         \/ Decide(p)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(DecideAny) /\ WF_vars(AbortOnTimeoutAny)
    /\ \A p \in participants : SF_vars(PreDecideFromCoord(p))
    /\ \A p \in participants : SF_vars(PreDecideFromForward(p))
    /\ \A p \in participants : \A q \in participants : SF_vars(Forward(p, q))

Agreement ==
    \A p1, p2 \in participants : (decision[p1] = commit) => (decision[p2] = commit)

CommitValidity ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : coordVote[q] = yes)

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : coordVote[q] = no
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

Irreversibility ==
    \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

DecideEventually ==
    \A p \in participants : (p \in participants) ~> (decision[p] \in {commit, abort})

DecideLiveness == DecideEventually

TypeInvNB == TypeOK
=============================================================================