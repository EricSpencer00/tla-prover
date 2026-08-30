---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordReq, coordVote, coordBroadcast, coordDecision,
          coordAlive, coordFaulty, forwarding

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordReq, coordVote, coordBroadcast, coordDecision,
          coordAlive, coordFaulty, forwarding>>

\* forwarding[p][q] holds what p has a pre-decision for, and whether p has
\* already forwarded that pre-decision to q (a per-destination flag).
Init ==
    /\ participantVote = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> waiting]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantSent = [p \in participants |-> FALSE]
    /\ coordReq = [p \in participants |-> undecided]
    /\ coordVote = [p \in participants |-> undecided]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

SendCoordReq(p) ==
    /\ coordAlive
    /\ coordReq[p] = undecided
    /\ coordReq' = [coordReq EXCEPT ![p] = yes]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty,
                   forwarding>>

GetVote(p) ==
    /\ coordAlive
    /\ coordReq[p] = yes
    /\ participantAlive[p]
    /\ participantVote[p] = undecided
    /\ participantVote' = [participantVote EXCEPT ![p] = yes]
    /\ coordVote' = [coordVote EXCEPT ![p] = yes]
    /\ UNCHANGED <<participantAlive, participantDecision, participantFaulty,
                   participantSent, coordReq, coordBroadcast, coordDecision,
                   coordAlive, coordFaulty, forwarding>>

DetectFault(p) ==
    /\ participantAlive[p]
    /\ participantFaulty[p] = FALSE
    /\ participantVote[p] = undecided
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantSent, coordReq, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forwarding>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] = yes
    /\ coordDecision' = commit
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordAlive, coordFaulty, forwarding>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordDecision, coordAlive, coordFaulty, forwarding>>

Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, forwarding>>

SendVote(p) ==
    /\ participantAlive[p]
    /\ participantVote[p] = undecided
    /\ participantVote' = [participantVote EXCEPT ![p] = yes]
    /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantAlive, participantDecision, participantFaulty,
                   coordReq, coordVote, coordBroadcast, coordDecision,
                   coordAlive, coordFaulty, forwarding>>

AbortOnVote ==
    /\ \E p \in participants : participantVote[p] = no
    /\ coordDecision = undecided
    /\ coordDecision' = abort
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordAlive, coordFaulty, forwarding>>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = waiting
    /\ ~coordAlive
    /\ \A q \in participants : coordBroadcast[q] \in {notsent, coordDecision}
    /\ \A q \in participants : ~(~participantAlive[q] /\ forwarding[q][p] \in {commit, abort})
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent, coordReq, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forwarding>>

\* New: participant p adopts a pre-decision already stored in its own entry.
PreDecideFromCoordinator(p) ==
    /\ participantAlive[p]
    /\ forwarding[p][p] = notsent
    /\ coordBroadcast[p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordBroadcast[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* New: participant p adopts a pre-decision forwarded by a peer q.
PreDecideFromPeer(p) ==
    /\ participantAlive[p]
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
         /\ p # q
         /\ forwarding[q][p] \in {commit, abort}
         /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* New: forward a stored pre-decision to a peer before finalizing locally.
Forward(p, q) ==
    /\ participantAlive[p]
    /\ p # q
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = waiting
    /\ forwarding[p][p] \in {commit abort}
    /\ \A q \in participants : q # p => forwarding[p][q] = forwarding[p][p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent, coordReq, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forwarding>>

\* New: a faulty participant may still forward a decision it had already stored.
ForwardByFault(p, q) ==
    /\ ~participantAlive[p]
    /\ p # q
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, forwarding>>

Next ==
    \/ \E p \in participants : SendCoordReq(p)
    \/ \E p \in participants : GetVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ Die
    \/ \E p \in participants : SendVote(p)
    \/ AbortOnVote
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : PreDecideFromCoordinator(p)
    \/ \E p \in participants : PreDecideFromPeer(p)
    \/ \E p \in participants, q \in participants : Forward(p q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants, q \in participants : ForwardByFault(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendCoordReq(p))
    /\ WF_vars(\E p \in participants : GetVote(p))
    /\ SF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
    /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))

TypeInvNB ==
    /\ participantVote \in [participants -> {yes, no, undecided}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {waiting, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantSent \in [participants -> {FALSE, TRUE}]
    /\ coordReq \in [participants -> {yes, no, undecided}]
    /\ coordVote \in [participants -> {yes, no, undecided}]
    /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* Safety: agreement, validity, and irrevocability.
AC1 ==
    \A p, q \in participants :
        (participantDecision[p] = commit /\ participantDecision[q] = abort) => FALSE

AC2 ==
    \A p \in participants : participantDecision[p] = commit => \A q \in participants : participantVote[q] = yes

AC3 ==
    \A p \in participants :
        participantDecision[p] = abort =>
            \/ \E q \in participants : participantVote[q] = no
            \/ \E q \in participants : participantFaulty[q]
            \/ coordFaulty

AC4 ==
    \A p \in participants :
        (participantDecision[p] = commit \/ participantDecision[p] = abort) =>
            (~coordAlive /\ participantDecision[p] = commit) \/ (coordDecision = commit /\ participantDecision[p] = commit)

\* Liveness: always eventually everyone decides or a fault is uncovered.
AC3Live == <>(\A p \in participants : participantDecision[p] # waiting \/ \E q \in participants : participantFaulty[q] \/ coordFaulty)

\* Liveness: every non-faulty participant eventually reaches a decision.
AC5 == \A p \in participants : (participantAlive[p] ~> (participantDecision[p] # waiting))

====