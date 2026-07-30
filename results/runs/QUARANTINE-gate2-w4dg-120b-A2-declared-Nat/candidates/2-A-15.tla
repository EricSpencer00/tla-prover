---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordRequest, coordVote, coordBroadcast, coordDecide
VARIABLES coordAlive, coordFaulty, partVote, partAlive, partDecision
VARIABLES partFaulty, hasVoted, fwdTable

vars == <<coordRequest, coordVote, coordBroadcast, coordDecide,
          coordAlive, coordFaulty, partVote, partAlive,
          partDecision, partFaulty, hasVoted, fwdTable>>

\* The reliable broadcast is implemented by a forwarding table per participant:
\* fwdTable[p][q] = the status p has forwarded to q (notsent, commit, abort).
\* A participant must forward to everybody before finalizing its decision.
\* The table also holds each participant's own pre-decision at its own index.

TypeInvNB ==
    /\ coordRequest \in {waiting, yes, no}
    /\ coordVote \in {undecided, yes, no}
    /\ coordBroadcast \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ partVote \in [participants -> {yes, no, undecided}]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partDecision \in [participants -> {undecided, commit, abort}]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ hasVoted \in [participants -> BOOLEAN]
    /\ fwdTable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ coordRequest = waiting
    /\ coordVote = undecided
    /\ coordBroadcast = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ partVote = [p \in participants |-> undecided]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ hasVoted = [p \in participants |-> FALSE]
    /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: send (the request), collect a vote, detect a fault,
\* decide, broadcast, and crash. All inherited from the base protocol.
CoordSend(p) ==
    /\ coordAlive
    /\ coordRequest = waiting
    /\ coordRequest' = partVote[p]
    /\ UNCHANGED <<coordVote, coordBroadcast, coordAlive, coordFaulty,
                  partVote, partAlive, partDecision, partFaulty, hasVoted,
                  fwdTable>>

CoordVote ==
    /\ coordAlive
    /\ coordVote = undecided
    /\ coordVote' = coordRequest
    /\ UNCHANGED <<coordRequest, coordBroadcast, coordAlive, coordFaulty,
                  partVote, partAlive, partDecision, partFaulty, hasVoted,
                  fwdTable>>

CoordFault ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast,
                  partVote, partAlive, partDecision, partFaulty,
                  hasVoted, fwdTable>>

CoordDecide ==
    /\ coordAlive
    /\ coordVote # undecided
    /\ coordBroadcast' = coordVote
    /\ UNCHANGED <<coordRequest, coordVote, coordAlive, coordFaulty,
                  partVote, partAlive, partDecision, partFaulty,
                  hasVoted, fwdTable>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordBroadcast # undecided
    /\ fwdTable[p][p] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordBroadcast]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partDecision,
                  partFaulty, hasVoted>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast,
                  partVote, partAlive, partDecision, partFaulty,
                  hasVoted, fwdTable>>

\* Participant actions: send a vote, abort on a no vote or on timeout, and
\* the reliable-broadcast steps (pre-decide from coordinator, pre-decide
\* from a peer, forward to a peer, and finalize once all peers are covered).
SendVote(p) ==
    /\ partAlive[p]
    /\ partVote[p] = undecided
    /\ partVote' = [partVote EXCEPT ![p] = yes]
    /\ hasVoted' = [hasVoted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partAlive, partDecision, partFaulty,
                  fwdTable>>

AbortOnVote(p) ==
    /\ partAlive[p]
    /\ partVote[p] = no
    /\ partDecision[p] = undecided
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partFaulty,
                  hasVoted, fwdTable>>

AbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ coordFaulty
    /\ coordBroadcast = undecided
    /\ \A q \in participants : fwdTable[q][p] = notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partFaulty,
                  hasVoted, fwdTable>>

PredecideCoord(p) ==
    /\ partAlive[p]
    /\ coordBroadcast # undecided
    /\ fwdTable[p][p] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordBroadcast]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partDecision,
                  partFaulty, hasVoted>>

PredecideForward(p) ==
    /\ partAlive[p]
    /\ fwdTable[p][p] = notsent
    /\ \E q \in participants :
         /\ partAlive[q]
         /\ fwdTable[q][p] # notsent
         /\ fwdTable' = [fwdTable EXCEPT ![p][p] = fwdTable[q][p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partDecision,
                  partFaulty, hasVoted>>

Forward(p, q) ==
    /\ partAlive[p]
    /\ fwdTable[p][p] # notsent
    /\ fwdTable[p][q] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partDecision,
                  partFaulty, hasVoted>>

Decide(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ \A q \in participants : fwdTable[p][q] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = fwdTable[p][p]]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partAlive, partFaulty,
                  hasVoted, fwdTable>>

Die(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordRequest, coordVote, coordBroadcast, coordAlive,
                  coordFaulty, partVote, partDecision, hasVoted,
                  fwdTable>>

Next ==
    \/ \E p \in participants :
         \/ CoordSend(p) \/ CoordBroadcast(p) \/ SendVote(p)
         \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ PredecideCoord(p)
         \/ PredecideForward(p) \/ Decide(p) \/ Die(p)
         \/ \E q \in participants : Forward(p, q)
    \/ CoordVote \/ CoordFault \/ CoordDecide \/ CoordDie

\* Weak fairness on all progress steps except the death steps.
SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : CoordSend(p))
    /\ WF_vars(\E p \in participants : CoordVote)
    /\ WF_vars(\E p \in participants : CoordDecide)
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : PredecideCoord(p))
    /\ WF_vars(\E p \in participants : PredecideForward(p))
    /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))

\* Safety: no two participants ever decide differently (AC1), a commit
\* implies unanimous yes (AC2), an abort has a no vote, a faulty participant,
\* or a faulty coordinator backing it up (AC3), and decisions are permanent (AC4).
AC1 == \A p, q \in participants :
           (partDecision[p] = commit /\ partDecision[q] = abort) => FALSE

AC2 == \A p \in participants :
           partDecision[p] = commit => \A q \in participants : partVote[q] = yes

AC3 == \A p \in participants :
           partDecision[p] = abort =>
             \/ \E q \in participants : partVote[q] = no
             \/ \E q \in participants : partFaulty[q]
             \/ coordFaulty

AC4 == \A p \in participants :
           partDecision[p] # undecided => partDecision' = [partDecision EXCEPT ![p] = partDecision[p]]

\* Liveness: the extended set AC3 (termination or a fault) plus the
\* non-blocking guarantee that every non-faulty participant decides.
AC3 == <>(\A p \in participants : partDecision[p] # undecided \/ partFaulty[p] \/ coordFaulty)

AC5 == \A p \in participants : (partAlive[p] /\ partDecision[p] = undecided) ~> partDecision[p] # undecided

====