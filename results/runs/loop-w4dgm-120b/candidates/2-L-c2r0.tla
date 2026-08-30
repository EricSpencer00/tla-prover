---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends the simple broadcast protocol ACP-SB by adding a reliable
\* broadcast forward: each participant keeps a forwarding table recording
\* what decision (if any) it has received and which participants it has
\* already forwarded that decision to.

VARIABLES vote, alive, decision, faulty, voteSent, coordAlive, coordFaulty,
          forwarded, predecided

vars == <<vote, alive, decision, faulty, voteSent, coordAlive,
           coordFaulty, forwarded, predecided>>

TypeOK ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ predecided \in [participants -> {commit, abort, waiting}]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
    /\ predecided = [p \in participants |-> waiting]

SendVote(p) ==
    /\ coordAlive /\ alive[p] /\ vote[p] = undecided /\ ~voteSent[p]
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, coordAlive, coordFaulty,
                   forwarded, predecided>>

\* The coordinator abandons a request for which no participant voted yes,
\* and also abandons a request when some participant is already deemed
\* faulty, so it never waits on a lost participant.
AbortOnVote(p) ==
    /\ coordAlive /\ vote[p] = no /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordAlive, coordFaulty,
                   forwarded, predecided>>

AbortOnTimeout(p) ==
    /\ coordAlive /\ decision[p] = waiting
    /\ \A q \in participants : ~alive[q] \/ vote[q] # undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordAlive, coordFaulty,
                   forwarded, predecided>>

\* The coordinator only decides on a request that every participant voted
\* yes on and that has not already been decided.
Decide(p) ==
    /\ coordAlive /\ decision[p] = waiting
    /\ \A q \in participants : vote[q] = yes
    /\ decision' = [decision EXCEPT ![p] = commit]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordAlive, coordFaulty,
                   forwarded, predecided>>

Broadcast(p, q) ==
    /\ coordAlive /\ decision[p] = commit /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = commit]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordAlive,
                   coordFaulty, predecided>>
BroadcastAbort(p, q) ==
    /\ coordAlive /\ decision[p] = abort /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordAlive,
                   coordFaulty, predecided>>

\* New action: upon receiving a pre-decision from the coordinator, a
\* participant stores it in its own forwarding table and will now forward
\* it to everyone else before finalizing.
PreDecideFromCoord(p) ==
    /\ alive[p] /\ predecided[p] = waiting /\ forwarded[p][p] # notsent
    /\ predecided' = [predecided EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordAlive,
                   coordFaulty, forwarded>>

PreDecideFromPeer(p) ==
    /\ alive[p] /\ predecided[p] = waiting
    /\ \E q \in participants :
         /\ forwarded[q][p] # notsent
         /\ predecided' = [predecided EXCEPT ![p] = forwarded[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordAlive,
                   coordFaulty, forwarded>>

\* New action: a participant forwards its pre-decision to another
\* participant that has not yet received it.
Forward(p, q) ==
    /\ alive[p] /\ predecided[p] # waiting /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = predecided[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordAlive,
                   coordFaulty, predecided>>

\* New action: a participant finalizes its own decision only once it has
\* forwarded its pre-decision to every other participant.
DecideNB(p) ==
    /\ alive[p] /\ predecided[p] # waiting
    /\ \A q \in participants : forwarded[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = predecided[p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordAlive,
                   coordFaulty, forwarded, predecided>>

AbortNoVote(p) ==
    /\ alive[p] /\ decision[p] = waiting
    /\ coordFaulty /\ predecided[p] = waiting
    /\ \A q \in participants : forwarded[q][p] = notsent
    /\ \A q \in participants : ~alive[q] \/ voteSent[q]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordAlive, coordFaulty,
                   forwarded, predecided>>

Die(p) ==
    /\ alive[p] /\ coordAlive
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, coordAlive, coordFaulty,
                   forwarded, predecided>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   forwarded, predecided>>

Next ==
    \/ \E p \in participants :
         \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p)
         \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p) \/ DecideNB(p)
         \/ AbortNoVote(p) \/ Die(p)
         \/ \E q \in participants : Broadcast(p, q) \/ BroadcastAbort(p, q)
                                   \/ Forward(p, q)
    \/ CoordDie

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
    /\ WF_vars(\E p \in participants : DecideNB(p))

\* Safety: atomicity and agreement (no contradictory decisions, and every
\* decision is backed by unanimous yes-votes or a failure).
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes
AC3 == \A p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no \/ faulty[q]) \/ coordFaulty
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p] = decision[p]

\* Liveness: all requests are eventually decided, and every non-faulty
\* participant eventually decides, thanks to reliable forwarding.
EventualDecision == <>(\A p \in participants : decision[p] # waiting \/ coordFaulty)
AC5 == \A p \in participants : (alive[p] /\ predecided[p] = waiting) ~> decision[p] # waiting

SpecProperties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ EventualDecision /\ AC5

Spec == SpecNB /\ SpecProperties

====