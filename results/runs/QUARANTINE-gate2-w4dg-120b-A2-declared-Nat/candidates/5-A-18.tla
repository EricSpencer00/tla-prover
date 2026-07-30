---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
    participants,
    yes,
    no,
    undecided,
    commit,
    abort,
    waiting,
    notsent

VARIABLES
    vote,
    alive,
    decision,
    faulty,
    sentvote,
    requestsent,
    recvvote,
    broadcastsent,
    coorddecision,
    coordalive,
    coordfaulty

vars == <<
    vote,
    alive,
    decision,
    faulty,
    sentvote,
    requestsent,
    recvvote,
    broadcastsent,
    coorddecision,
    coordalive,
    coordfaulty
>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in BOOLEAN
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in BOOLEAN
    /\ sentvote \in [participants -> BOOLEAN]
    /\ requestsent \in [participants -> BOOLEAN]
    /\ recvvote \in [participants -> {yes, no, waiting}]
    /\ broadcastsent \in [participants -> {yes, no, notsent}]
    /\ coorddecision \in {undecided, commit, abort}
    /\ coordalive \in BOOLEAN
    /\ coordfaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = TRUE
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = FALSE
    /\ sentvote = [p \in participants |-> FALSE]
    /\ requestsent = [p \in participants |-> FALSE]
    /\ recvvote = [p \in participants |-> waiting]
    /\ broadcastsent = [p \in participants |-> notsent]
    /\ coorddecision = undecided
    /\ coordalive = TRUE
    /\ coordfaulty = FALSE

\* Coordinator actions ---------------------------------------------------------

SendRequest(p) ==
    /\ coordalive
    /\ ~requestsent[p]
    /\ requestsent' = [requestsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

ReceiveVote(p) ==
    /\ coordalive
    /\ coorddecision = undecided
    /\ \A q \in participants: requestsent[q]
    /\ recvvote[p] = waiting
    /\ sentvote[p]
    /\ recvvote' = [recvvote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, requestsent,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

DetectFault(p) ==
    /\ coordalive
    /\ coorddecision = undecided
    /\ \A q \in participants: requestsent[q]
    /\ recvvote[p] = waiting
    /\ \A q \in participants: ~sentvote[q]
    /\ coorddecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, requestsent,
                    recvvote, broadcastsent, coordalive, coordfaulty>>

MakeDecision ==
    /\ coordalive
    /\ coorddecision = undecided
    /\ \A p \in participants: recvvote[p] # waiting
    /\ coorddecision' = IF \A p \in participants: recvvote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, requestsent,
                    recvvote, broadcastsent, coordalive, coordfaulty>>

\* Simple broadcast: a single outstanding send, which is what blocks.
BroadcastDecision(p) ==
    /\ coordalive
    /\ coorddecision # undecided
    /\ broadcastsent[p] = notsent
    /\ broadcastsent' = [broadcastsent EXCEPT ![p] = coorddecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, requestsent,
                    recvvote, coorddecision, coordalive, coordfaulty>>

CoordDie ==
    /\ coordalive
    /\ coordalive' = FALSE
    /\ coordfaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, requestsent,
                    recvvote, broadcastsent, coorddecision, coordalive, coordfaulty>>

\* Participant actions --------------------------------------------------------

SendVote(p) ==
    /\ alive
    /\ requestsent[p]
    /\ ~sentvote[p]
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, requestsent, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

DecideAbortOnVote(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ sentvote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, requestsent, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

DecideAbortOnTimeout(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ ~coordalive
    /\ ~requestsent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, requestsent, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

DecideOnBroadcast(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ broadcastsent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcastsent[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentvote, requestsent, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

ParticipantDie(p) ==
    /\ alive
    /\ alive' = FALSE
    /\ faulty' = TRUE
    /\ UNCHANGED <<vote, decision, sentvote, requestsent, recvvote,
                    broadcastsent, coorddecision, coordalive, coordfaulty>>

Next ==
    \/ \E p \in participants: SendRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: DecideAbortOnVote(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ \E p \in participants: DecideAbortOnTimeout(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants: SendVote(p))
    /\ WF_vars(\E p \in participants: DecideAbortOnVote(p))
    /\ WF_vars(\E p \in participants: DecideOnBroadcast(p))
    /\ WF_vars(MakeDecision)

\* Safety properties ----------------------------------------------------------

AC1 == \A p1, p2 \in participants:
          (decision[p1] = commit /\ decision[p2] = abort) => FALSE

AC2 == \A p \in participants: decision[p] = commit => \A p2 \in participants: vote[p2] = yes

AC3 == \A p \in participants: decision[p] = abort =>
          \/ \E p2 \in participants: vote[p2] = no
          \/ faulty
          \/ coordfaulty

AC4 == \A p \in participants:
          (decision[p] = commit => decision' [p] = commit)
          /\ (decision[p] = abort => decision' [p] = abort)

\* Liveness property (the blocking one) ---------------------------------------

AC3Eventual == <>(\A p \in participants: decision[p] # undecided \/ faulty \/ coordfaulty)

====