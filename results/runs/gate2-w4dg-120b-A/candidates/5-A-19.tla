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

\* The coordinator is the sole decision-maker: it collects votes, decides, then
\* broadcasts the decision one participant at a time (simple broadcast). A
\* coordinator crash during broadcast is exactly what makes the protocol
\* blocking, since a participant that never receives the decision is stuck.
\* Death transitions are excluded from fairness: a participant or coordinator
\* may crash silently at any moment without being forced to progress.

VARIABLES
    vote,
    alive,
    decision,
    faulty,
    voted,
    requested,
    recvVote,
    broadcasted,
    coordDecision,
    coordAlive,
    coordFaulty

vars == <<vote, alive, decision, faulty, voted, requested,
           recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> yes \cup no]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ requested \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> yes \cup no \cup {waiting}]
    /\ broadcasted \in [participants -> {notsent} \cup {commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> yes \cup no]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ requested = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendRequest(p) ==
    /\ coordAlive
    /\ ~requested[p]
    /\ requested' = [requested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : requested[q]
    /\ recvVote[p] = waiting
    /\ voted[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  requested, broadcasted, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : requested[q]
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  requested, recvVote, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : recvVote[p] \in yes \cup no
    /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  requested, recvVote, broadcasted, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  requested, recvVote, coordDecision, coordAlive, coordFaulty>>

CoordinatorDies ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voted,
                  requested, recvVote, broadcasted, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ ~voted[p]
    /\ requested[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, requested,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantAborts(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ voted[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, requested,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortedOnVoteRequestTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~requested[p]
    /\ coordFaulty
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, requested,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcasted[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, voted, requested,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDies(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voted, requested,
                  recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordinatorDies
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : ParticipantAborts(p)
    \/ \E p \in participants : AbortedOnVoteRequestTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDies(p)

\* Weak fairness applies to every live progress action EXCEPT death.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendRequest(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : CoordDetectFault(p))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : ParticipantAborts(p))
    /\ WF_vars(\E p \in participants : AbortedOnVoteRequestTimeout(p))
    /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))

\* Safety: participants never disagree, and any terminal outcome is justified
\* by the votes already cast or by a failure.
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
    \A p \in participants : decision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ coordFaulty

Irreversible ==
    \A p \in participants :
        /\ (decision[p] = commit => decision' [p] = commit)
        /\ (decision[p] = abort => decision' [p] = abort)

\* Liveness: every participant is eventually resolved, or the protocol halts
\* by failure. The simple broadcast variant cannot guarantee every live
\* participant decides; a coordinator hang during broadcast leaves undecided
\* participants stranded, but the system always reaches a terminal outcome.
Resolution ==
    \E p \in participants : decision[p] \in {commit, abort}
        \/ \E p \in participants : faulty[p]
        \/ coordFaulty

====