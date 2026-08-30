---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC

TypeInv ==
    /\ voteFor \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decidedP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ sentReq \in [participants -> {notsent, waiting}]
    /\ recVote \in [participants -> {waiting, yes, no}]
    /\ sentDecision \in [participants -> {notsent, waiting}]
    /\ decision \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ voteFor \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decidedP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ sentReq = [p \in participants |-> notsent]
    /\ recVote = [p \in participants |-> waiting]
    /\ sentDecision = [p \in participants |-> notsent]
    /\ decision = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* Coordinator: send a vote request to a participant.
SendVoteReq(p) ==
    /\ aliveC
    /\ sentReq[p] = notsent
    /\ sentReq' = [sentReq EXCEPT ![p] = waiting]
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, recVote, sentDecision, decision, aliveC, faultyC>>

\* Coordinator: receive a vote from a participant that has sent it.
RecvVote(p) ==
    /\ aliveC
    /\ decision = undecided
    /\ sentReq[p] = waiting
    /\ sentVote[p]
    /\ recVote[p] = waiting
    /\ recVote' = [recVote EXCEPT ![p] = voteFor[p]]
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, sentDecision, decision, aliveC, faultyC>>

\* Coordinator: detect a participant fault and abort instead.
DetectFault(p) ==
    /\ aliveC
    /\ decision = undecided
    /\ sentReq[p] = waiting
    /\ recVote[p] = waiting
    /\ ~aliveP[p]
    /\ decision' = abort
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, sentDecision, aliveC, faultyC>>

\* Coordinator: decide commit only when every vote is yes; otherwise abort.
MakeDecision ==
    /\ aliveC
    /\ decision = undecided
    /\ \A p \in participants : sentReq[p] = waiting /\ recVote[p] # waiting
    /\ decision' = IF (\A p \in participants : recVote[p] = yes) THEN commit ELSE abort
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, sentDecision, aliveC, faultyC>>

\* Coordinator: broadcast the decision to a participant (simple broadcast, so it can crash mid-way).
Broadcast(p) ==
    /\ aliveC
    /\ decision # undecided
    /\ sentDecision[p] = notsent
    /\ sentDecision' = [sentDecision EXCEPT ![p] = waiting]
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, decision, aliveC, faultyC>>

\* Coordinator: the coordinator can crash and become faulty.
DieC ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, sentDecision, decision>>

\* Participant: send its vote to the coordinator once it receives the request.
SendVote(p) ==
    /\ aliveP[p]
    /\ sentReq[p] = waiting
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteFor, aliveP, decidedP, faultyP, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* Participant: abort unilaterally if its own vote is no.
AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decidedP[p] = undecided
    /\ sentVote[p]
    /\ voteFor[p] = no
    /\ decidedP' = [decidedP EXCEPT ![p] = abort]
    /\ UNCHANGED <<voteFor, aliveP, faultyP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* Participant: abort by timeout if the coordinator died without requesting.
AbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ decidedP[p] = undecided
    /\ ~aliveC
    /\ sentReq[p] = notsent
    /\ decidedP' = [decidedP EXCEPT ![p] = abort]
    /\ UNCHANGED <<voteFor, aliveP, faultyP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* Participant: decide based on the coordinator's broadcast.
Decide(p) ==
    /\ aliveP[p]
    /\ decidedP[p] = undecided
    /\ sentDecision[p] = waiting
    /\ decidedP' = [decidedP EXCEPT ![p] = decision]
    /\ UNCHANGED <<voteFor, aliveP, faultyP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* Participant: a participant can crash and become faulty.
DieP(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteFor, decidedP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* Coordinated broadcast: one participant gets its decision at a time (asynchronous
\* step, not a simultaneous broadcast to everybody).
BroadcastSome == \E p \in participants : Broadcast(p)

\* Participant progress: one participant at a time goes from undecided to a final
\* decision (applies to abort-on-vote, abort-on-timeout, and decide actions).
DecideSome == \E p \in participants : AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p)

Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ BroadcastSome
    \/ DieC
    \/ \E p \in participants : SendVote(p)
    \/ DecideSome
    \/ \E p \in participants : DieP(p)

Spec == Init /\ [][Next]_<<voteFor, aliveP, decidedP, faultyP, sentVote, sentReq, recVote, sentDecision, decision, aliveC, faultyC>>

\* No two participants ever decide differently.
Agree ==
    \A p, q \in participants :
        (decidedP[p] = commit /\ decidedP[q] = abort) => FALSE

\* If anyone commits, then every participant voted yes.
CommitValid ==
    (\E p \in participants : decidedP[p] = commit) => (\A p \in participants : voteFor[p] = yes)

\* If anyone aborts, then it is justified by a no vote or a failure.
AbortValid ==
    (\E p \in participants : decidedP[p] = abort) =>
        (\E p \in participants : voteFor[p] = no \/ faultyP[p] \/ faultyC)

\* A participant decides at most once: commit is absorbing, and abort is absorbing.
DecideOnce ==
    \A p \in participants : (decidedP[p] = commit) ~> (decidedP[p] = commit)

\* At least one participant decides, or a failure occurs.
DecideOrFail == <>(\E p \in participants : decidedP[p] # undecided \/ faultyC)

====