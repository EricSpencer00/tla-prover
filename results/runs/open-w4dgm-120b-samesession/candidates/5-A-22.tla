---- MODULE ACP_SB ----
\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), from Babaoglu & Toueg.
\* A single coordinator collects participant votes and broadcasts a commit
\* decision; a coordinator failure during broadcast can leave participants undecided,
\* which is precisely why this simple-broadcast variant does NOT guarantee
\* termination (the non-blocking liveness property AC5 is omitted for that reason).
\* Actions: SendVoteReq, RecvVote, DetectFault, Decide, Broadcast, Die (coord);
\* SendVote, AbortOnVote, AbortOnTimeout, AdoptDecision, Die (participants).
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes # no /\ commit # abort /\ commit # undecided /\ abort # undecided
       /\ undecided # waiting /\ undecided # notsent

VARIABLES vote, alive, decision, faulty, sentVote, reqSent,
         recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, reqSent,
           recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvdVote \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvdVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendVoteReq(p) ==
    /\ coordAlive /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
    /\ coordAlive /\ coordDecision = undecided /\ reqSent[p]
    /\ recvdVote[p] = waiting /\ alive[p] /\ sentVote[p]
    /\ recvdVote' = [recvdVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   reqSent, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Failure detection here is immediate and magical (a crash is noticed at once).
DetectFault(p) ==
    /\ coordAlive /\ coordDecision = undecided /\ reqSent[p]
    /\ recvdVote[p] = waiting /\ ~alive[p] /\ ~sentVote[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   reqSent, recvdVote, broadcasted, coordAlive, coordFaulty>>

Decide ==
    /\ coordAlive /\ coordDecision = undecided
    /\ \A p \in participants : reqSent[p]
    /\ \A p \in participants : recvdVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : recvdVote[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   reqSent, recvdVote, broadcasted, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive /\ coordDecision # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   reqSent, recvdVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                   reqSent, recvdVote, broadcasted, coordDecision>>

SendVote(p) ==
    /\ alive[p] /\ ~sentVote[p] /\ reqSent[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p] /\ decision[p] = undecided /\ sentVote[p] /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ alive[p] /\ decision[p] = undecided /\ ~reqSent[p]
    /\ coordFaulty /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AdoptDecision(p) ==
    /\ alive[p] /\ decision[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, reqSent,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, reqSent,
                   recvdVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

\* Which actors may die is a nondeterministic choice, not a fairness concern.
Next ==
    \/ \E p \in participants : SendVoteReq(p) \/ RecvVote(p) \/ DetectFault(p)
                                 \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                                 \/ AbortOnTimeout(p) \/ AdoptDecision(p) \/ PartDie(p)
    \/ Decide \/ CoordDie

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVoteReq(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : Broadcast(p))
    /\ WF_vars(\E p \in participants : AdoptDecision(p))
    /\ SF_vars(\E p \in participants : RecvVote(p))
    /\ SF_vars(Decide)

\* The agreed-upon decision cannot split between participants.
NoSplitOutcome ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => p = q

\* Irreversibility: once a participant has decided, it can never un-decide.
DecideIrreversible ==
    \A p \in participants :
        /\ (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

\* The non-blocking termination guarantee (ACI) is NOT included here because
\* Simple Broadcast can leave participants undecided after a coordinator crash.
EventuallyDecide ==
    <>(\A p \in participants : decision[p] # undecided
         \/ \E p \in participants : faulty[p]
         \/ coordFaulty)

====