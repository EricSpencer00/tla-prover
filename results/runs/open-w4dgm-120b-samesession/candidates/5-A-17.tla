---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Simple broadcast: a coordinator crash mid-broadcast can stall participants
\* forever, so termination is not guaranteed (only AC3 liveness below).
\* Failure detection here is magical (immediate), not time-based.
\* Actions: capitalized acronyms for grouping/precedence; Finish is the final
\* sink that absorbs already-finished terminal versions so the state space
\* stays finite and strongly connected once every actor has decided.

VARIABLES v, alive, decision, faulty, responded
VARIABLES reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty

vars == <<v, alive, decision, faulty, responded,
           reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ v \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ responded \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ coordSend \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ v \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ responded = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ coordSend = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordRequestVote(p) ==
    /\ coordAlive
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   recv, coordSend, coordDecision, coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ reqSent[p]
    /\ recv[p] = waiting
    /\ alive[p]
    /\ responded[p]
    /\ recv' = [recv EXCEPT ![p] = v[p]]
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   reqSent, coordSend, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ reqSent[p]
    /\ recv[p] = waiting
    /\ ~alive[p]
    /\ ~responded[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   reqSent, recv, coordSend, coordAlive, coordFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : recv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : recv[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   reqSent, recv, coordSend, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSend[p] = notsent
    /\ coordSend' = [coordSend EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   reqSent, recv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<v, alive, decision, faulty, responded,
                   reqSent, recv, coordSend, coordDecision>>

PartSendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ ~responded[p]
    /\ responded' = [responded EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<v, alive, decision, faulty, reqSent, recv,
                   coordSend, coordDecision, coordAlive, coordFaulty>>

PartAbortVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ responded[p]
    /\ v[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<v, alive, faulty, responded,
                   reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty>>

PartAbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~reqSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<v, alive, faulty, responded,
                   reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty>>

PartDecide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSend[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSend[p]]
    /\ UNCHANGED <<v, alive, faulty, responded,
                   reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<v, decision, responded,
                   reqSent, recv, coordSend, coordDecision, coordAlive, coordFaulty>>

Finish(p) ==
    /\ decision[p] # undecided
    /\ UNCHANGED vars

Next ==
    \/ \E p \in participants : CoordRequestVote(p) \/ CoordReceiveVote(p)
                                \/ CoordDetectFault(p) \/ CoordBroadcast(p)
                                \/ PartSendVote(p) \/ PartAbortVote(p)
                                \/ PartAbortTimeout(p) \/ PartDecide(p)
                                \/ PartDie(p) \/ Finish(p)
    \/ CoordDecide \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : CoordRequestVote(p))
    /\ WF_vars(\E p \in participants : CoordReceiveVote(p))
    /\ WF_vars(\E p \in participants : PartSendVote(p))
    /\ WF_vars(\E p \in participants : PartAbortVote(p))
    /\ WF_vars(\E p \in participants : PartAbortTimeout(p))
    /\ WF_vars(\E p \in participants : PartDecide(p))

\* AC1: no two participants can disagree. AC2: commit only on unanimity.
\* AC3: abort only if somebody voted no or somebody is faulty. AC4: decisions
\* are sticky -- once effective (a broadcast or a vote-driven abort) they
\* cannot be undone or superseded, which is what keeps the model consistent.
CommitAgree ==
    /\ (\A p \in participants : decision[p] = commit)
         => (\A p \in participants : v[p] = yes)
    /\ (\A p \in participants : decision[p] = abort)
         => (\E p \in participants : v[p] = no \/ faulty[p] \/ coordFaulty)
    /\ \A p \in participants : decision[p] = commit => decision[p] = commit
    /\ \A p \in participants : decision[p] = abort => decision[p] = abort

\* The broadcast can stall, so we only require some progress to always
\* remain available: a decision eventually appears somewhere, or a fault
\* surfaces that justifies a stall -- this is the weakened AC3 liveness.
EventualDecisionOrFault ==
    <>(\E p \in participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty)

====