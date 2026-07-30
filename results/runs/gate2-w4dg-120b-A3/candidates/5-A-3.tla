---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordVote, coordAlive, coordFaulty, coordSent, coordDecision, coordBroadcast,
         vote, alive, decision, faulty, voteSent

vars == <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision, coordBroadcast,
          vote, alive, decision, faulty, voteSent>>

RECURSIVE AllRec(_)
AllRec(S) == IF S = {} THEN TRUE
            ELSE LET x == CHOOSE y \in S : TRUE
                 IN coordVote[x] # waiting /\ coordBroadcast[x] # notsent /\ decision[x] # undecided /\ AllRec(S \ {x})

TypeInv ==
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordSent \in [participants -> BOOLEAN]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]

Init ==
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordSent = [p \in participants |-> FALSE]
    /\ coordDecision = undecided
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]

\* Coordinator actions.
SendRequest(p) ==
    /\ coordAlive
    /\ ~coordSent[p]
    /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   vote, alive, decision, faulty, voteSent>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ coordVote[p] = waiting
    /\ voteSent[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordDecision, coordBroadcast,
                   vote, alive, decision, faulty, voteSent>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordBroadcast,
                   vote, alive, decision, faulty, voteSent>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordBroadcast,
                   vote, alive, decision, faulty, voteSent>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   vote, alive, decision, faulty, voteSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordVote, coordSent, coordDecision, coordBroadcast,
                   vote, alive, decision, faulty, voteSent>>

\* Participant actions.
SendVote(p) ==
    /\ alive[p]
    /\ coordSent[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   coordBroadcast, vote, alive, decision, faulty>>

AbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ voteSent[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   coordBroadcast, vote, alive, faulty, voteSent>>

AbortOnCoordDead(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   coordBroadcast, vote, alive, faulty, voteSent>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   coordBroadcast, vote, alive, faulty, voteSent>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordSent, coordDecision,
                   coordBroadcast, vote, decision, voteSent>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnNo(p)
    \/ \E p \in participants : AbortOnCoordDead(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : PartDie(p)

\* Weak fairness on progress actions (excluding death transitions).
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : SendRequest(p))
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : MakeDecision)

\* Safety: agreement, commit/abort validity, and irrevocability.
Agree ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
    \A p \in participants :
        decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

Irreversible ==
    \A p \in participants :
        /\ (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

\* Liveness: everyone decides OR someone fails (simple broadcast, not non-blocking).
DecideOrFail ==
    <>(AllRec(participants) \/ \E q \in participants : faulty[q] \/ coordFaulty)

====