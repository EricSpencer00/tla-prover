---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator state: voting phase (requests sent, votes gathered), then broadcasting.
CoordinatorStates == [requestSent : [participants -> BOOLEAN],
                       arriveVote : [participants -> {yes, no, waiting}],
                       broadcast : [participants -> {commit, abort, notsent}],
                       decision : {commit, abort, undecided},
                       alive : BOOLEAN,
                       faulty : BOOLEAN]

VARIABLES cstate, vote, alive, decision, faulty, sentVote

vars == <<cstate, vote, alive, decision, faulty, sentVote>>

TypeInv == /\ cstate \in CoordinatorStates
           /\ vote \in [participants -> {yes, no}]
           /\ alive \in [participants -> BOOLEAN]
           /\ decision \in [participants -> {undecided, commit, abort}]
           /\ faulty \subseteq participants
           /\ sentVote \subseteq participants

Init == /\ cstate = [requestSent |-> [p \in participants |-> FALSE],
                     arriveVote |-> [p \in participants |-> waiting],
                     broadcast |-> [p \in participants |-> notsent],
                     decision |-> undecided,
                     alive |-> TRUE,
                     faulty |-> FALSE]
        /\ vote \in [participants -> {yes, no}]
        /\ alive = [p \in participants |-> TRUE]
        /\ decision = [p \in participants |-> undecided]
        /\ faulty = {}
        /\ sentVote = {}

\* Simple broadcast: the coordinator sends one decision message at a time.
SendRequest(p) == /\ cstate.alive
                  /\ ~cstate.requestSent[p]
                  /\ cstate' = [cstate EXCEPT !.requestSent[p] = TRUE]
                  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

ReceiveVote(p) == /\ cstate.alive
                  /\ cstate.decision = undecided
                  /\ cstate.requestSent[p]
                  /\ cstate.arriveVote[p] = waiting
                  /\ p \in sentVote
                  /\ cstate' = [cstate EXCEPT !.arriveVote[p] = vote[p]]
                  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

CoordinatorDetectFault(p) == /\ cstate.alive
                            /\ cstate.decision = undecided
                            /\ cstate.requestSent[p]
                            /\ cstate.arriveVote[p] = waiting
                            /\ ~alive[p]
                            /\ cstate' = [cstate EXCEPT !.decision = abort]
                            /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

MakeDecision == /\ cstate.alive
               /\ cstate.decision = undecided
               /\ \A p \in participants : cstate.arriveVote[p] # waiting
               /\ cstate' = [cstate EXCEPT !.decision =
                               IF \A p \in participants : cstate.arriveVote[p] = yes
                               THEN commit ELSE abort]
               /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

BroadcastDecision(p) == /\ cstate.alive
                       /\ cstate.decision # undecided
                       /\ cstate.broadcast[p] = notsent
                       /\ cstate' = [cstate EXCEPT !.broadcast[p] = cstate.decision]
                       /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

CoordinatorDie == /\ cstate.alive
                  /\ cstate' = [cstate EXCEPT !.alive = FALSE, !.faulty = TRUE]
                  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote>>

SendVote(p) == /\ alive[p]
               /\ cstate.requestSent[p]
               /\ p \notin sentVote
               /\ sentVote' = sentVote \cup {p}
               /\ UNCHANGED <<cstate, vote, alive, decision, faulty>>

AbortOnNo(p) == /\ alive[p]
                /\ decision[p] = undecided
                /\ p \in sentVote
                /\ vote[p] = no
                /\ decision' = [decision EXCEPT ![p] = abort]
                /\ UNCHANGED <<cstate, vote, alive, faulty, sentVote>>

AbortOnTimeout(p) == /\ alive[p]
                     /\ decision[p] = undecided
                     /\ ~cstate.requestSent[p]
                     /\ ~cstate.alive
                     /\ decision' = [decision EXCEPT ![p] = abort]
                     /\ UNCHANGED <<cstate, vote, alive, faulty, sentVote>>

DecideOnBroadcast(p) == /\ alive[p]
                        /\ decision[p] = undecided
                        /\ cstate.broadcast[p] # notsent
                        /\ decision' = [decision EXCEPT ![p] = cstate.broadcast[p]]
                        /\ UNCHANGED <<cstate, vote, alive, faulty, sentVote>>

ParticipantDie(p) == /\ alive[p]
                     /\ alive' = [alive EXCEPT ![p] = FALSE]
                     /\ faulty' = faulty \cup {p}
                     /\ UNCHANGED <<cstate, vote, decision, sentVote>>

Next == \/ \E p \in participants : SendRequest(p)
        \/ \E p \in participants : ReceiveVote(p)
        \/ \E p \in participants : CoordinatorDetectFault(p)
        \/ MakeDecision
        \/ \E p \in participants : BroadcastDecision(p)
        \/ CoordinatorDie
        \/ \E p \in participants : SendVote(p)
        \/ \E p \in participants : AbortOnNo(p)
        \/ \E p \in participants : AbortOnTimeout(p)
        \/ \E p \in participants : DecideOnBroadcast(p)
        \/ \E p \in participants : ParticipantDie(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : AbortOnNo(p))
        /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))

\* AC1: no two participants are ever allowed to disagree on the outcome.
NoConflictingDecisions == \A p, q \in participants :
                            (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit can only happen on unanimity of yes votes.
CommitOnlyOnAllYes == \A p \in participants :
                        decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort requires at least one no vote or a failure of some part.
AbortOnlyOnNoOrFailure == \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ faulty # {}
      \/ cstate.faulty

\* Once a participant decides, it never moves to a different decision.
IrreversibleOnceDecided == \A p \in participants :
    /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
    /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])

\* Liveness: no non-faulty participant is left undecided forever -- not here.
Progress == <>(\A p \in participants : decision[p] # undecided \/ faulty # {} \/ cstate.faulty)

====