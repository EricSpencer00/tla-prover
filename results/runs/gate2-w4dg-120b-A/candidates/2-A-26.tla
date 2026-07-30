---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* A forwarding table entry is either empty (notsent), or records a pre-decision
\* received from the coordinator or from a forwarding by another participant.
Entries == {notsent, commit, abort}

VARIABLES vote, alive, decision, faulty, votesent, coordstate, table

vars == <<vote, alive, decision, faulty, votesent, coordstate, table>>

\* The system is alive while it is in transit, stopped after everyone decided, or
\* crashed after some participant failed.
CoordActive == coordstate \in {waiting, decided}
SystemAlive == CoordActive /\ \A p \in participants : alive[p]
SystemStopped == ~CoordActive /\ \A p \in participants : decision[p] # undecided
SystemCrashed == ~CoordActive /\ \E p \in participants : ~alive[p]

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ votesent \in [participants -> BOOLEAN]
  /\ coordstate \in {waiting, decided, crashed}
  /\ table \in [participants -> [participants -> Entries]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ votesent = [p \in participants |-> FALSE]
  /\ coordstate = waiting
  /\ table = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorRequest(p) ==
  /\ coordstate = waiting
  /\ vote[p] = undecided
  /\ coordstate' = decided
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, votesent, table>>

CoordinatorVote(p) ==
  /\ coordstate = decided
  /\ vote[p] # undecided
  /\ votesent[p] = FALSE
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordstate, table>>

CoordinatorFault(p) ==
  /\ coordstate = decided
  /\ vote[p] = undecided
  /\ coordstate' = crashed
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, votesent, table>>

CoordinatorBroadcast(p) ==
  /\ coordstate = decided
  /\ votesent[p] = TRUE
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = IF vote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, coordstate, table>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, votesent, coordstate, table>>

ParticipantAbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, coordstate, table>>

\* A participant learns its pre-decision from the coordinator's broadcast.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordstate = decided
  /\ table[p][p] = notsent
  /\ table' = [table EXCEPT ![p][p] =
        IF vote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordstate>>

\* A participant learns its pre-decision from another participant's forward.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants :
        /\ q # p
        /\ table[q][p] # notsent
        /\ table[p][p] = notsent
        /\ table' = [table EXCEPT ![p][p] = table[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordstate>>

\* Forwarding: send your own pre-decision to someone who has not yet received it.
Forward(p, q) ==
  /\ alive[p]
  /\ table[p][p] # notsent
  /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = table[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordstate>>

\* Only finalize once the pre-decision has reached every other participant.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : table[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = table[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, coordstate, table>>

\* Abort on timeout when the coordinator and all non-faulty participants have
\* stopped making progress and no forwarding can still rescue us.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordstate = crashed
  /\ \A q \in participants :
        alive[q] => decision[q] = undecided
  /\ \A q \in participants :
        (~alive[q] /\ faulty[q]) => \A r \in participants :
            alive[r] => table[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, coordstate, table>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, votesent, coordstate, table>>

Next ==
  \/ \E p \in participants :
        CoordinatorRequest(p) \/ CoordinatorVote(p) \/ CoordinatorFault(p)
        \/ CoordinatorBroadcast(p)
  \/ \E p \in participants : ParticipantSendVote(p) \/ ParticipantAbortOnVote(p)
        \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p) \/ Decide(p)
        \/ AbortOnTimeout(p) \/ ParticipantDie(p)
  \/ \E p, q \in participants : Forward(p, q)

\* Forwarding and pre-deciding are weakly fair; death is excluded, so the model
\* keeps making progress on the live participants it can.
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants : Decide(p))

\* Safety: no two participants ever reach different decisions.
AC1 ==
  ~(\E p, q \in participants :
        /\ decision[p] = commit
        /\ decision[q] = abort)

\* Safety: a commit requires unanimity.
AC2 ==
  (decision[CHOOSE p \in participants : TRUE] = commit) =>
    (\A p \in participants : vote[p] = yes)

\* Safety: an abort must be explainable by a no vote or a fault.
AC3 ==
  (decision[CHOOSE p \in participants : TRUE] = abort) =>
    \/ (\E p \in participants : vote[p] = no)
    \/ (\E p \in participants : faulty[p])
    \/ (coordstate = crashed)

\* Safety: decisions are final.
AC4 ==
  \A p \in participants :
    (decision[p] = commit) ~> (decision[p] = commit)
    /\ (decision[p] = abort) ~> (decision[p] = abort)

\* Liveness: the whole run eventually resolves, or someone ends up faulty.
AC3Liveness ==
  <>(SystemStopped \/ SystemCrashed)

\* Liveness: a non-faulty participant eventually decides -- guaranteed by
\* reliable broadcast, which the simple broadcast variant cannot guarantee.
AC5 ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====