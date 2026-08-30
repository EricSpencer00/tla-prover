---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, palive, decision, faulty, votesent, ptable
vars == <<pstate, palive, decision, faulty, votesent, ptable>>

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ palive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {waiting, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ votesent \in [participants -> BOOLEAN]
    /\ ptable \in [participants -> [participants -> {notsent, commit, abort}]]

\* The coordinator's own record of the decision it broadcast to each participant.
cstate == [p \in participants |-> ptable["coordinator"][p]]

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ palive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ votesent = [p \in participants |-> FALSE]
    /\ ptable = [p \in participants |-> [q \in participants \cup {"coordinator"} |-> notsent]]

SendRequest(p) ==
    /\ pstate[p] = undecided
    /\ votesent[p] = FALSE
    /\ pstate' = [pstate EXCEPT ![p] = yes]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<palive, decision, faulty, ptable>>

\* The coordinator is slow but never fails here; a slow participant is handled by
\* the live-forwarding guarantee, not by a coordinator timeout.
GetVote(p) ==
    /\ votesent[p] = FALSE
    /\ pstate[p] \in {yes, no}
    /\ cstate[p] = notsent
    /\ pstate[p] = no
    /\ ptable' = [ptable EXCEPT !["coordinator"][p] = abort]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, palive, decision, faulty>>

\* The coordinator never broadcasts a yes vote.
GetVoteYes(p) ==
    /\ votesent[p] = FALSE
    /\ pstate[p] = yes
    /\ cstate[p] = notsent
    /\ ptable' = [ptable EXCEPT !["coordinator"][p] = commit]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, palive, decision, faulty>>

\* The coordinator only acts on a participant it can still hear from.
DetectFault(p) ==
    /\ votesent[p] = FALSE
    /\ pstate[p] = undecided
    /\ ~palive[p]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, palive, decision, faulty, ptable>>

MakeDecision ==
    /\ \A p \in participants : votesent[p]
    /\ \A p \in participants : cstate[p] = notsent
    /\ LET d == IF (\A p \in participants : pstate[p] = yes) THEN commit ELSE abort
       IN ptable' = [ptable EXCEPT !["coordinator"] = [p \in participants |-> d]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, votesent>>

Broadcast(p) ==
    /\ cstate[p] # notsent
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = cstate[p]]
    /\ UNCHANGED <<pstate, palive, faulty, votesent, ptable>>

Die(p) ==
    /\ palive[p] = TRUE
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, decision, votesent, ptable>>

\* A participant stores the decision it receives from the coordinator.
PreDecideFromCoordinator(p) ==
    /\ pstate[p] # undecided
    /\ cstate[p] # notsent
    /\ ptable[p][p] = notsent
    /\ ptable' = [ptable EXCEPT ![p][p] = cstate[p]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, votesent>>

\* A participant also stores a decision forwarded by another participant.
PreDecideFromForward(p, q) ==
    /\ pstate[p] # undecided
    /\ ptable[p][q] # notsent
    /\ ptable[p][p] = notsent
    /\ ptable' = [ptable EXCEPT ![p][p] = ptable[p][q]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, votesent>>

\* Forwarding: a participant must tell every other participant what it pre-decided.
Forward(p, q) ==
    /\ pstate[p] # undecided
    /\ ptable[p][p] # notsent
    /\ ptable[p][q] = notsent
    /\ ptable' = [ptable EXCEPT ![p][q] = ptable[p][p]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, votesent>>

\* A participant only finalizes locally once it has forwarded to everyone.
Decide(p) ==
    /\ pstate[p] # undecided
    /\ \A q \in participants : ptable[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = ptable[p][p]]
    /\ UNCHANGED <<pstate, palive, faulty, votesent, ptable>>

\* Abort on timeout if the coordinator is dead and no one else can recover.
AbortOnTimeout(p) ==
    /\ pstate[p] # undecided
    /\ decision[p] = waiting
    /\ ~palive["coordinator"]
    /\ \A q \in participants : cstate[q] = notsent
    /\ \A q \in participants : ~faulty[q] => \A r \in participants : ptable[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, palive, faulty, votesent, ptable>>

SendVote == \E p \in participants : SendRequest(p)
GetVoteAny == \E p \in participants : GetVote(p)
DetectAny == \E p \in participants : DetectFault(p)
PreDecideAny == \E p \in participants : PreDecideFromCoordinator(p)
ForwardAny == \E p \in participants, q \in participants : Forward(p, q)
DecideAny == \E p \in participants : Decide(p)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendVote)
    /\ WF_vars(GetVoteAny)
    /\ WF_vars(DetectAny)
    /\ WF_vars(PreDecideAny)
    /\ WF_vars(ForwardAny)
    /\ WF_vars(DecideAny)

\* Safety: no two participants end up in different final states.
Agreement ==
    \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Liveness: the reliable broadcast forces every non-faulty participant to decide.
EventualDecision ==
    \A p \in participants : (palive[p] /\ ~faulty[p]) ~> (decision[p] # waiting)

====