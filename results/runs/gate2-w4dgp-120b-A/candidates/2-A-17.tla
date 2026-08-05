---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME Undecided \notin {yes, no, commit, abort}
ASSUME Waiting \notin {yes, no, commit, abort}

VARIABLES pstate, alive, decision, faulty, sentVote, req, vote, broadcast, cstate, fwd

vars == <<pstate, alive, decision, faulty, sentVote, req, vote, broadcast, cstate, fwd>>

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ req \in {waiting, yes, no}
    /\ vote \in {yes, no}
    /\ broadcast \in [participants -> {yes, no, notsent}]
    /\ cstate \in {waiting, yes, no, broadcast, committed}
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ req = waiting
    /\ vote = no
    /\ broadcast = [p \in participants |-> notsent]
    /\ cstate = waiting
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReqNB ==
    /\ cstate = waiting
    /\ cstate' = yes
    /\ req' = waiting
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, vote, broadcast, fwd>>

GetVoteNB(p) ==
    /\ cstate = yes
    /\ alive[p]
    /\ ~sentVote[p]
    /\ pstate[p] = undecided
    /\ \E v \in {yes, no} : pstate' = [pstate EXCEPT ![p] = v]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, req, vote, broadcast, cstate, fwd>>

CoordinatorFaultNB ==
    /\ cstate \in {yes, broadcast}
    /\ \E p \in participants : alive[p]
    /\ cstate' = no
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, req, vote, broadcast, fwd>>

MakeDecision ==
    /\ cstate = yes
    /\ \E p \in participants : pstate[p] = no
    /\ vote = no
    /\ cstate' = no
    /\ vote' = no
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, req, broadcast, fwd>>

MakeDecision ==
    /\ cstate = yes
    /\ \A p \in participants : pstate[p] = yes
    /\ vote = yes
    /\ cstate' = yes
    /\ vote' = yes
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, req, broadcast, fwd>>

BroadcastDecision ==
    /\ cstate \in {yes, no}
    /\ cstate' = broadcast
    /\ broadcast' = [p \in participants |-> vote]
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, req, vote, fwd>>

DieNB(p) ==
    /\ alive[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pstate, decision, sentVote, req, vote, broadcast, cstate, fwd>>

PreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcast[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, req, vote, broadcast, cstate, fwd>>

PreDecideFromForwarding(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in participants : fwd[q][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[CHOOSE q \in participants : fwd[q][p] # notsent][p]]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, req, vote, broadcast, cstate, fwd>>

Forward(p, q) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ fwd[p][q] = notsent
    /\ q # p
    /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, req, vote, broadcast, cstate>>

DecideNB(p) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ \A q \in participants : q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = decision[p]]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, req, vote, broadcast, cstate, fwd>>

AbortOnTimeoutNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ cstate = no
    /\ \A q \in participants : broadcast[q] = notsent
    /\ \A q \in participants : alive[q] => fwd[p][q] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, alive, faulty, sentVote, req, vote, broadcast, cstate, fwd>>

NextNB ==
    \/ SendReqNB
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordinatorFaultNB
    \/ \E p \in participants : GetVoteNB(p)
    \/ \E p \in participants : DieNB(p)
    \/ \E p \in participants : PreDecideFromCoordinator(p)
    \/ \E p \in participants : PreDecideFromForwarding(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : DecideNB(p)
    \/ \E p \in participants : AbortOnTimeoutNB(p)

SpecNB == InitNB /\ [][NextNB]_vars
    /\ (\A p \in participants : WF_vars(DecideNB(p)))
    /\ (\A p \in participants : \A q \in participants : WF_vars(Forward(p, q)))
    /\ (\A p \in participants : WF_vars(PreDecideFromCoordinator(p)))
    /\ (\A p \in participants : WF_vars(PreDecideFromForwarding(p)))
    /\ WF_vars(SendReqNB)
    /\ WF_vars(GetVoteNB(CHOOSE p \in participants : sentVote[p]))

AgreementNB ==
    ~(\E p \in participants, q \in participants :
        decision[p] = commit /\ decision[q] = abort)

CommitValidNB ==
    (\E p \in participants : decision[p] = commit) =>
        (\A p \in participants : pstate[p] = yes)

AbortValidNB ==
    (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : pstate[p] = no \/ faulty[p] \/ cstate = no)

IrrevocableNB ==
    \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~>
        (decision[p] = commit \/ decision[p] = abort)

TerminationNB ==
    <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ cstate = no)

NonBlockingNB ==
    \A p \in participants : (decision[p] = undecided) ~> (decision[p] # undecided \/ faulty[p] \/ cstate = no)

====