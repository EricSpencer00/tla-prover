---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, or the pre-decision (commit/abort) received.
\* The coordinator's broadcast is unreliable (it may die mid-broadcast), so
\* participants forward decisions to each other to guarantee eventual delivery.
\* The invariant is agreement: no two participants reach different decisions.
\* The liveness property is non-blocking termination for every non-faulty
\* participant, which the forwarding mechanism provides even after coordinator
\* failure.

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, voteSent, coordReq, coordVote,
           coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {yes, no, undecided}
    /\ coordBroadcast \in [participants -> {commit, abort, undecided}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordReq = waiting
    /\ coordVote = undecided
    /\ coordBroadcast = [p \in participants |-> undecided]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = yes
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
    /\ coordAlive
    /\ alive[p]
    /\ vote[p] = undecided
    /\ coordReq # waiting
    /\ coordVote = undecided
    /\ coordVote' = vote[p]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault(p) ==
    /\ coordAlive
    /\ alive[p]
    /\ vote[p] = no
    /\ coordVote = undecided
    /\ coordVote' = no
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

MakeDecision ==
    /\ coordAlive
    /\ coordVote # undecided
    /\ coordDecision = undecided
    /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = undecided
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordDecision, coordAlive, coordFaulty, fwd>>

Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, fwd>>

SendVote(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ vote[p] # undecided
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : coordBroadcast[q] # undecided
    /\ \A q \in participants : ~(~alive[q] /\ fwd[q][p] # notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

\* A participant stores a pre-decision it receives from the coordinator.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ coordBroadcast[p] # undecided
    /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant stores a pre-decision it receives from another participant.
PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ fwd[q][p] # notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p]
    /\ alive[q]
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant finalizes its decision only after forwarding to everyone.
Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DieP(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
    \/ SendRequest \/ MakeDecision \/ Die
    \/ \E p \in participants :
         \/ GetVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ SendVote(p)
         \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ PreDecideFromCoord(p)
         \/ PreDecideFromFwd(p) \/ Decide(p) \/ DieP(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision)
    /\ \A p \in participants :
         /\ WF_vars(GetVote(p)) /\ WF_vars(DetectFault(p))
         /\ WF_vars(Broadcast(p)) /\ WF_vars(SendVote(p))
         /\ WF_vars(AbortOnVote(p)) /\ WF_vars(AbortOnTimeout(p))
         /\ WF_vars(PreDecideFromCoord(p)) /\ WF_vars(PreDecideFromFwd(p))
         /\ WF_vars(Decide(p))

Agreement ==
    \A p, q \in participants : (decision[p] = commit) => (decision[q] # abort)

CommitValidity ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

Irrevocability ==
    \A p \in participants :
        (decision[p] # undecided) ~> (decision[p] = decision[p])

DecideEventually ==
    \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

SpecNBVars == vars

SpecNBStateSpace == SpecNB /\ SpecNBVars

SpecNBStateSpaceTypeOK == SpecNB /\ TypeInvNB

====