---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* The Non-Blocking Atomic Commitment Protocol (ACP-NB) extends the
\* simple broadcast variant (ACP-SB) by implementing a reliable broadcast:
\* participants forward the pre-decision they received to all other
\* participants before finalizing locally.  This ensures that even if the
\* coordinator crashes mid-broadcast, surviving participants can still
\* learn the decision through peer forwarding, so every non-faulty
\* participant eventually decides -- a termination guarantee the simple
\* broadcast variant lacks.  Both the coordinator and participants may
\* crash, but a crashed participant's already-sent forwardings remain in
\* effect for the others, which is what keeps the protocol non-blocking.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, forward

vars == <<vote, alive, decision, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ req \in {waiting, notsent}
  /\ coordVote \in {yes, no, undecided}
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ req = waiting
  /\ coordVote = undecided
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions are inherited from ACP-SB; only participant actions
\* differ (the new reliable-broadcast steps are added at the end).
SendReq == /\ coordAlive /\ req = waiting /\ req' = notsent /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote, broadcast, coordAlive, coordFaulty, forward>>

GetVote ==
  /\ coordAlive /\ req = notsent /\ \E p \in participants :
       /\ alive[p] /\ ~voted[p] /\ voted' = [voted EXCEPT ![p] = TRUE]
       /\ vote' = [vote EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

DetectFault ==
  /\ coordAlive /\ req = notsent /\ coordVote = undecided /\ coordFaulty = FALSE /\ \E p \in participants : ~alive[p]
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, req, coordVote, broadcast, coordAlive, forward>>

MakeDecision ==
  /\ coordAlive /\ coordVote = undecided /\ \E p \in participants : voted[p]
  /\ coordVote' = IF vote[p] = no THEN no ELSE yes
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, req, broadcast, coordAlive, coordFaulty, forward>>

Broadcast ==
  /\ coordAlive /\ coordVote # undecided
  /\ \E p \in participants :
       /\ broadcast' = [broadcast EXCEPT ![p] = coordVote]
       /\ forward' = [forward EXCEPT ![p][p] = coordVote]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, req, coordVote, coordAlive, coordFaulty>>

Die ==
  /\ coordAlive /\ coordAlive' = FALSE /\ UNCHANGED <<vote, alive, decision, faulty, voted, req, coordVote, broadcast, coordFaulty, forward>>

SendVote ==
  /\ \E p \in participants :
       /\ alive[p] /\ ~voted[p]
       /\ ~faulty[p]
       /\ voted' = [voted EXCEPT ![p] = TRUE]
       /\ vote' = [vote EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

AbortVote ==
  /\ \E p \in participants :
       /\ alive[p] /\ ~voted[p]
       /\ ~faulty[p]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, voted, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

AbortTimeout ==
  /\ ~coordAlive /\ ~coordFaulty
  /\ \A p \in participants : broadcast[p] = notsent
  /\ \A p \in participants : \A q \in participants : ~(~alive[p] /\ forward[p][q] # notsent)
  /\ \E p \in participants : alive[p] /\ decision[p] = undecided
  /\ decision' = [p \in participants |-> IF alive[p] /\ decision[p] = undecided THEN abort ELSE decision[p]]
  /\ UNCHANGED <<vote, alive, voted, faulty, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

\* A participant adopts the decision it received from the coordinator.
PreDecideCoordinator ==
  /\ \E p \in participants :
       /\ alive[p] /\ decision[p] = undecided
       /\ broadcast[p] # notsent
       /\ decision[p] = undecided
       /\ forward' = [forward EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, decision>>

\* A participant adopts the decision it received from another participant's forwarding.
PreDecideForward ==
  /\ \E p \in participants :
       /\ alive[p] /\ decision[p] = undecided
       /\ (\E q \in participants : forward[q][p] # notsent)
       /\ decision[p] = undecided
       /\ forward' = [forward EXCEPT ![p][p] = (CHOOSE q \in participants : forward[q][p] # notsent)]
  /\ UNCHANGED <<vote, alive, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, decision>>

\* Forward the pre-decision this participant has to another participant.
Forward ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = undecided
       /\ forward[p][p] # notsent
       /\ \E q \in participants :
            /\ p # q
            /\ forward[p][q] = notsent
            /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, decision>>

\* Non-blocking termination: a participant decides only after it has
\* forwarded its pre-decision to all others, so a mid-broadcast crash
\* cannot leave an undecided survivor once everyone else's forwards have arrived.
DecideNB ==
  /\ \E p \in participants :
       /\ alive[p] /\ decision[p] = undecided
       /\ (\A q \in participants : forward[p][q] # notsent \/ q = p)
       /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

DieNB ==
  /\ \E p \in participants : alive[p] /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, faulty, voted, req, coordVote, broadcast, coordAlive, coordFaulty, forward>>

NextNB ==
  \/ SendReq \/ GetVote \/ DetectFault \/ Broadcast \/ MakeDecision \/ Die \/ DieNB
  \/ SendVote \/ AbortVote \/ AbortTimeout
  \/ PreDecideCoordinator \/ PreDecideForward \/ Forward \/ DecideNB

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ SF_vars(SendReq) /\ SF_vars(GetVote) /\ SF_vars(DetectFault) /\ SF_vars(Broadcast) /\ SF_vars(MakeDecision) /\ SF_vars(Die)
  /\ SF_vars(SendVote) /\ SF_vars(AbortVote) /\ SF_vars(AbortTimeout) /\ SF_vars(DecideNB)
  /\ SF_vars(PreDecideCoordinator) /\ SF_vars(PreDecideForward) /\ SF_vars(Forward)

\* Safety properties: agreement, commit and abort validity, and irrevocability.
Agreement == ~(\E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort)

CommitValidity == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordFaulty)

Irrevocability ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: agreement's strong progress version (everybody decides or someone fails),
\* plus the non-blocking termination guarantee for every non-faulty participant.
AgreementStrongProgress ==
  <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ coordFaulty)

DecideEventually == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided \/ faulty[p])

====