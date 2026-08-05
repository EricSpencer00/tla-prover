---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES partVote, partAlive, partDec, partFaulty, partSent, coordReq, coordVote,
          coordBroad, coordDec, coordAlive, coordFaulty, forwarded

vars == <<partVote, partAlive, partDec, partFaulty, partSent, coordReq, coordVote,
          coordBroad, coordDec, coordAlive, coordFaulty, forwarded>>

\* forwarded[p][q] is what participant p has forwarded to participant q
\* (notsent, commit, or abort). Each participant also keeps a local copy of
\* the decision it has learned (its own entry in forwarded) before finalizing.

AllDecided ==
  /\ \A p \in participants : partAlDec[p]
  /\ \A p \in participants : \A q \in participants : partAlDec[q]

SomeDecided ==
  \E p \in participants : partAlDec[p]

CoordAliveVotes ==
  \E p \in participants : coordAlive /\ partVote[p] = yes

CoordBroadcastAlive ==
  \E p \in participants : coordAlive /\ coordBroad[p]

\* A dead participant may still have a useful decision cached to forward
\* to a surviving participant, so forwarded messages from dead participants
\* are not discarded.
AliveForwardedDecision ==
  \E p \in participants :
     (\A q \in participants : partAlive[q] => forwarded[p][q] # notsent)
       /\ ~partAlive[p]

TypeInvNB ==
  /\ partVote \in [participants -> {yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDec \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordBroad \in [participants -> {notsent, commit, abort}]
  /\ coordDec \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ partVote \in [participants -> {yes, no}]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDec = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = yes
  /\ coordBroad = [p \in participants |-> notsent]
  /\ coordDec = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* A participant may crash silently at any time; no notification is sent to
\* anybody, which is what makes the forwarding by survivors observable.
DieNB ==
  /\ \E p \in participants : partAlive[p]
  /\ \E p \in participants :
       /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
       /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partVote, partDec, partSent, coordReq, coordVote,
                 coordBroad, coordDec, coordAlive, coordFaulty, forwarded>>

PreDecideFromCoordinator ==
  /\ \E p \in participants :
       /\ partAlive[p]
       /\ coordBroad[p] # notsent
       /\ forwarded[p][p] = notsent
       /\ forwarded' = [forwarded EXCEPT ![p][p] = coordBroad[p]]
  /\ UNCHANGED <<partVote, partAlive, partDec, partFaulty, partSent, coordReq,
                 coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

PreDecideFromForward ==
  /\ coordAlive
  /\ \E p \in participants, q \in participants :
       /\ partAlive[p]
       /\ forwarded[q][p] # notsent
       /\ forwarded[p][p] = notsent
       /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<partVote, partAlive, partDec, partFaulty, partSent, coordReq,
                 coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

\* Forward the pre-decision to one specific participant that has not yet
\* received it.  Requires an actual decision (not notsent) to be forwarded.
Forward ==
  /\ \E p \in participants :
       /\ partAlive[p]
       /\ forwarded[p][p] # notsent
       /\ \E q \in participants :
            /\ forwarded[p][q] = notsent
            /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<partVote, partAlive, partDec, partFaulty, partSent, coordReq,
                 coordVote, coordBroad, coordDec, coordAlive, coordFaulty>>

\* A participant finalizes its decision only after it has forwarded to every
\* other participant, which is what makes termination non-blocking.
DecideNB ==
  /\ \E p \in participants :
       /\ partAlive[p]
       /\ partDec[p] = undecided
       /\ forwarded[p][p] # notsent
       /\ \A q \in participants : forwarded[p][q] # notsent
       /\ partDec' = [partDec EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent, coordReq, coordVote,
                 coordBroad, coordDec, coordAlive, coordFaulty, forwarded>>

\* If the coordinator has died and no alive participant ever received a
\* broadcast from it, the remaining participants may time out and abort,
\* provided no dead participant still has a useful decision to forward.
AbortOnTimeoutNB ==
  /\ ~coordAlive
  /\ \A p \in participants : ~coordBroad[p]
  /\ ~AliveForwardedDecision
  /\ \E p \in participants :
       /\ partAlive[p]
       /\ partDec[p] = undecided
       /\ partDec' = [partDec EXCEPT ![p] = abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent, coordReq, coordVote,
                 coordBroad, coordDec, coordAlive, coordFaulty, forwarded>>

NextNB ==
  \/ DieNB
  \/ PreDecideFromCoordinator
  \/ PreDecideFromForward
  \/ Forward
  \/ DecideNB
  \/ AbortOnTimeoutNB

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(PreDecideFromCoordinator)
  /\ WF_vars(PreDecideFromForward)
  /\ WF_vars(Forward)
  /\ WF_vars(DecideNB)
  /\ WF_vars(AbortOnTimeoutNB)

\* Agreement: no two participants reach different decisions.
AC1 == ~(SomeDecided /\ \E p, q \in participants :
                     partDec[p] = commit /\ partDec[q] = abort)

\* Commit is valid only when every participant voted yes.
AC2 == (\E p \in participants : partDec[p] = commit) => (\A p \in participants : partVote[p] = yes)

\* Abort is justified by a no vote or a crash.
AC3 == (\E p \in participants : partDec[p] = abort) =>
          (\E p \in participants : partVote[p] = no \/ partFaulty[p] \/ coordFaulty)

\* Irreversibility: once a decision is made it is never undone.
AC4 == \A p \in participants : (partDec[p] = commit \/ partDec[p] = abort) ~> (partDec[p] = commit \/ partDec[p] = abort)

\* Progress: either everyone decides or something crashed.
AC3Progress == <>(AllDecided \/ \E p \in participants : partFaulty[p] \/ coordFaulty)

\* Progress: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (partAlive[p] /\ partDec[p] = undecided) ~> (partAlDec[p])

PartDecide == \E p \in participants : partDec[p] # undecided

\* The non-blocking termination property requires strong fairness: a
\* participant that keeps learning and forwarding must not be stalled.
Fairness ==
  /\ WF_vars(PreDecideFromCoordinator)
  /\ WF_vars(PreDecideFromForward)
  /\ WF_vars(Forward)
  /\ SF_vars(DecideNB)
  /\ SF_vars(AbortOnTimeoutNB)

====