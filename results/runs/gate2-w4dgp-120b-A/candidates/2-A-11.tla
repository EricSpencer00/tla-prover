---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB builds on top of the ACP-SB (base) module's coordinator logic: a
\* single coordinator that decides commit/abort based on participant votes,
\* with both coordinator and participants allowed to crash. The extension
\* here is a reliable broadcast: participants forward a received decision to
\* every other participant before finalizing it locally, so a coordinator
\* crash mid-broadcast cannot leave a non-faulty participant stranded.

VARIABLES vote, partAlive, decision, partFaulty, voteSent, ptable, cstate

vars == <<vote, partAlive, decision, partFaulty, voteSent, ptable, cstate>>

PartIds == participants \cup {waiting}

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ ptable \in [participants -> [PartIds -> {notsent, commit, abort}]]
  /\ cstate \in [type: {leader, participant}, alive: BOOLEAN,
                 faulty: BOOLEAN, msg: PartIds]

InitNB ==
  /\ vote = [p \in participants |-> yes]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ ptable = [p \in participants |-> [q \in PartIds |-> notsent]]
  /\ cstate = [type |-> leader, alive |-> TRUE, faulty |-> FALSE, msg |-> waiting]

SendReqNB ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ \A p \in participants : voteSent[p] = FALSE
  /\ cstate' = [cstate EXCEPT !.msg = waiting]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, ptable>>

GetVoteNB(p) ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ voteSent[p] = FALSE
  /\ partAlive[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, ptable, cstate>>

DetectFaultNB ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ cstate.msg = waiting
  /\ \E p \in participants : voteSent[p] = FALSE
  /\ cstate' = [cstate EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, ptable>>

MakeDecisionNB ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ cstate.msg = waiting
  /\ \A p \in participants : voteSent[p]
  /\ cstate' = [cstate EXCEPT !.msg = IF \A p \in participants : vote[p] = yes
                                     THEN commit ELSE abort]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, ptable>>

BroadcastNB ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ cstate.msg \in {commit, abort}
  /\ cstate' = [type |-> participant, alive |-> FALSE, faulty |-> FALSE,
                msg |-> cstate.msg]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, ptable>>

DieNB ==
  /\ cstate.type = leader
  /\ cstate.alive
  /\ cstate' = [cstate EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, ptable>>

\* A participant stores the pre-decision it receives from the (still alive)
\* coordinator into its own forwarding table entry.
PreDecideFromCoord(p) ==
  /\ partAlive[p]
  /\ cstate.type = participant
  /\ cstate.alive
  /\ cstate.msg \in {commit, abort}
  /\ ptable[p][p] = notsent
  /\ ptable' = [ptable EXCEPT ![p][p] = cstate.msg]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, cstate>>

\* A participant stores the pre-decision it receives from another participant
\* (relayed via forwarding) into its own forwarding entry.
PreDecideFromPart(p) ==
  /\ partAlive[p]
  /\ ptable[p][p] = notsent
  /\ \E q \in participants :
       ptable[q][p] # notsent
         /\ ptable' = [ptable EXCEPT ![p][p] = ptable[q][p]]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, cstate>>

\* Forwarding step: a participant that has received a pre-decision (stored at
\* its own index in the forwarding table) forwards that pre-decision to
\* another participant that has not yet received it.
Forward(p, q) ==
  /\ partAlive[p]
  /\ ptable[p][p] # notsent
  /\ ptable[p][q] = notsent
  /\ ptable' = [ptable EXCEPT ![p][q] = ptable[p][p]]
  /\ UNCHANGED <<vote, partAlive, decision, partFaulty, voteSent, cstate>>

\* Once a participant's pre-decision has been forwarded to every other
\* participant, it finalizes (decides) locally -- the safe point where the
\* coordinator's broadcast is no longer needed for termination.
DecideNB(p) ==
  /\ partAlive[p]
  /\ decision[p] = undecided
  /\ ptable[p][p] # notsent
  /\ \A q \in participants : q # p => ptable[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED <<vote, partAlive, partFaulty, voteSent, ptable, cstate>>

AbortOnTimeoutNB(p) ==
  /\ partAlive[p]
  /\ decision[p] = undecided
  /\ ~ cstate.alive
  /\ (\A q \in participants : ptable[q][p] = notsent)
  /\ (\A q \in participants : ~ partAlive[q] => ptable[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, partAlive, partFaulty, voteSent, ptable, cstate>>

DiePartNB(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, ptable, cstate>>

NextNB ==
  \/ SendReqNB \/ DetectFaultNB \/ MakeDecisionNB \/ BroadcastNB \/ DieNB
  \/ \E p \in participants :
       GetVoteNB(p) \/ DiePartNB(p) \/ PreDecideFromCoord(p) \/ PreDecideFromPart(p)
         \/ DecideNB(p) \/ AbortOnTimeoutNB(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(SendReqNB) /\ WF_vars(DetectFaultNB) /\ WF_vars(MakeDecisionNB)
  /\ WF_vars(BroadcastNB) /\ WF_vars(DieNB)
  /\ \A p \in participants :
       WF_vars(GetVoteNB(p)) /\ WF_vars(PreDecideFromCoord(p))
         /\ WF_vars(PreDecideFromPart(p)) /\ WF_vars(DecideNB(p))
         /\ WF_vars(AbortOnTimeoutNB(p)) /\ WF_vars(DiePartNB(p))

\* Safety: no two participants ever commit and abort in disagreement.
AC1 == ~ \E p, q \in participants : decision[p] = commit /\ decision[q] = abort

\* Validity: a commit only occurs if every participant voted yes.
AC2 == \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

\* Validity: an abort is only legal if some participant voted no or some
\* participant crashed or the coordinator crashed.
AC3 == \A p \in participants : decision[p] = abort
         => (\E q \in participants : vote[q] = no \/ partFaulty[q] \/ cstate.faulty)

\* Irreversibility: a participant's decision is permanent.
AC3a == \A p \in participants :
          (decision[p] = commit => [decision EXCEPT ![p] = commit])
            /\ (decision[p] = abort => [decision EXCEPT ![p] = abort])

\* Liveness: either everyone decides, or the coordinator/permanent failure
\* case is reached -- all other traces must still resolve.
AC3 == <>(\A p \in participants : decision[p] # undecided \/ partFaulty[p] \/ cstate.faulty)

\* Every non-faulty participant eventually reaches a decision -- non-blocking
\* termination. The base broadcast protocol can stall here if the
\* coordinator dies mid-broadcast while some participant is still undecided.
AC5 == \A p \in participants : (partAlive[p] => <>(decision[p] # undecided))
====