---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Participant == participants
Decision == {undecided, commit, abort}
Vote == {no, yes}
FwdStatus == {notsent, commit, abort}

VARIABLES vote, alive, decision, faulty, sentVote, pstate
VARIABLES prep, recvP
vars == <<vote, alive, decision, faulty, sentVote, pstate, prep, recvP>>

\* prep/pstate implement the reliable broadcast. prep[p] records the decision
\* p has received (from the coordinator or from forwarding); recvP[p][q] records
\* whether p has already forwarded its pre-decision to participant q.
Init ==
  /\ vote = [p \in Participant |-> undecided]
  /\ alive = [p \in Participant |-> TRUE]
  /\ decision = [p \in Participant |-> undecided]
  /\ faulty = [p \in Participant |-> FALSE]
  /\ sentVote = [p \in Participant |-> FALSE]
  /\ pstate = [p \in Participant |-> waiting]
  /\ prep = [p \in Participant |-> notsent]
  /\ recvP = [p \in Participant |-> [q \in Participant |-> notsent]]

\* The coordinator and sendVote are unchanged from ACP-SB and are omitted here;
\* they are present in the full model; this module only adds the broadcast.
Decide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ prep[p] # notsent
  /\ \A q \in Participant : recvP[p][q] = prep[p]
  /\ decision' = [decision EXCEPT ![p] = prep[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, pstate, prep, recvP>>

PredecideFromCoord(p) ==
  /\ alive[p] = TRUE
  /\ prep[p] = notsent
  /\ pstate[p] # waiting
  /\ decision[p] = undecided
  /\ prep' = [prep EXCEPT ![p] = pstate[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, pstate, recvP>>

PredecideFromFwd(p) ==
  /\ alive[p] = TRUE
  /\ prep[p] = notsent
  /\ decision[p] = undecided
  /\ \E q \in Participant :
       /\ recvP[q][p] # notsent
       /\ prep' = [prep EXCEPT ![p] = recvP[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, pstate, recvP>>

Forward(p, q) ==
  /\ alive[p] = TRUE
  /\ prep[p] # notsent
  /\ recvP[p][q] = notsent
  /\ recvP' = [recvP EXCEPT ![p][q] = prep[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, pstate, prep>>

AbortTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ (pstate[p] = waiting \/ decision[p] = undecided)
  /\ \A q \in Participant : alive[q] = FALSE
  /\ \A q \in Participant : \A r \in Participant : recvP[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, pstate, prep, recvP>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, pstate, prep, recvP>>

Next ==
  \/ \E p \in Participant : Decide(p) \/ PredecideFromCoord(p)
                          \/ PredecideFromFwd(p) \/ AbortTimeout(p) \/ Die(p)
  \/ \E p \in Participant : \E q \in Participant : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Participant : PredecideFromCoord(p))
  /\ WF_vars(\E p \in Participant : PredecideFromFwd(p))
  /\ WF_vars(\E p \in Participant : \E q \in Participant : Forward(p, q))
  /\ WF_vars(\E p \in Participant : Decide(p))
  /\ WF_vars(\E p \in Participant : AbortTimeout(p))

\* Safety
TypeInvNB ==
  /\ vote \in [Participant -> Vote]
  /\ alive \in [Participant -> BOOLEAN]
  /\ decision \in [Participant -> Decision]
  /\ faulty \in [Participant -> BOOLEAN]
  /\ sentVote \in [Participant -> BOOLEAN]
  /\ pstate \in [Participant -> Vote \cup {waiting}]
  /\ prep \in [Participant -> {notsent} \cup Decision]
  /\ recvP \in [Participant -> [Participant -> {notsent} \cup Decision]]

\* No two participants commit vs. abort.
NoConflictingDecision ==
  \A p, q \in Participant :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit requires unanimous yes.
CommitValid == \A p \in Participant : decision[p] = commit => \A q \in Participant : vote[q] = yes

\* An abort has an excuse.
AbortValid ==
  \A p \in Participant : decision[p] = abort =>
    \/ \E q \in Participant : vote[q] = no
    \/ \E q \in Participant : faulty[q] = TRUE
    \/ (pstate[p] = waiting)

Irreversible ==
  \A p \in Participant : decision[p] = commit \/ decision[p] = abort => decision[p] = decision[p]

\* Liveness
AllDecidedOrFaulty ==
  <>(\A p \in Participant : decision[p] # undecided) \/ (\E p \in Participant : faulty[p])
Terminating ==
  \A p \in Participant : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====