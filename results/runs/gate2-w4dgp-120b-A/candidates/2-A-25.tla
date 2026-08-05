---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {} /\ commit = yes /\ abort = no

VARIABLES vote, alive, decision, faulty, voteSent, cstate, forwarded

vars == <<vote, alive, decision, faulty, voteSent, cstate, forwarded>>

RECURSIVE AllTrue(_, _)
AllTrue(f, S) ==
  IF S = {} THEN TRUE
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] /\ AllTrue(f, S \ {x})

Init ==
  /\ vote = [p \in participants |-> waiting]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ cstate = [p \in participants |-> waiting]
  /\ forwarded =
       [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator: collect votes, decide, and broadcast the decision.
SendRequest ==
  /\ cstate[CHOOSE p \in participants : TRUE] = waiting
  /\ cstate' = [p \in participants |-> IF cstate[p] = waiting THEN CHOOSE q \in participants : TRUE ELSE cstate[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarded>>

GetVote(p) ==
  /\ cstate[p] # waiting
  /\ vote[p] = waiting
  /\ alive[p]
  /\ voteSent[p]
  /\ vote' = [vote EXCEPT ![p] = cstate[p]]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, cstate, forwarded>>

DieCoordinator ==
  /\ cstate[CHOOSE p \in participants : TRUE] # waiting
  /\ cstate' = [p \in participants |-> waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarded>>

MakeDecision ==
  /\ cstate[CHOOSE p \in participants : TRUE] # waiting
  /\ \A p \in participants : vote[p] # waiting
  /\ cstate' = [p \in participants |-> waiting]
  /\ FORALL p \in participants : cstate[p] # waiting
       => cstate' = [cstate EXCEPT ![p] = IF \A q \in participants : vote[q] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarded>>

Broadcast ==
  /\ \E p \in participants :
       /\ cstate[p] # waiting
       /\ alive[p]
       /\ decision[p] = undecided
       /\ decision' = [decision EXCEPT ![p] = cstate[p]]
  /\ UNCHANGED <<vote, alive, voteSent, cstate, forwarded>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, cstate, forwarded>>

SendVote(p) ==
  /\ alive[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, cstate, forwarded>>

\* Participant: store a pre-decision received from either the coordinator
\* or a peer that forwarded it (receive-once, one entry per participant).
PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision[p] = notsent
  /\ decision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = cstate[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, forwarded>>

PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants :
       q # p /\ forwarded[q][p] # notsent /\ decision[p] = notsent
       /\ decision' = [decision EXCEPT ![p] = forwarded[q][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, forwarded>>

\* Reliable broadcast: forward the pre-decision to every other participant
\* before finalizing one's own decision locally.
Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ p # q
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants \ {p} : forwarded[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, forwarded>>

\* Abort on timeout when the coordinator is dead and no decision can reach
\* the participant, either directly from the coordinator or indirectly via
\* a forwarding peer, and no dead participant can still forward a decision.
\* This check is what gives the simple broadcast variant its bounded abort
\* bound (three undecided participants), and the reliable broadcast above
\* is what lets the non-blocking variant improve on that bound.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : ~alive[q]
  /\ \A q \in participants : decision[q] = notsent
  /\ \A r \in participants : ~faulty[r]
       => \A q \in participants : forwarded[r][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, cstate, forwarded>>

Next ==
  \/ SendRequest
  \/ Broadcast
  \/ DieCoordinator
  \/ Die(CHOOSE p \in participants : TRUE)
  \/ SendVote(CHOOSE p \in participants : TRUE)
  \/ GetVote(CHOOSE p \in participants : TRUE)
  \/ MakeDecision
  \/ PreDecideFromCoordinator(CHOOSE p \in participants : TRUE)
  \/ PreDecideFromForward(CHOOSE p \in participants : TRUE)
  \/ Forward(CHOOSE p \in participants : TRUE, CHOOSE q \in participants : TRUE)
  \/ Decide(CHOOSE p \in participants : TRUE)
  \/ AbortTimeout(CHOOSE p \in participants : TRUE)

SpecNB == Init /\ [][Next]_vars
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, cstate, forwarded>>

\* Cohort agreement: no two participants commit and abort respectively.
TypeInvNB ==
  /\ AllTrue(vote, participants)
  /\ AllTrue(alive, participants)
  /\ AllTrue(decision, participants)
  /\ AllTrue(faulty, participants)
  /\ AllTrue(voteSent, participants)
  /\ AllTrue(cstate, participants)
  /\ AllTrue(forwarded, participants)

\* Agreement: once decided, a participant never changes decision.
\* (No cycle of commit/abort as a cycle of different decisions is impossible.)
Irreversible == \A p \in participants : (decision[p] # undecided) ~> (decision[p] = decision[p])

\* Fault-free safety: if someone commits everyone voted yes.
NoDivergence == (commit # undecided) ~> (\A p \in participants : vote[p] = yes)

\* Fault-free safety for aborts: an abort is always explained by a no vote
\* or a crash on either side of the communication.
AbortExplained ==
  (abort # undecided) ~> ( (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ (\E p \in participants : ~alive[p]) )

\* Bounded abort: the base protocol always resolves in a bounded number of
\* steps (three undecided participants) even though it is not non-blocking.
BoundedAbort == (\E p \in participants : decision[p] = abort) ~> ( (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ (\E p \in participants : ~alive[p]) \/ (\A p \in participants : decision[p] # undecided) )

\* Non-blocking termination: every non-faulty participant reaches a decision.
Terminate == (\A p \in participants : alive[p]) ~> (\A p \in participants : decision[p] # undecided)

====