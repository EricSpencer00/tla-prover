---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: a participant forwards its pre-decision to all others
\* before finalizing locally, so a coordinator crash cannot strand the rest.
\* The state extends the simple broadcast protocol with a forwarding table
\* per participant (what it got and what it has forwarded).

VARIABLES vote, alive, decision, faulty, sentVote, forwarded, coordinator

vars == <<vote, alive, decision, faulty, sentVote, forwarded, coordinator>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ coordinator \in [alive : BOOLEAN, faulty : BOOLEAN,
                       req : BOOLEAN, phase : {"init", "voting", "decided"},
                       decision : {commit, abort, waiting}]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
  /\ coordinator = [alive |-> TRUE, faulty |-> FALSE, req |-> FALSE,
                    phase |-> "init", decision |-> waiting]

\* Coordinator opens a two-phase-commit round for the shared update.
Request ==
  /\ coordinator.alive
  /\ coordinator.phase = "init"
  /\ coordinator' = [coordinator EXCEPT !.phase = "voting", !.req = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, forwarded>>

\* A participant casts its single vote for the current round.
SendVote(p) ==
  /\ coordinator.phase = "voting"
  /\ alive[p]
  /\ ~sentVote[p]
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, forwarded, coordinator>>

\* Vote no: a strict participant aborts the round globally.
AbortOnVote(p) ==
  /\ coordinator.phase = "voting"
  /\ alive[p]
  /\ vote[p] = no
  /\ coordinator' = [coordinator EXCEPT !.phase = "decided",
                     !.decision = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, forwarded>>

\* Coordinator dies mid-round; participants must rely on forwarding.
DetectFault ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, forwarded>>

\* Coordinator decides commit with unanimity and broadcasts it.
Decide ==
  /\ coordinator.phase = "voting"
  /\ coordinator.alive
  /\ \A p \in participants : vote[p] = yes
  /\ coordinator' = [coordinator EXCEPT !.phase = "decided",
                     !.decision = commit]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, forwarded>>

Broadcast(p) ==
  /\ coordinator.phase = "decided"
  /\ coordinator.alive
  /\ ~faulty[p]
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordinator.decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinator>>

\* A participant may receive a broadcast pre-decision from the coordinator.
PreDecideFromCoordinator(p) ==
  /\ coordinator.phase = "decided"
  /\ ~faulty[p]
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordinator.decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinator>>

\* A participant may receive a pre-decision forwarded from another participant.
PreDecideFromForward(p) ==
  /\ ~faulty[p]
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ forwarded[q][p] # notsent
       /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinator>>

\* Forward a received pre-decision to another participant that has none.
Forward(p, q) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ p # q
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinator>>

\* Once a pre-decision has been forwarded to everyone, finalize locally.
DecideLocally(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants : q # p => forwarded[p][q] # notsent
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, forwarded, coordinator>>

\* Timeout: with the coordinator dead and no reliable broadcast path left,
\* a participant aborts rather than wait forever.
AbortOnTimeout(p) ==
  /\ ~coordinator.alive
  /\ decision[p] = waiting
  /\ \A q \in participants :
       \/ coordinator.alive
       \/ forwarded[q][p] # notsent
  /\ coordinator.faulty \/ \E q \in participants : faulty[q]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, forwarded, coordinator>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, forwarded, coordinator>>

\* Every non-faulty participant must still be able to finalize through
\* forwarding alone, so an abort must always be reachable even if the
\* coordinator dies before it.
Stall == UNCHANGED vars /\ coordinator.alive /\ coordinator.phase = "init"

Next ==
  \/ Request \/ DetectFault \/ Decide \/ Stall
  \/ \E p \in participants :
       \/ SendVote(p) \/ AbortOnVote(p) \/ Broadcast(p)
       \/ PreDecideFromCoordinator(p) \/ PreDecideFromForward(p)
       \/ DecideLocally(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : DecideLocally(p))

\* At most one of commit or abort is reachable from the start: the two
\* outcomes are mutually exclusive branches of the two-phase protocol.
AC1 == \A p, q \in participants : ~ (decision[p] = commit /\ decision[q] = abort)

\* A commit is only possible through a unanimous yes vote.
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort is always rationalized by a no vote or a participant fault.
AC3 == \A p \in participants : decision[p] = abort =>
         \/ \E q \in participants : vote[q] = no
         \/ \E q \in participants : faulty[q]
         \/ coordinator.faulty

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

AC5 == \A p \in participants : ~faulty[p] ~> decision[p]

\* AC3 is the non-trivial branch: every participant's abort must be
\* justified, so the abort outcome is always reachable (not a deadlock).
\* AC4 is per participant; AC5 is per non-faulty participant.
Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5

TypeInvNB == TypeOK /\ coordinator.phase \in {"init", "voting", "decided"}

====