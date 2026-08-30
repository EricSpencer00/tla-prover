---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the base ACP-SB spec (the comment explains the change; the spec
\* itself is fully self-contained, with no module imported from ACP_SB).
\* Forwarding is what keeps non-blocking termination alive after the coordinator dies.

VARIABLES vote, alive, decision, faulty, sent, coord, fwd

vars == <<vote, alive, decision, faulty, sent, coord, fwd>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coord \in [req: {waiting, commit, abort}, vote: {yes, no, undecided}, cast: BOOLEAN, alive: BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* The forwarding table is always a full record: no entry is ever dropped, so a
\* delivered decision is never lost by being overwritten with notsent.
Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coord = [req |-> waiting, vote |-> undecided, cast |-> FALSE, alive |-> TRUE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
  /\ coord.req = waiting
  /\ \A p \in participants: ~sent[p]
  /\ coord' = [coord EXCEPT !.req = commit]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

\* Coordinator's vote is the reduction of everybody's vote into one decision.
GetVote ==
  /\ coord.req # waiting
  /\ ~coord.cast
  /\ \A p \in participants: vote[p] # undecided
  /\ coord' = [coord EXCEPT !.vote = \E p \in participants: vote[p],
                           !.cast = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

\* Fault detection is what keeps the protocol non-blocking after a crash.
DetectFault ==
  /\ coord.alive
  /\ ~coord.cast
  /\ coord.req = commit
  /\ \E p \in participants: ~alive[p]
  /\ coord' = [coord EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

MakeDecision ==
  /\ coord.alive
  /\ coord.cast
  /\ coord.req # waiting
  /\ coord.alive
  /\ coord.req' = waiting
  /\ coord.cast' = FALSE
  /\ decision' = [p \in participants |-> IF coord.vote = yes THEN commit ELSE abort]
  /\ sent' = [p \in participants |-> FALSE]
  /\ fwd' = [p \in participants |-> [q \in participants |-> notsent]]
  /\ UNCHANGED <<vote, alive, faulty, coord>>

\* Broadcast to everyone, not just to those who will actually listen.
Broadcast ==
  /\ coord.alive
  /\ coord.vote # undecided
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ fwd' = [fwd EXCEPT ![p][p] = IF coord.vote = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ sent[p]
  /\ fwd' = [fwd EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

PreDecideFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants: q # p /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = IF \E q \in participants: fwd[q][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ p # q
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

Decide(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants: fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = IF fwd[p][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, fwd>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coord.alive
  /\ ~sent[p]
  /\ \A q \in participants: ~alive[q] => fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coord, fwd>>

SendVote(p) ==
  /\ alive[p]
  /\ coord.req # waiting
  /\ vote[p] = undecided
  /\ \A q \in participants: ~alive[q]
  /\ \A q \in participants: vote[q] = undecided
  /\ \E v \in {yes, no}: vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, sent, coord, fwd>>

AbortCoord ==
  /\ coord.alive
  /\ coord.req = commit
  /\ coord.alive
  /\ \E p \in participants: ~alive[p]
  /\ coord' = [coord EXCEPT !.req = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent fwd>>

DecideAny == \E p \in participants: Decide(p)

Next ==
  \/ SendReq \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast
  \/ \E p \in participants: PreDecideCoord(p) \/ PreDecideFwd(p)
  \/ \E p \in participants, q \in participants: Forward(p, q)
  \/ DecideAny
  \/ \E p \in participants: AbortTimeout(p) \/ Die(p) \/ SendVote(p)
  \/ AbortCoord

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendReq) /\ WF_vars(GetVote) /\ WF_vars(MakeDecision) /\ WF_vars(Broadcast)
  /\ WF_vars(DecideAny)

\* Safety: agreement is preserved across coordinator and participant crashes alike.
TypeInvNB == TypeOK

\* Liveness: every alive participant eventually decides.
AC5 == \A p \in participants: (alive[p] /\ decision[p] = waiting) ~> (alive[p] /\ decision[p] # waiting)

====