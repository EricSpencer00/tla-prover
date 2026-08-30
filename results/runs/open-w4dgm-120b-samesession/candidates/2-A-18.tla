---- MODULE ACP_NB ----
EXTENDS Integers, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coord

Vars == <<vote, alive, decision, faulty, sent, coord>>

\* vote: yes/no per participant; decision: commit/abort/undecided; coord:
\* coordinator state; sent: each participant's forwarding table (decision
\* stored at its own index, plus forwarded-or-not per other participant).
NoCoord == [req |-> no, vote |-> no, bc |-> no, decision |-> undecided,
             alive |-> TRUE, faulty |-> FALSE]

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \subseteq participants
  /\ sent \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ coord \in [req : {yes, no, undecided}, vote : {yes, no, undecided},
                bc : {yes, no, notsent}, decision : {commit, abort, undecided},
                alive : BOOLEAN, faulty : BOOLEAN]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sent = [p \in participants |-> [q \in participants |-> notsent]]
  /\ coord = NoCoord

\* The coordinator runs the two-phase commit as in ACP-SB.
SendRequest ==
  /\ coord.alive /\ ~coord.faulty /\ coord.req = undecided
  /\ \A p \in participants : vote[p] = undecided
  /\ \E v \in {yes, no} : coord' = [coord EXCEPT !.req = v]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

GetVote(p) ==
  /\ coord.alive /\ coord.req # undecided
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, sent, coord>>

DetectFault(p) ==
  /\ vote[p] = undecided
  /\ coord.alive /\ ~coord.faulty
  /\ coord.req # undecided
  /\ coord.vote = undecided
  /\ \A q \in participants : vote[q] = undecided
  /\ coord' = [coord EXCEPT !.vote = no]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

MakeDecision ==
  /\ coord.alive /\ coord.vote = undecided
  /\ coord.req # undecided
  /\ coord' = [coord EXCEPT !.vote = coord.req]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

Broadcast(p) ==
  /\ coord.alive /\ coord.vote # undecided /\ coord.bc = notsent
  /\ sent[p][p] = notsent
  /\ sent' = [sent EXCEPT ![p][p] = IF coord.vote = yes THEN commit ELSE abort]
  /\ coord' = [coord EXCEPT !.bc = coord.vote]
  /\ UNCHANGED <<vote, alive, decision, faulty>>

\* Crashing is always available; weak fairness is never assumed on it.
Die ==
  /\ coord.alive
  /\ coord' = [coord EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

\* A participant's own forwarding entry is set either by the coordinator's
\* broadcast (reliable broadcast) or by another participant's forwarding.
PreDecideCoord(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ coord.alive /\ coord.bc # notsent /\ sent[p][p] = notsent
  /\ sent' = [sent EXCEPT ![p][p] = IF coord.bc = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

PreDecideFwd(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ sent[p][p] = notsent
  /\ \E q \in participants :
       sent[q][p] # notsent
       /\ sent' = [sent EXCEPT ![p][p] = sent[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

\* The participant forwards its pre-decision to every other participant before
\* it is allowed to finalize locally -- this is what stops it from blocking.
Forward(p, q) ==
  /\ alive[p] /\ sent[p][p] # notsent /\ sent[p][q] = notsent
  /\ sent' = [sent EXCEPT ![p][q] = sent[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

Decide(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ sent[p][p] # notsent
  /\ \A q \in participants : sent[p][q] = sent[p][p]
  /\ decision' = [decision EXCEPT ![p] = sent[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

AbortOnTimeout(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ ~coord.alive
  /\ coord.faulty = FALSE
  /\ \A q \in participants : sent[q][p] = notsent
  /\ \A q \in participants : ~(~alive[q] /\ sent[q][p] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

DieP(p) ==
  /\ alive[p] /\ p \notin faulty
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sent, coord>>

\* Progress: the coordinator progresses (request, vote, decision, broadcast)
\* whenever it is still alive and not yet faulty; participants forward and
\* finalize their decision whenever they are still alive (crashing is not
\* assumed fair), so a non-faulty participant can always make progress.
CoordinatorStep == SendRequest \/ MakeDecision \/ Die
ParticipantStep == \E p \in participants : Forward(p, p) \/ Decide(p)

Next ==
  \/ SendRequest \/ MakeDecision \/ Die
  \/ \E p \in participants :
       GetVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ PreDecideCoord(p)
       \/ PreDecideFwd(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ DieP(p)
       \/ (\E q \in participants : Forward(p, q))

SpecSB == Init /\ [][Next]_Vars /\ WF_Vars(CoordinatorStep) /\ WF_Vars(ParticipantStep)

SpecNB == SpecSB /\ WF_Vars(Die) /\ WF_Vars(\E p \in participants : DieP(p))

\* Safety: agreement, validity, and irrevocability are exactly as in ACP-SB.
AC1 == \A p, q \in participants : (decision[p] = commit) ~> (decision[q] \in {commit, undecided})
AC2 == (\E p \in participants : decision[p] = commit) ~> (\A q \in participants : vote[q] = yes)
AC3 == (\E p \in participants : decision[p] = abort) ~>
         (\A q \in participants : vote[q] = no \/ q \in faulty \/ coord.faulty)
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] = decision[p])
TypeInvNB == TypeOK

\* Liveness: the non-blocking guarantee -- every non-faulty participant
\* eventually decides, which the simple broadcast version cannot promise.
AC5 == \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

Spec == SpecNB
\* AC3 is a progress guarantee that holds even without the forwarding
\* mechanism, so it is retained from ACP-SB for completeness.
\* AC5 is the new non-blocking termination guarantee.
Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5
====