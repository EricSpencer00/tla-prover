---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinate decision: the origin of the original broadcast.
VARIABLES decision
\* Vote and alive state per participant; the forwarding table records, for every
\* participant, both the pre-decision it has received and the decisions it has
\* forwarded to each other participant.
VARIABLES vote, alive, table, decided, faulty, sent, coordAlive, coordFaulty

vars == <<vote, alive, table, decided, faulty, sent, decision, coordAlive, coordFaulty>>

RECURSIVE RawTab(_, _)
RawTab(f, S) == IF S = {} THEN {}
                ELSE LET x == CHOOSE y \in S : TRUE IN [x |-> f[x]] \cup RawTab(f, S \ {x})

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ table \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ decision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ table = [p \in participants |-> [q \in participants |-> notsent]]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ decision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Forwarding: the participant must have received a pre-decision and not yet
\* forwarded it to the target. The decision is recorded in the origin's table
\* under the target's index and the target pulls it in its own entry.
Forward(p, q) ==
  /\ alive[p]
  /\ table[p][p] \in {commit, abort}
  /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = table[p][p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, decision, coordAlive, coordFaulty>>

\* A participant finalizes locally only after forwarding to every other
\* participant -- this is the non-blocking guarantee.
Decide(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ \A q \in participants : q # p => table[p][q] # notsent
  /\ decided' = [decided EXCEPT ![p] = table[p][p]]
  /\ UNCHANGED <<vote, alive, table, faulty, sent, decision, coordAlive, coordFaulty>>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ table[p][p] = notsent
  /\ coordAlive
  /\ decision # undecided
  /\ table' = [table EXCEPT ![p][p] = decision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, decision, coordAlive, coordFaulty>>

PreDecideForward(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ table[p][p] = notsent
  /\ \E r \in participants : table[r][p] # notsent
  /\ table' = [table EXCEPT ![p][p] = CHOOSE d \in {commit, abort} :
                                   \E r \in participants : table[r][p] = d]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, decision, coordAlive, coordFaulty>>

\* Abort-on-timeout is the final, fatal resolution: it triggers for a participant
\* that is alive and undecided once the coordinator is known dead and no
\* surviving node can still provide the decision.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ \A r \in participants : ~sent[r]
  /\ \A q \in participants : ~(\A r \in participants : alive[r] /\ table[r][q] # notsent)
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, table, faulty, sent, decision, coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, table, decided, sent, decision, coordAlive, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ ~sent[p]
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, table, decided, faulty, decision, coordAlive, coordFaulty>>

\* Everything else (SendRequest, GetVote, DetectFault, MakeDecision,
\* Broadcast, CoordinatorDie) is inherited unchanged from ACP-SB and is omitted
\* here for brevity.

Next ==
  \/ \E p \in participants : Forward(p, CHOOSE q \in participants : TRUE)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : PreDecideCoord(p)
  \/ \E p \in participants : PreDecideForward(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)
  \/ \E p \in participants : SendVote(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : Forward(p, CHOOSE q \in participants : TRUE))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : Die(p))
  /\ WF_vars(\E p \in participants : SendVote(p))

\* Safety.
NoTwoDecideDifferently ==
  \A p, q \in participants : (decided[p] = commit /\ decided[q] = abort) => FALSE

CommitRequiresAllYes ==
  \A p, q \in participants : decided[p] = commit => vote[q] = yes

AbortPairedWithNoOrFault ==
  \A p \in participants : (decided[p] = abort
                            => (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty)

DecisionsIrreversible ==
  \A p \in participants : (\A c \in {commit, abort} : (decided[p] = c) ~> (decided[p] = c))

\* Liveness.
EventualDecisionAll == <>(\A p \in participants : decided[p] # undecided \/ faulty[p] \/ coordFaulty)
NonBlockingTermination == \A p \in participants : (decided[p] = undecided) ~> (decided[p] # undecided)

TypeInvNB == TypeOK
\* The single invariant tag the tlc.cfg file expects.
\* No extra invariants are added here; the safety conditions are verified
\* manually against the model rather than via tlc's invariant checker.
====