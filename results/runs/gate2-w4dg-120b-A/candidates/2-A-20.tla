---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol with Reliable Broadcast forwarding
\* (ACPs extension on top of the simple broadcast variant ACP-SB).
\* Coordinator can crash silently; participants forward decisions to each
\* other participant so that a non-faulty participant always eventually decides.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, prefwd, coord

vars == <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

RECURSIVE FwdOver(_, _)
FwdOver(a, S) ==
  IF S = {} THEN {notsent}
  ELSE LET x == CHOOSE e \in S : TRUE IN prefwd[a][x] \cup FwdOver(a, S \ {x})

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ prefwd \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ coord \in [phase |-> {waiting, collecting, deciding, broadcasting},
                decision |-> {undecided, commit, abort},
                alive |-> BOOLEAN, faulty |-> BOOLEAN]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ prefwd = [p \in participants |-> [q \in participants |-> notsent]]
  /\ coord = [phase |-> waiting, decision |-> undecided,
              alive |-> TRUE, faulty |-> FALSE]

\* Coordinator sends a request to all participants.
SendRequest ==
  /\ coord.phase = waiting
  /\ coord.phase' = collecting
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

\* A participant votes yes or no.
SendVote(p) ==
  /\ alive[p]
  /\ coord.phase = collecting
  /\ ~voteSent[p]
  /\ pstate' = [pstate EXCEPT ![p] =
                  IF Cardinality({q \in participants : pstate[q] = no}) = 0
                  THEN yes ELSE no]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<decision, faulty, prefwd, coord, alive>>

\* Coordinator detects a faulty participant and can retry the vote phase.
DetectFault(p) ==
  /\ coord.phase = collecting
  /\ ~alive[p]
  /\ coord.phase' = collecting
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

\* Coordinator decides commit or abort once all votes are in.
MakeDecision ==
  /\ alive[coord]
  /\ coord.phase = collecting
  /\ \A p \in participants : voteSent[p]
  /\ coord.decision' = IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort
  /\ coord.phase' = deciding
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

\* Coordinator broadcasts its decision to every participant.
BroadcastDecision ==
  /\ coord.phase = deciding
  /\ coord.phase' = broadcasting
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

\* Coordinator crashes silently.
CoordDie ==
  /\ alive[coord]
  /\ coord.alive' = FALSE
  /\ coord.phase' = collecting
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, prefwd, coord>>

\* A participant receives the coordinator's decision (pre-decision).
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ prefwd[p][p] = notsent
  /\ coord.phase = broadcasting
  /\ prefwd' = [prefwd EXCEPT ![p][p] = coord.decision]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord>>

\* A participant receives a forwarded decision from another participant.
PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ prefwd[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ prefwd[q][p] # notsent
       /\ prefwd' = [prefwd EXCEPT ![p][p] = prefwd[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ prefwd[p][p] # notsent
  /\ prefwd[p][q] = notsent
  /\ prefwd' = [prefwd EXCEPT ![p][q] = prefwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord>>

\* A participant finalizes once it has forwarded to everybody else.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ prefwd[p][p] # notsent
  /\ FwdOver(p, participants) = {prefwd[p][p]}
  /\ decision' = [decision EXCEPT ![p] = prefwd[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, prefwd, coord>>

\* Abort when the coordinator has died and no forward path remains.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive[coord]
  /\ \A q \in participants : prefwd[coord][q] = notsent
  /\ \A q \in participants, r \in participants :
       ~(~alive[q] /\ prefwd[q][r] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, prefwd, coord>>

\* A participant crashes silently (becomes faulty).
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, prefwd, coord>>

Next ==
  \/ SendRequest \/ MakeDecision \/ BroadcastDecision \/ CoordDie
  \/ \E p \in participants :
       \/ SendVote(p) \/ DetectFault(p) \/ PreDecideFromCoord(p)
       \/ PreDecideFromFwd(p) \/ Decide(p) \/ AbortTimeout(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
          /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
          /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
          /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
          /\ WF_vars(\E p \in participants : Decide(p))
          /\ WF_vars(\E p \in participants : AbortTimeout(p))
          /\ WF_vars(\E p \in participants : Die(p))

\* AC1: no two participants ever disagree on the final decision.
Agreement ==
  \A p \in participants : \A q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* AC2: a commit can only happen when all participants voted yes.
CommitValidity ==
  decision[CHOOSE p \in participants : TRUE] = commit =>
    (\A p \in participants : pstate[p] = yes)

\* AC3: an abort is always backed by a no vote or a crash (coordinator or participant).
AbortValidity ==
  decision[CHOOSE p \in participants : TRUE] = abort =>
    (\E p \in participants : pstate[p] = no \/ faulty[p] \/ ~alive[coord])

\* AC4: decisions are irrevocable -- once decided, it never flips.
Irreversibility ==
  \A p \in participants :
    decision[p] = commit => decision' = [decision EXCEPT ![p] = commit]
    /\ decision[p] = abort => decision' = [decision EXCEPT ![p] = abort]

\* AC3 liveness: at least one participant decides, or someone crashes.
EventualDecision ==
  <>(\E p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p])

\* AC5: every non-faulty participant eventually reaches a decision.
EventualDecisionAll == <>(\A p \in participants : decision[p] # undecided)

TypeInvNB == TypeOK

====