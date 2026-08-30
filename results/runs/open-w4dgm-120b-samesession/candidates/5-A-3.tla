---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The system tracks the two-sided state of the vote exchange: the coordinator
\* collects votes from participants, then broadcasts its decision back out.
\* Both sides can die silently at any time, which is what makes this a blocking
\* protocol under failures.
VARIABLES pstate, coord

vars == <<pstate, coord>>

TypeOK ==
  /\ pstate \in [participants -> [vote: {yes, no}, alive: BOOLEAN,
                                  decision: {undecided, commit, abort},
                                  fatal: BOOLEAN, sent: BOOLEAN,
                                  rcvd: {waiting, yes, no}]]
  /\ coord \in [asked: [participants -> BOOLEAN],
                rv: [participants -> {waiting, yes, no}],
                sentTo: [participants -> {notsent, commit, abort}],
                decision: {undecided, commit, abort},
                alive: BOOLEAN, fatal: BOOLEAN]

Init ==
  /\ pstate = [p \in participants |-> [vote |-> CHOOSE v \in {yes, no} : TRUE,
                                      alive |-> TRUE, decision |-> undecided,
                                      fatal |-> FALSE, sent |-> FALSE, rcvd |-> waiting]]
  /\ coord = [asked |-> [p \in participants |-> FALSE],
              rv |-> [p \in participants |-> waiting], sentTo |-> [p \in participants |-> notsent],
              decision |-> undecided, alive |-> TRUE, fatal |-> FALSE]

\* The coordinator only asks for a participant's vote while it is alive and
\* undecided; a crashed coordinator freezes the request phase in place.
AskVote(p) ==
  /\ coord.alive /\ coord.decision = undecided /\ ~coord.asked[p]
  /\ coord' = [coord EXCEPT !.asked[p] = TRUE]
  /\ UNCHANGED <<pstate>>

RecvVote(p) ==
  /\ coord.alive /\ coord.decision = undecided /\ coord.asked[p]
  /\ coord.rv[p] = waiting /\ pstate[p].sent
  /\ coord' = [coord EXCEPT !.rv[p] = pstate[p].vote]
  /\ UNCHANGED <<pstate>>

DetectFault(p) ==
  /\ coord.alive /\ coord.decision = undecided /\ coord.asked[p]
  /\ coord.rv[p] = waiting /\ ~pstate[p].alive /\ ~pstate[p].sent
  /\ coord' = [coord EXCEPT !.decision = abort]
  /\ UNCHANGED <<pstate>>

Decide ==
  /\ coord.alive /\ coord.decision = undecided
  /\ \A p \in participants : coord.asked[p]
  /\ coord.decision' = IF \A p \in participants : coord.rv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, coord>>

\* Simple broadcast: a decided coordinator sends its decision one participant
\* at a time, in whatever order it happens to get to. A crash here is fatal to
\* the participants it has not yet reached.
Broadcast(p) ==
  /\ coord.alive /\ coord.decision # undecided
  /\ coord.sentTo[p] = notsent
  /\ coord' = [coord EXCEPT !.sentTo[p] = coord.decision]
  /\ UNCHANGED <<pstate>>

CoordDie ==
  /\ coord.alive /\ coord.alive' = FALSE /\ coord.fatal' = TRUE
  /\ UNCHANGED <<pstate, coord>>

Vote(p) ==
  /\ pstate[p].alive /\ coord.asked[p] /\ ~pstate[p].sent
  /\ pstate' = [pstate EXCEPT ![p].sent = TRUE]
  /\ UNCHANGED <<coord>>

AbortOnVote(p) ==
  /\ pstate[p].alive /\ pstate[p].decision = undecided
  /\ pstate[p].sent /\ pstate[p].vote = no
  /\ pstate' = [pstate EXCEPT ![p].decision = abort]
  /\ UNCHANGED <<coord>>

AbortOnTimeout(p) ==
  /\ pstate[p].alive /\ pstate[p].decision = undecided
  /\ ~coord.asked[p] /\ ~coord.alive
  /\ pstate' = [pstate EXCEPT ![p].decision = abort]
  /\ UNCHANGED <<coord>>

DecideOnBroadcast(p) ==
  /\ pstate[p].alive /\ pstate[p].decision = undecided
  /\ coord.sentTo[p] # notsent
  /\ pstate' = [pstate EXCEPT ![p].decision = coord.sentTo[p]]
  /\ UNCHANGED <<coord>>

PartDie(p) ==
  /\ pstate[p].alive /\ pstate[p].alive' = FALSE /\ pstate[p].fatal' = TRUE
  /\ UNCHANGED <<pstate, coord>>

Next ==
  \/ Decide
  \/ \E p \in participants :
       \/ AskVote(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
       \/ Vote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p)
       \/ PartDie(p)
  \/ CoordDie

\* SAFETY: any pair of participants that both resolved must have resolved the
\* same way -- this is the pairwise decision equivalence the spec demands.
DecisionCoherence ==
  \A p, q \in participants :
    /\ (pstate[p].decision = commit /\ pstate[q].decision = abort) => FALSE
    /\ (pstate[p].decision = abort /\ pstate[q].decision = commit) => FALSE

\* LIVENESS: either everything resolves, or a crash leaves it hanging -- it
\* never refuses to resolve without a crash having actually happened.
ResolutionOrCrash ==
  (<>(\A p \in participants : pstate[p].decision # undecided)) \/ (\E p \in participants : pstate[p].fatal \/ coord.fatal)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : Vote(p))
  /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

TypeInv == TypeOK
====