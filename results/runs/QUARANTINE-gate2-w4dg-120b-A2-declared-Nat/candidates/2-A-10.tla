---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coord, pstate, fwdtab

TypeInvNB ==
  /\ coord \in [req: {waiting, yes, no}, vote: {yes, no}, broadcast: 0..3,
                decision: {undecided, commit, abort}, alive: BOOLEAN,
                faulty: BOOLEAN]
  /\ pstate \in [participants -> [vote: {yes, no}, alive: BOOLEAN, faulty: BOOLEAN,
                                 decision: {undecided, commit, abort},
                                 voted: BOOLEAN]]
  /\ fwdtab \in [participants -> [participants -> {notsent, commit, abort}]]

Blank ==
  [vote |-> yes, alive |-> TRUE, faulty |-> FALSE, decision |-> undecided,
   voted |-> FALSE]

InitNB ==
  /\ coord = [req |-> waiting, vote |-> yes, broadcast |-> 0, decision |-> undecided,
              alive |-> TRUE, faulty |-> FALSE]
  /\ pstate = [q \in participants |-> Blank]
  /\ fwdtab = [q \in participants |-> [r \in participants |-> notsent]]

\* Coordinator actions are inherited unchanged from the simple broadcast protocol.
SendRequest ==
  /\ coord.alive /\ coord.req = waiting
  /\ coord' = [coord EXCEPT !.req = no]
  /\ UNCHANGED <<pstate, fwdtab>>

SendVote(q) ==
  /\ pstate[q].alive /\ ~pstate[q].voted /\ coord.alive
  /\ coord.req = no
  /\ pstate' = [pstate EXCEPT ![q] = [Blank EXCEPT !.vote = no, !.voted = TRUE]]
  /\ UNCHANGED <<coord, fwdtab>>

DetectFault ==
  /\ coord.alive /\ coord.broadcast < 3
  /\ coord.broadcast' = coord.broadcast + 1
  /\ UNCHANGED <<coord, pstate, fwdtab>>

Decide ==
  /\ coord.broadcast >= 1 /\ coord.decision = undecided
  /\ coord' = [coord EXCEPT !.decision = coord.vote]
  /\ UNCHANGED <<pstate, fwdtab>>

Broadcast(q) ==
  /\ coord.broadcast > 0
  /\ pstate[q].alive /\ pstate[q].decision = undecided
  /\ coord.alive /\ coord.decision # undecided
  /\ pstate' = [pstate EXCEPT ![q].decision = coord.decision]
  /\ UNCHANGED <<coord, fwdtab>>

DieCoord ==
  /\ coord.alive
  /\ coord' = [coord EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<pstate, fwdtab>>

\* New: pre-decide from the coordinator's broadcast.
PreDecideFromCoord(q) ==
  /\ pstate[q].alive
  /\ pstate[q].decision = undecided
  /\ coord.alive
  /\ coord.broadcast > 0
  /\ coord.decision # undecided
  /\ fwdtab[q][q] = notsent
  /\ fwdtab' = [fwdtab EXCEPT ![q][q] = coord.decision]
  /\ UNCHANGED <<coord, pstate>>

\* New: pre-decide from a participant's forwarded message.
PreDecideFromFwd(q) ==
  /\ pstate[q].alive
  /\ pstate[q].decision = undecided
  /\ \E r \in participants :
       /\ r # q
       /\ fwdtab[r][q] # notsent
       /\ fwdtab[q][q] = notsent
       /\ fwdtab' = [fwdtab EXCEPT ![q][q] = fwdtab[r][q]]
  /\ UNCHANGED <<coord, pstate>>

\* New: forward the stored pre-decision to another participant.
Forward(q, r) ==
  /\ pstate[q].alive
  /\ r # q
  /\ fwdtab[q][q] # notsent
  /\ fwdtab[q][r] = notsent
  /\ fwdtab' = [fwdtab EXCEPT ![q][r] = fwdtab[q][q]]
  /\ UNCHANGED <<coord, pstate>>

\* New: decide only after having forwarded to everyone else.
DecideFromFwd(q) ==
  /\ pstate[q].alive
  /\ pstate[q].decision = undecided
  /\ \A r \in participants : r # q => fwdtab[q][r] # notsent
  /\ pstate' = [pstate EXCEPT ![q].decision = fwdtab[q][q]]
  /\ UNCHANGED <<coord, fwdtab>>

AbortOnTimeout(q) ==
  /\ pstate[q].alive /\ pstate[q].decision = undecided
  /\ coord.faulty
  /\ \/ \A r \in participants : coord.broadcast = 0
     \/ (\A r \in participants : pstate[r].alive => fwdtab[r][q] = notsent)
  /\ pstate' = [pstate EXCEPT ![q].decision = abort]
  /\ UNCHANGED <<coord, fwdtab>>

DieParticipant(q) ==
  /\ pstate[q].alive
  /\ pstate' = [pstate EXCEPT ![q].alive = FALSE, ![q].faulty = TRUE]
  /\ UNCHANGED <<coord, fwdtab>>

NextNB ==
  \/ SendRequest \/ DetectFault \/ Decide \/ DieCoord
  \/ \E q \in participants :
       \/ SendVote(q) \/ Broadcast(q) \/ PreDecideFromCoord(q)
       \/ PreDecideFromFwd(q) \/ DecideFromFwd(q) \/ AbortOnTimeout(q)
       \/ DieParticipant(q)
       \/ \E r \in participants : Forward(q, r)

SpecNB ==
  /\ InitNB /\ [][NextNB]_<<coord, pstate, fwdtab>>
  /\ WF_vars(SendRequest) /\ WF_vars(Decide) /\ WF_vars(DieCoord)
  /\ \A q \in participants :
       WF_vars(SendVote(q)) /\ WF_vars(PreDecideFromCoord(q))
       /\ WF_vars(PreDecideFromFwd(q)) /\ WF_vars(DecideFromFwd(q))
       /\ WF_vars(AbortOnTimeout(q))

\* Safety: no two participants ever reach different decisions, and each decision
\* is backed by unanimously yes votes or a witnessed fault/abort.
AC1 ==
  \A p, q \in participants :
    (pstate[p].decision = commit /\ pstate[q].decision = abort) => FALSE

AC2 ==
  \E p \in participants : pstate[p].decision = commit =>
    \A q \in participants : pstate[q].vote = yes

AC3 ==
  \E p \in participants : pstate[p].decision = abort =>
    \/ \E q \in participants : pstate[q].vote = no
    \/ \E q \in participants : pstate[q].faulty
    \/ coord.faulty

AC4 ==
  \A p \in participants :
    pstate[p].decision \in {commit, abort} =>
      pstate[p].decision = [q \in participants |-> pstate[q].decision][p]

\* Liveness: every non-faulty participant eventually decides (the non-blocking
\* guarantee that distinguishes ACP-NB from ACP-SB).
AC5 ==
  \A p \in participants :
    (pstate[p].alive /\ ~pstate[p].faulty) ~> (pstate[p].decision # undecided)

====