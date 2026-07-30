---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The forwarding table is a per-participant map: for each participant it records
\* (a) the pre-decision this participant has received for itself, and (b) which
\* other participants it has forwarded that pre-decision to.
VARIABLES pstate, coord, fwd

vars == << pstate, coord, fwd >>

States == {undecided, commit, abort}
FwdStates == {notsent, commit, abort}

TypeInvNB ==
  /\ pstate \in [participants -> [vote : {yes, no}, alive : BOOLEAN,
                      decision : States, faulty : BOOLEAN, sent : BOOLEAN]]
  /\ coord \in [request : {yes, no, waiting}, vote : {yes, no, waiting},
               broadcast : {yes, no, waiting}, decision : {yes, no},
               alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> FwdStates]]

Init ==
  /\ pstate = [p \in participants |->
                 [vote |-> undecided, alive |-> TRUE, decision |-> undecided,
                  faulty |-> FALSE, sent |-> FALSE]]
  /\ coord = [request |-> waiting, vote |-> waiting, broadcast |-> waiting,
              decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorSendRequest(r) ==
  /\ coord.alive
  /\ coord.request = waiting
  /\ pstate[r].vote = undecided
  /\ coord' = [coord EXCEPT !.request = pstate[r].vote]
  /\ UNCHANGED << pstate, fwd >>

CoordinatorCollectVote(v) ==
  /\ coord.alive
  /\ coord.vote = waiting
  /\ coord.request # waiting
  /\ coord' = [coord EXCEPT !.vote = v]
  /\ UNCHANGED << pstate, fwd >>

CoordinatorDetectFault(p) ==
  /\ coord.alive
  /\ pstate[p].vote = waiting
  /\ coord' = [coord EXCEPT !.faulty = TRUE]
  /\ UNCHANGED << pstate, fwd >>

CoordinatorMakeDecision ==
  /\ coord.alive
  /\ coord.vote # waiting
  /\ coord.decision = undecided
  /\ coord' = [coord EXCEPT !.decision = coord.vote,
               !.broadcast = coord.vote]
  /\ UNCHANGED << pstate, fwd >>

CoordinatorBroadcast ==
  /\ coord.alive
  /\ coord.broadcast \in {yes, no}
  /\ coord' = [coord EXCEPT !.broadcast = coord.vote]
  /\ UNCHANGED << pstate, fwd >>

CoordinatorDie ==
  /\ coord.alive
  /\ coord' = [coord EXCEPT !.alive = FALSE]
  /\ UNCHANGED << pstate, fwd >>

SendVote(p) ==
  /\ pstate[p].alive
  /\ ~ pstate[p].sent
  /\ coord.request \in {yes, no}
  /\ pstate' = [pstate EXCEPT ![p].vote = coord.request, ![p].sent = TRUE]
  /\ UNCHANGED << coord, fwd >>

AbortOnCoordinatorVote ==
  /\ coord.alive
  /\ coord.vote = no
  /\ \A p \in participants : pstate[p].alive => pstate[p].decision = undecided
  /\ pstate' = [p \in participants |->
                  [pstate[p] EXCEPT !.decision = abort]]
  /\ UNCHANGED << coord, fwd >>

\* A participant receives the coordinator's broadcast and stores it in its own
\* forwarding entry, which is the pre-decision it will later forward onward.
PredecideFromCoordinator(p) ==
  /\ pstate[p].alive
  /\ pstate[p].decision = undecided
  /\ coord.broadcast \in {yes, no}
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coord.broadcast]
  /\ UNCHANGED << pstate, coord >>

PredecideFromForwarding(p) ==
  /\ pstate[p].alive
  /\ pstate[p].decision = undecided
  /\ \E q \in participants :
        /\ q # p
        /\ fwd[q][p] \in {commit, abort}
        /\ fwd[p][p] = notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED << pstate, coord >>

\* Forward the pre-decision to another participant.
Forward(p, q) ==
  /\ q # p
  /\ pstate[p].alive
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED << pstate, coord >>

\* Local finalization is gated on forwarding to everyone else first.
Decide(p) ==
  /\ pstate[p].alive
  /\ pstate[p].decision = undecided
  /\ \A q \in participants : q # p => fwd[p][q] = fwd[p][p]
  /\ pstate' = [pstate EXCEPT ![p].decision = fwd[p][p]]
  /\ UNCHANGED << coord, fwd >>

\* Abort on timeout if the coordinator is dead and no fresh broadcast or forward
\* is available.
AbortOnTimeout(p) ==
  /\ pstate[p].alive
  /\ pstate[p].decision = undecided
  /\ ~ coord.alive
  /\ coord.broadcast = waiting
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ pstate' = [pstate EXCEPT ![p].decision = abort]
  /\ UNCHANGED << coord, fwd >>

Die(p) ==
  /\ pstate[p].alive
  /\ pstate[p].alive' = FALSE
  /\ pstate[p].faulty' = TRUE
  /\ UNCHANGED << coord, fwd >>

Progress ==
  \/ \E r \in participants : CoordinatorSendRequest(r)
  \/ CoordinatorCollectVote(yes)
  \/ CoordinatorCollectVote(no)
  \/ \E p \in participants : CoordinatorDetectFault(p)
  \/ CoordinatorMakeDecision
  \/ CoordinatorBroadcast
  \/ CoordinatorDie
  \/ \E p \in participants : SendVote(p)
  \/ AbortOnCoordinatorVote
  \/ \E p \in participants : PredecideFromCoordinator(p)
  \/ \E p \in participants : PredecideFromForwarding(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)

SpecNB ==
  /\ Init
  /\ [][Progress]_vars
  /\ WF_vars(\E r \in participants : CoordinatorSendRequest(r))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PredecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PredecideFromForwarding(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: no two participants reach different final decisions.
AC1 == \A p, q \in participants : (pstate[p].decision = commit) ~> (pstate[q].decision = abort)

\* Safety: committing means everybody voted yes.
AC2 == (\E p \in participants : pstate[p].decision = commit) ~>
        (\A q \in participants : pstate[q].vote = yes)

\* Safety: aborting means somebody voted no or crashed.
AC3 == (\E p \in participants : pstate[p].decision = abort) ~>
        (\E q \in participants : pstate[q].vote = no \/ pstate[q].faulty) \/ coord.faulty

\* Safety: decisions are final once made.
AC4 == \A p, q \in participants :
        (pstate[p].decision = undecided /\ pstate[q].decision # undecided) ~>
          (pstate[p].decision = undecided)

\* Liveness: either everyone decides, or someone crashes.
AC3Live == <>(\A p \in participants : pstate[p].decision # undecided \/ coord.faulty \/ \E q \in participants : pstate[q].faulty)

\* Liveness: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (~pstate[p].faulty) ~> (pstate[p].decision # undecided)

Properties == {AC3Live, AC5}

====