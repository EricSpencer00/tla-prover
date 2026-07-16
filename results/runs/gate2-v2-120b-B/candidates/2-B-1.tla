---- MODULE ACP_NB ----
\* Non blocking Atomic Commitment Protocol (ACP-NB) extension of ACP_SB
\* This module adds a "forward" map to each participant to support reliable
\* broadcast of pre‑decisions.  The only change required for TLC is to make the
\* action preDecideOnForward assign the whole participant variable (as required
\* by the state‑transition relation) while preserving its original semantics.

EXTENDS ACP_SB

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeInvParticipantNB ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN,
      forward   : [ participants -> {notsent, commit, abort} ]
    ]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : {TRUE},
      decision : {undecided},
      faulty   : {FALSE},
      voteSent : {FALSE},
      forward  : [ participants -> {notsent} ]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* forward(i,j): participant i forwards its pre‑decision to participant j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
              ]
      ]
  /\ UNCHANGED << coordinator >>

\* preDecideOnForward(i,j): participant i adopts the decision that participant j
\* has already forwarded to i
\* The original specification only updated participant[i].forward[i]; TLC
\* requires the whole participant variable to be assigned.  We therefore assign
\* participant' to the same value as before, differing only in the entry for i.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
              ]
      ]
  /\ UNCHANGED << coordinator >>

\* preDecide(i): participant i receives the coordinator's broadcast
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
              ]
      ]
  /\ UNCHANGED << coordinator >>

\* decideNB(i): participant i makes its final decision after having forwarded
\* its pre‑decision to every other participant
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]
      ]
  /\ UNCHANGED << coordinator >>

\* abortOnTimeout(i): timeout handling when the coordinator is dead
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED << coordinator >>

\* ----------------------------------------------------------------------
\* Combined participant program (as in the original spec)
\* ----------------------------------------------------------------------
parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB ==
  InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* ----------------------------------------------------------------------
\* (Possibly invalid) safety properties (unchanged)
\* ----------------------------------------------------------------------
AllCommit ==
  \A i \in participants :
      <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort ==
  \A i \in participants :
      <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes
      ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====