---- MODULE ACP_NB ------------------------------------------------------------
EXTENDS ACP_SB

\*=============================
\* Types
\*=============================
TypeInvParticipantNB ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN,
      forward   : [participants -> {notsent, commit, abort}]
    ]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\*=============================
\* Initial state
\*=============================
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : {TRUE},
      decision : {undecided},
      faulty   : {FALSE},
      voteSent : {FALSE},
      forward  : [participants -> {notsent}]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\*=============================
\* Actions
\*=============================
\* Forward a pre‑decision from i to j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' =
       [participant EXCEPT ![i] =
         [@ EXCEPT !.forward =
           [@ EXCEPT ![j] = participant[i].forward[i]]
         ]
       ]
  /\ UNCHANGED <<coordinator>>

\* Receive a forwarded decision from j (pre‑decision)
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' =
       [participant EXCEPT ![i] =
         [@ EXCEPT !.forward =
           [@ EXCEPT ![i] = participant[j].forward[i]]
         ]
       ]
  /\ UNCHANGED <<coordinator>>

\* Receive a decision directly from the coordinator (pre‑decision)
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' =
       [participant EXCEPT ![i] =
         [@ EXCEPT !.forward =
           [@ EXCEPT ![i] = coordinator.broadcast[i]]
         ]
       ]
  /\ UNCHANGED <<coordinator>>

\* Commit the pre‑decision after it has been forwarded to all others
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' =
       [participant EXCEPT ![i] =
         [@ EXCEPT !.decision = participant[i].forward[i]]
       ]
  /\ UNCHANGED <<coordinator>>

\* Abort because of a timeout (simulated condition)
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants :
        participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' =
       [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\*=============================
\* Combined participant program
\*=============================
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

\*=============================
\* Overall specification
\*=============================
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][parProgNNB \/ coordProgN]_<<coordinator, participant>> /\ fairnessNB

\*=============================
\* (Some) Intended properties
\*=============================
AllCommit == \A i \in participants :
               <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort == \A i \in participants :
              <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    (\A j \in participants : participant[j].vote = yes)
      ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

=============================================================================