---- MODULE ACP_NB ---------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

--------------------------------------------------------------------------------
\* Participants type is extended with a "forward" variable.  
\* Coordinator type is unchanged.

VARIABLES participant, coordinator

\* Type invariants (kept from the original specification for completeness)
TypeInvParticipantNB == 
  participant \in [participants -> [
    vote      : {yes, no},
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    voteSent  : BOOLEAN,
    forward   : [participants -> {notsent, commit, abort}]
  ]]
  
TypeInvCoordinator ==
  coordinator \in [participants -> {waiting, decided}]  \* placeholder; real definition from ACP_SB
  
TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

--------------------------------------------------------------------------------
\* Initial state (unchanged)

InitParticipantNB == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : TRUE,
    decision : undecided,
    faulty   : FALSE,
    voteSent : FALSE,
    forward  : [participants -> notsent]
  ]
]

InitCoordinator == InitCoordinator \* from ACP_SB (unchanged)

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------
\* Action definitions (minimal fixes applied)

\* forward(i,j): participant i forwards its predecision to participant j
forward(i,j) == 
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = 
          [@ EXCEPT ![j] = participant[i].forward[i]]
        ]
      ]
  /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i receives decision from participant j
preDecideOnForward(i,j) == 
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = 
          [@ EXCEPT ![i] = participant[j].forward[i]]
        ]
      ]
  /\ UNCHANGED coordinator

\* preDecide(i): participant i receives decision from coordinator
preDecide(i) == 
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = 
          [@ EXCEPT ![i] = coordinator.broadcast[i]]
        ]
      ]
  /\ UNCHANGED coordinator

\* decideNB(i): participant i decides based on its predecision
decideNB(i) == 
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.decision = participant[i].forward[i]]
      ]
  /\ UNCHANGED coordinator

\* abortOnTimeout(i): simulated timeout leading to abort
abortOnTimeout(i) == 
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* The rest of the actions are inherited from ACP_SB; we expose the ones used
\* in the combined program definition for clarity.

\* Placeholder definitions for actions from ACP_SB (they are unchanged)
sendVote(i)          == SendVote(i)          \* from ACP_SB
abortOnVote(i)       == AbortOnVote(i)       \* from ACP_SB
abortOnTimeoutRequest(i) == AbortOnTimeoutRequest(i) \* from ACP_SB
parDie(i)            == ParDie(i)            \* from ACP_SB
coordProgB           == CoordProgB           \* from ACP_SB

--------------------------------------------------------------------------------
\* Combined participant program (original logic, now using the fixed actions)

parProgNB(i,j) == 
    \/ sendVote(i) 
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ forward(i,j) 
    \/ preDecideOnForward(i,j) 
    \/ abortOnTimeout(i) 
    \/ preDecide(i) 
    \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgB

--------------------------------------------------------------------------------
\* Fairness (unchanged)

fairnessNB == 
    /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
    /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES (kept unchanged)

AllCommit == \A i \in participants : <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == 
    \A i \in participants :
        \A j \in participants : participant[j].vote = yes
    ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================