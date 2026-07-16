---- MODULE ACP_NB ---------------------------------------------------------
\* Non‑blocking Atomic Commitment Protocol (ACP‑NB)
\* Extends the basic protocol defined in ACP_SB.
\* The specification adds a “forward” map that stores a pre‑decision that a
\* participant has received (either from the coordinator or from another
\* participant) before it is finally committed to the local “decision” field.

EXTENDS ACP_SB

\*----------------------------------------------------------------------
\* Types
\*----------------------------------------------------------------------
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

\*----------------------------------------------------------------------
\* Initialization
\*----------------------------------------------------------------------
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : TRUE,
      decision : undecided,
      faulty   : FALSE,
      voteSent : FALSE,
      forward  : [ participants -> notsent ]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\*----------------------------------------------------------------------
\* Actions
\*----------------------------------------------------------------------
\* 1. Forward a pre‑decision from i to j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent           \* i already has a pre‑decision
  /\ participant[i].forward[j] = notsent
  /\ participant' = [ participant EXCEPT
        ![i] = [ @ EXCEPT
                !.forward = [ @ EXCEPT ![j] = participant[i].forward[i] ] ] ]
  /\ UNCHANGED << coordinator >>

\* 2. Receive a pre‑decision that j has forwarded to i
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [ participant EXCEPT
        ![i] = [ @ EXCEPT
                !.forward = [ @ EXCEPT ![i] = participant[j].forward[i] ] ] ]
  /\ UNCHANGED << coordinator >>

\* 3. Receive the coordinator’s broadcasted decision
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [ participant EXCEPT
        ![i] = [ @ EXCEPT
                !.forward = [ @ EXCEPT ![i] = coordinator.broadcast[i] ] ] ]
  /\ UNCHANGED << coordinator >>

\* 4. Commit the (pre‑)decision once it has been forwarded to everyone
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [ participant EXCEPT
        ![i] = [ @ EXCEPT !.decision = participant[i].forward[i] ] ]
  /\ UNCHANGED << coordinator >>

\* 5. Abort on a simulated timeout
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants :
        participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [ participant EXCEPT
        ![i] = [ @ EXCEPT !.decision = abort ] ]
  /\ UNCHANGED << coordinator >>

\*----------------------------------------------------------------------
\* The interleaving of all participant‑level actions (including those from ACP_SB)
\*----------------------------------------------------------------------
parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

\* At each step some participant may die (parDie) or execute one of the
\* actions above.  The existential quantifier models the nondeterministic choice
\* of which pair (i, j) participates.
parProgNNB ==
  \E i, j \in participants :
       parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

\*----------------------------------------------------------------------
\* Fairness
\*----------------------------------------------------------------------
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

\*----------------------------------------------------------------------
\* Full specification
\*----------------------------------------------------------------------
SpecNB ==
  InitNB /\
  [][progNNB]_<<coordinator, participant>> /\
  fairnessNB

\*----------------------------------------------------------------------
\* (Some) properties (kept unchanged – they are only illustrative)
\*----------------------------------------------------------------------
AllCommit ==
  \A i \in participants :
    <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort ==
  \A i \in participants :
    <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    ( \A j \in participants : participant[j].vote = yes )
    ~> ( participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty )

================================================================================