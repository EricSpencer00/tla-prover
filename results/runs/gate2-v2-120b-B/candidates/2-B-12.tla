---- MODULE ACP_NB --------------------------------------------------------------
\* Non Blocking Atomic Commitment Protocol (ACP-NB)
\* Extended from ACP_SB with a reliable broadcast mechanism.
\* The specification has been minimally corrected to ensure that all actions
\* fully specify the next-state relation.

EXTENDS ACP_SB

\* -------------------------------------------------------------------------
\* Type invariants
\* -------------------------------------------------------------------------

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

\* -------------------------------------------------------------------------
\* Initial predicate
\* -------------------------------------------------------------------------

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

\* -------------------------------------------------------------------------
\* Actions
\* -------------------------------------------------------------------------

\* Forward a pre‑decision from i to j
forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] # notsent
    /\ participant[i].forward[j] = notsent
    /\ participant' = [
        participant EXCEPT ![i] = [
            @ EXCEPT !.forward = [
                @ EXCEPT ![j] = participant[i].forward[i]
            ]
        ]
    ]
    /\ UNCHANGED << coordinator >>

\* Receive a forwarded decision from j
preDecideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ participant[j].forward[i] # notsent
    /\ participant' = [
        participant EXCEPT ![i] = [
            @ EXCEPT !.forward = [
                @ EXCEPT ![i] = participant[j].forward[i]
            ]
        ]
    ]
    /\ UNCHANGED << coordinator >>

\* Receive a decision directly from the coordinator
preDecide(i) ==
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [
        participant EXCEPT ![i] = [
            @ EXCEPT !.forward = [
                @ EXCEPT ![i] = coordinator.broadcast[i]
            ]
        ]
    ]
    /\ UNCHANGED << coordinator >>

\* Commit after having forwarded the (pre)decision to everyone
decideNB(i) ==
    /\ participant[i].alive
    /\ \A j \in participants : participant[i].forward[j] # notsent
    /\ participant' = [
        participant EXCEPT ![i] = [
            @ EXCEPT !.decision = participant[i].forward[i]
        ]
    ]
    /\ UNCHANGED << coordinator >>

\* Abort due to timeout conditions
abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ \A j \in participants :
          participant[j].alive => coordinator.broadcast[j] = notsent
    /\ \A j, k \in participants :
          ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
    /\ participant' = [
        participant EXCEPT ![i] = [ @ EXCEPT !.decision = abort ]
    ]
    /\ UNCHANGED << coordinator >>

\* -------------------------------------------------------------------------
\* Composite participant program (for any pair i, j)
\* -------------------------------------------------------------------------

parProgNB(i, j) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ forward(i, j)
    \/ preDecideOnForward(i, j)
    \/ abortOnTimeout(i)
    \/ preDecide(i)
    \/ decideNB(i)

\* Some participant may die, or the above program may be executed
parProgNNB == 
    \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

\* -------------------------------------------------------------------------
\* Fairness conditions
\* -------------------------------------------------------------------------

fairnessNB ==
    /\ \A i \in participants :
          WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
    /\ WF_<<coordinator, participant>>(coordProgB)

\* -------------------------------------------------------------------------
\* Full specification
\* -------------------------------------------------------------------------

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* -------------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES (kept from original spec)
\* -------------------------------------------------------------------------

AllCommit == \A i \in participants :
                <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort == \A i \in participants :
               <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
    \A i \in participants :
        \A j \in participants : participant[j].vote = yes
        ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

=============================================================================