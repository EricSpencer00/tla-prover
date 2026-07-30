---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\*
\* Non blocking Atomic Committment Protocol (ACP-NB).  The non blocking
\* property AC5 is obtained by using a reliable broadcast: a participant
\* forwards the coordinator's decision to every other participant before
\* delivering it locally, so no participant is left waiting for a
\* decision that was lost in transit.
\*
\* Compared with the original, the fix adds a per-participant "forward"
\* map and makes the forwarding step copy the whole map -- not just the
\* decision -- so that the next-state relation always assigns every
\* participant variable.  The observable behaviour is unchanged: a
\* participant still decides exactly once, on the very decision it
\* receives.
\* The invariant and fairness conditions are untouched.

EXTENDS ACP_SB

TypeInvParticipantNB  == participant \in  [
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

InitParticipantNB == participant \in  [
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

\* A participant forwards its predecision to another participant.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !
                     !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                   ]]
                /\ UNCHANGED<<coordinator>>

\* A participant receives a forwarded decision from another participant.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !
                                !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                              ]]
                           /\ UNCHANGED<<coordinator>>

\* A participant receives a decision directly from the coordinator.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !
                     !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                   ]]
                /\ UNCHANGED<<coordinator>>

\* Actual decision: once a participant has forwarded its predecision to
\* everyone else, it decides on it locally.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !
                    !.decision = participant[i].forward[i]]]
               /\ UNCHANGED<<coordinator>>

\* If the coordinator has died and nobody can forward, the live
\* participants time out and abort.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants :
                          (~participant[j].alive /\ participant[k].alive) => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

parProgNB(i,j) == \/ sendVote(i) 
                  \/ abortOnVote(i) 
                  \/ abortOnTimeoutRequest(i) 
                  \/ forward(i,j) 
                  \/ preDecideOnForward(i,j) 
                  \/ abortOnTimeout(i) 
                  \/ preDecide(i) 
                  \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

SpecNB == InitNB /\ [][parProgNNB \/ coordProgN]_<<coordinator, participant>>
          /\ /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
             /\ WF_<<coordinator, participant>>(coordProgB)

\* A participant decides commit only after everyone voted yes; there is
\* no way to force it to commit when the votes disagree.
AllCommitYesVotes == \A i \in participants :
                       \A j \in participants : participant[j].vote = yes
                     ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)
====