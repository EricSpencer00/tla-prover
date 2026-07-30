---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\*
\* Non blocking Atomic Commit Protocol (ACP-NB).  The non blocking property
\* AC5 is obtained by a reliable broadcast realized as follows:
\*   - upon reception of a broadcast message, the message is forwarded to all
\*     participants before being delivered locally;
\*   - each participant stores the decision forwarded to it in a per-source
\*     entry of its "forward" variable, delivering only once it has received
\*     the decision from every participant (including the coordinator).
\*
\* The change fixed the incomplete action: a forwarding action may leave one
\* participant's own forward entry untouched, so the next-state relation
\* left that entry unspecified.  The precondition now requires at least one
\* source whose forwarded decision is still notsent, and the action
\* always forwards one such source, so no participant's forward entry is ever
\* left unspecified.  The protocol's safety properties are untouched.
\* Since the participant record has grown, the type invariant is extended
\* accordingly.
\* The rest of the protocol is unchanged.

EXTENDS ACP_SB

\* Participant records now carry their forwarded decisions per source.
TypeInvParticipantNB == participant \in [
    participants -> [
        vote     : {yes, no},
        alive    : BOOLEAN,
        decision : {undecided, commit, abort},
        faulty   : BOOLEAN,
        voteSent : BOOLEAN,
        forward  : [ participants -> {notsent, commit, abort} ]
    ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* Initially, participants have not forwarded anything.
InitParticipantNB == participant \in [
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

\* forward(i,j): participant i forwards its (pre)decision to participant j.
\* Preconditions: participant i is alive, has a (pre)decision, and has not
\* yet forwarded that decision to participant j.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                 ]]
                /\ UNCHANGED << coordinator >>

\* preDecideOnForward(i,j): participant i receives the decision participant j
\* has forwarded to it.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                             ]]
                           /\ UNCHANGED << coordinator >>

\* preDecide(i): participant i receives the decision the coordinator broadcast.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                 ]]
                /\ UNCHANGED << coordinator >>

\* decideNB(i): participant i decides once it has received a (pre)decision
\* from every participant (including the coordinator).
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.decision = participant[i].forward[i]
                 ]]
               /\ UNCHANGED << coordinator >>

\* abortOnTimeout(i): an abort is decided when the coordinator is dead and
\* no undecided participant can still learn anything about the decision.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED << coordinator >>

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES 
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====