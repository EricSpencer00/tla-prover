---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, that message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (becomes "decision")

EXTENDS ACP_SB

\* Participants are extended with a "forward" variable; the coordinator is
\* unchanged.

TypeInvParticipantNB == participant \in [
  participants -> [
    vote      : {yes, no}, alive     : BOOLEAN, decision  : {undecided, commit, abort},
    faulty    : BOOLEAN, voteSent  : BOOLEAN,
    forward   : [ participants -> {notsent, commit, abort} ]
  ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* Initially, participants have not forwarded anything yet.

InitParticipantNB == participant \in [
  participants -> [
    vote     : {yes, no}, alive : TRUE, decision : undecided,
    faulty   : FALSE, voteSent : FALSE,
    forward  : [ participants -> {notsent} ]
  ]
]

InitNB == InitParticipantNB /\ InitCoordinator

\* forward(i,j): participant i forwards its predecision to participant j.
\* i is alive, has a predecision, and has not yet forwarded it to j.
forward(i,j) == /\ i # j /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [ participant EXCEPT ![i] = 
                      [ @ EXCEPT !.forward = @ [j |-> participant[i].forward[i]] ] ]
                /\ UNCHANGED << coordinator >>

\* preDecideOnForward(i,j): participant i receives decision from participant j.
\* i is alive and undecided; participant j has forwarded its decision to i.
preDecideOnForward(i,j) == /\ i # j /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [ participant EXCEPT ![i] = 
                                [ @ EXCEPT !.forward = @ [i |-> participant[j].forward[i]] ] ]
                           /\ UNCHANGED << coordinator >>

\* preDecide(i): participant i receives decision from the coordinator.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [ participant EXCEPT ![i] = 
                     [ @ EXCEPT !.forward = @ [i |-> coordinator.broadcast[i]] ] ]
                /\ UNCHANGED << coordinator >>

\* decideNB(i): actual decision, after the predecision has been forwarded to 
\* all other participants.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [ participant EXCEPT ![i].decision = participant[i].forward[i] ]
               /\ UNCHANGED << coordinator >>

\* abortOnTimeout(i): simulated timeout. Coordinator died before sending and
\* live participants received no forward from a dead one.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [ participant EXCEPT ![i].decision = abort ]
                     /\ UNCHANGED << coordinator >>

\* For N participants
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* Invalid properties (intentionally retained as a demo of failure):
AllCommit          == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort           == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)
AllCommitYesVotes  == \A i \in participants : (\A j \in participants : participant[j].vote = yes)
                        ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

====