---- MODULE ACP_NB -------------------------------------------------------------
\* Non blocking Atomic Committment Protocol (ACP-NB).  Every participant first
\* predecides (commits or aborts), then forwards that predecision to all other
\* participants before actually deciding.  A participant only decides once it
\* has received its own predecision from every participant -- its own broadcast
\* and the broadcasts of all others -- which is the backpressure that enforces
\* the non blocking property: a slow participant is not the one that blocks the
\* others.
\* Author: Charlie Pearson, 2002; edited for the TLA+2020 syntax by OpenAI

EXTENDS ACP_SB

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

\* forward(i,j): participant i forwards the predecision it has put in forward[i]
\* to participant j, provided i is alive and hasn't already forwarded it to j.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
                /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i receives (and stores) the predecision
\* already forwarded to it by participant j.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
                           /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i receives (and stores) the coordinator's decision.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
                /\ UNCHANGED <<coordinator>>

\* decideNB(i): participant i actually decides, once every participant (including
\* itself) has put the *same* predecision into i's forward field.
decideNB(i) == /\ participant[i].alive
               /\ participant[i].decision = undecided
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): simulated timeout.  Coordinator is down, and nobody 
\* (neither coordinator nor a dead participant) has forwarded a predecision to i.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

\* Participant actions are indexed by i (the acting participant) and by j (the
\* other participant that is either the source of a forwarded predecision, or
\* the destination of a forwarded predecision).  For a given i, the j values
\* are taken from a disjunction, which is exactly what prevents an action on a
\* frozen (dead) participant from being indistinguishable from no action at all.
parProgNB(i,j) == \/ sendVote(i)
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j)
                  \/ preDecideOnForward(i,j)
                  \/ preDecide(i)
                  \/ decideNB(i)
                  \/ abortOnTimeout(i)

parProgNNB == \E i,j \in participants : parProgNB(i,j) \/ parDie(i)

progNNB == parProgNNB \/ coordProgN

\* Each participant's predecision-and-forward step is strongly fair, which
\* means a slow participant must eventually forward and decide -- this is what
\* rules out a plain deadlock (versus a genuine livelock where everyone keeps
\* trying but nobody ever gets ahead of the backpressure condition).
fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : preDecideOnForward(i,j))
              /\ \A i \in participants : WF_<<coordinator, participant>>(decideNB(i))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* The protocol makes progress: each alive participant eventually decides, and
\* a participant that has already died stays dead.
EventuallyDecided == \A i \in participants : <>(participant[i].decision # undecided \/ ~participant[i].alive)

=====================================================================