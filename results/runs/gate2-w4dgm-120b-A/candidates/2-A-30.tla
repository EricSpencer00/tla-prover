---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSentVote, coordinatorRequest, coordinatorVote,
          coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty,
          forwarded

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
          participantSentVote, coordinatorRequest, coordinatorVote,
          coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty,
          forwarded>>

\* forwarded[i][j] is participant i's record of the decision it has sent to j.
\* It holds the pre-decision a participant received (at its own index) and the
\* forward it made to each other participant (the reliability mechanism).
Forwarding == {notsent, commit, abort}

TypeOK ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSentVote \in [participants -> BOOLEAN]
  /\ coordinatorRequest \in {waiting, yes, no}
  /\ coordinatorVote \in {yes, no}
  /\ coordinatorBroadcast \in [participants -> BOOLEAN]
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> Forwarding]]

Init ==
  /\ participantVote = [p \in participants |-> yes]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSentVote = [p \in participants |-> FALSE]
  /\ coordinatorRequest = waiting
  /\ coordinatorVote = yes
  /\ coordinatorBroadcast = [p \in participants |-> FALSE]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE
  /\ forwarded = [i \in participants |-> [j \in participants |-> notsent]]

SendRequest ==
  /\ coordinatorAlive = TRUE
  /\ coordinatorRequest = waiting
  /\ coordinatorRequest' = yes
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorVote, coordinatorBroadcast,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty, forwarded>>

GetVote(p) ==
  /\ coordinatorAlive = TRUE
  /\ participantAlive[p] = TRUE
  /\ participantSentVote[p] = FALSE
  /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
  /\ coordinatorVote' = participantVote[p]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 coordinatorRequest, coordinatorBroadcast,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty, forwarded>>

\* Coordinator declares the decision and starts the broadcast.
Decide(c) ==
  /\ coordinatorAlive = TRUE
  /\ coordinatorRequest # waiting
  /\ coordinatorDecision = undecided
  /\ coordinatorDecision' = c
  /\ coordinatorBroadcast' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorAlive, coordinatorFaulty, forwarded>>

Broadcast ==
  /\ coordinatorAlive = TRUE
  /\ coordinatorDecision # undecided
  /\ coordinatorBroadcast # [p \in participants |-> FALSE]
  /\ coordinatorBroadcast' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty, forwarded>>

Die ==
  /\ coordinatorAlive = TRUE
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, forwarded>>

\* A participant records the pre-decision it receives from the coordinator.
PreDecideFromCoordinator(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = undecided
  /\ coordinatorAlive = TRUE
  /\ coordinatorDecision # undecided
  /\ coordinatorBroadcast[p] = TRUE
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordinatorDecision]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

\* A participant records the pre-decision it receives from another participant.
PreDecideFromPeer(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = undecided
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants:
       /\ q # p
       /\ forwarded[q][p] # notsent
       /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

Forward(p, q) ==
  /\ participantAlive[p] = TRUE
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

\* A participant finalizes only after its pre-decision has reached everyone.
Decide(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = undecided
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants: forwarded[p][q] = forwarded[p][p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 forwarded>>

AbortOnTimeout(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = undecided
  /\ coordinatorAlive = FALSE
  /\ \A q \in participants: ~coordinatorBroadcast[q]
  /\ \A q \in participants: participantAlive[q] => forwarded[q][p] = notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                 participantSentVote, coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 forwarded>>

DieP(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantDecision, participantSentVote,
                 coordinatorRequest, coordinatorVote,
                 coordinatorBroadcast, coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 forwarded>>

Next ==
  \/ SendRequest
  \/ Broadcast
  \/ Die
  \/ \E p \in participants:
       \/ GetVote(p)
       \/ Decide(p)
       \/ PreDecideFromCoordinator(p)
       \/ PreDecideFromPeer(p)
       \/ AbortOnTimeout(p)
       \/ DieP(p)
       \/ \E q \in participants: Forward(p, q)
  \/ \E c \in {commit, abort}: Decide(c)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: GetVote(p))
  /\ WF_vars(\E p \in participants: PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants: PreDecideFromPeer(p))
  /\ WF_vars(\E p \in participants: \E q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: Decide(p))

\* Safety: no two participants reach different decisions.
AgreementNB ==
  \A p, q \in participants:
     (participantDecision[p] # undecided /\ participantDecision[q] # undecided)
       => participantDecision[p] = participantDecision[q]

TypeInvNB == TypeOK

\* Progress guaranteed by the reliable broadcast: all live participants decide.
CoordinatorTerminating == \A p \in participants: participantAlive[p] ~> (participantDecision[p] # undecided)

====