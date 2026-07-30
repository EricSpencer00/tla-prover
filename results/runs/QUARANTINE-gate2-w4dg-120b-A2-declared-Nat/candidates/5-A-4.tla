---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordinatorSent, recvd,
          broadcasted, coordinatorDecision, coordinatorAlive, coordinatorFaulty

vars == <<vote, alive, decision, faulty, sentVote, coordinatorSent, recvd,
           broadcasted, coordinatorDecision, coordinatorAlive,
           coordinatorFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordinatorSent \in [participants -> BOOLEAN]
  /\ recvd \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {notSent, commit, abort}]
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordinatorSent = [p \in participants |-> FALSE]
  /\ recvd = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notSent]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE

SendRequest(p) ==
  /\ coordinatorAlive
  /\ ~coordinatorSent[p]
  /\ coordinatorSent' = [coordinatorSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

ReceiveVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ coordinatorSent[p]
  /\ recvd[p] = waiting
  /\ sentVote[p]
  /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinatorSent,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

DetectFault(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ coordinatorSent[p]
  /\ recvd[p] = waiting
  /\ ~alive[p]
  /\ coordinatorDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinatorSent,
                recvd, broadcasted, coordinatorAlive, coordinatorFaulty>>

Decide ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants: recvd[p] # waiting
  /\ coordinatorDecision' = IF \A p \in participants: recvd[p] = yes
                             THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinatorSent,
                recvd, broadcasted, coordinatorAlive, coordinatorFaulty>>

Broadcast(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision # undecided
  /\ broadcasted[p] = notSent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinatorSent,
                recvd, coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

CoordinatorDie ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordinatorSent,
                recvd, broadcasted, coordinatorDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ coordinatorSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordinatorSent, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordinatorSent, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordinatorAlive
  /\ ~coordinatorSent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordinatorSent, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notSent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordinatorSent, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordinatorSent, recvd,
                broadcasted, coordinatorDecision, coordinatorAlive,
                coordinatorFaulty>>

Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ Decide
  \/ \E p \in participants: Broadcast(p)
  \/ CoordinatorDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideFromBroadcast(p)
  \/ \E p \in participants: ParticipantDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: SendVote(p))
  /\ WF_vars(\E p \in participants: AbortOnVote(p))
  /\ WF_vars(\E p \in participants: DecideFromBroadcast(p))
  /\ WF_vars(\E p \in participants: Broadcast(p))
  /\ SF_vars(Decide)

Decided == \A p \in participants: decision[p] # undecided

AC1 == \A p, q \in participants:
  ~(decision[p] = commit /\ decision[q] = abort)

AC2 == \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

AC3 == \A p \in participants: decision[p] = abort => (\E q \in participants: vote[q] = no)
        \/ (\E q \in participants: faulty[q])
        \/ coordinatorFaulty

AC4 == \A p \in participants: decision[p] = commit => decision' [p] = commit
        /\ (decision[p] = abort => decision' [p] = abort)

AC3liveness == <>Decided \/ <>(\E q \in participants: faulty[q]) \/ coordinatorFaulty

====