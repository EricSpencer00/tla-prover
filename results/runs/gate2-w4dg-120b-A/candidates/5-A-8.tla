---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants,
  yes,
  no,
  undecided,
  commit,
  abort,
  waiting,
  notsent

VARIABLES
  vote,
  alive,
  decision,
  faulty,
  sentVote,
  reqSent,
  recVote,
  bSent,
  coordDecision,
  coordAlive,
  coordFaulty

vars == << vote, alive, decision, faulty, sentVote,
           reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recVote \in [participants -> {yes, no, waiting}]
  /\ bSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqSent = [p \in participants |-> FALSE]
  /\ recVote = [p \in participants |-> waiting]
  /\ bSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest ==
  /\ coordAlive
  /\ \E p \in participants :
       /\ ~reqSent[p]
       /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 recVote, bSent, coordDecision, coordAlive, coordFaulty >>

RecvVote ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \E p \in participants :
       /\ reqSent[p]
       /\ recVote[p] = waiting
       /\ sentVote[p]
       /\ recVote' = [recVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, bSent, coordDecision, coordAlive, coordFaulty >>

DetectFault ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \E p \in participants :
       /\ reqSent[p]
       /\ recVote[p] = waiting
       /\ ~alive[p]
       /\ coordDecision' = abort
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recVote, bSent, coordAlive, coordFaulty >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recVote, bSent, coordAlive, coordFaulty >>

BroadcastDecision ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ \E p \in participants :
       /\ bSent[p] = notsent
       /\ bSent' = [bSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recVote, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recVote, bSent, coordDecision, coordFaulty >>

SendVote ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ reqSent[p]
       /\ sentVote[p] = FALSE
       /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty,
                 reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

AbortOnVote ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = undecided
       /\ sentVote[p]
       /\ vote[p] = no
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sentVote,
                 reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = undecided
       /\ coordAlive = FALSE
       /\ reqSent[p] = FALSE
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sentVote,
                 reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

DecideOnBroadcast ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ decision[p] = undecided
       /\ bSent[p] # notsent
       /\ decision' = [decision EXCEPT ![p] = bSent[p]]
  /\ UNCHANGED << vote, alive, faulty, sentVote,
                 reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

PartDie ==
  /\ \E p \in participants :
       /\ alive[p]
       /\ alive' = [alive EXCEPT ![p] = FALSE]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, decision, sentVote,
                 reqSent, recVote, bSent, coordDecision, coordAlive, coordFaulty >>

Next ==
  \/ SendRequest
  \/ RecvVote
  \/ DetectFault
  \/ MakeDecision
  \/ BroadcastDecision
  \/ CoordDie
  \/ SendVote
  \/ AbortOnVote
  \/ AbortOnTimeout
  \/ DecideOnBroadcast
  \/ PartDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendRequest)
  /\ WF_vars(SendVote)
  /\ WF_vars(DecideOnBroadcast)
  /\ WF_vars(AbortOnVote)
  /\ WF_vars(BroadcastDecision)
  /\ WF_vars(MakeDecision)

Agree == \A p1, p2 \in participants : ~(decision[p1] = commit /\ decision[p2] = abort)

CommitValid == \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
  \E p \in participants :
    decision[p] = abort =>
      \/ (\E q \in participants : vote[q] = no)
      \/ (\E q \in participants : faulty[q])
      \/ coordFaulty

IrreversibleDecide ==
  /\ \A p \in participants : decision[p] = commit => decision[p] = commit
  /\ \A p \in participants : decision[p] = abort => decision[p] = abort

EventuallyDecideOrFault ==
  <>(\E p \in participants : decision[p] # undecided) \/ coordFaulty

====