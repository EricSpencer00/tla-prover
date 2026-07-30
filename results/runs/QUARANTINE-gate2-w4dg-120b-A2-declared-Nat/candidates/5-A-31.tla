---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordDecision, coordFaulty, coordRequested, coordRecv, coordSent
VARIABLES vote, alive, decision, faulty, sent
vars == <<coordAlive, coordDecision, coordFaulty, coordRequested,
          coordRecv, coordSent, vote, alive, decision, faulty, sent>>

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordFaulty \in BOOLEAN
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {waiting, yes, no}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ coordFaulty = FALSE
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ vote = [p \in participants |-> IF (p \in participants) THEN yes ELSE no]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]

SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRecv, coordSent,
                 vote, alive, decision, faulty, sent>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ sent[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordSent, vote, alive, decision, faulty, sent>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordAlive, coordRequested, coordRecv, coordSent, vote,
                 alive, decision, faulty, sent>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordRecv,
                 coordSent, vote, alive, decision, faulty, sent>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, vote, alive, decision, faulty, sent>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordRequested, coordRecv, coordSent,
                 vote, alive, decision, faulty, sent>>

SendMyVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, coordSent, vote, alive, decision, faulty>>

AbortOnMyVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, coordSent, vote, alive, faulty, sent>>

AbortOnLostRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, coordSent, vote, alive, faulty, sent>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, coordSent, vote, alive, faulty, sent>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordRequested,
                 coordRecv, coordSent, vote, decision, sent>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
                              \/ BroadcastDecision(p) \/ SendMyVote(p) \/ AbortOnMyVote(p)
                              \/ AbortOnLostRequest(p) \/ DecideOnBroadcast(p) \/ PartDie(p)
  \/ MakeDecision \/ CoordDie

Spec == Init /\ [][Next]_vars
            /\ WF_vars(\E p \in participants : SendMyVote(p))
            /\ WF_vars(\E p \in participants : AbortOnMyVote(p))
            /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
            /\ WF_vars(MakeDecision)

Agree ==
  \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValid ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValid ==
  \A p \in participants : decision[p] = abort =>
     (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)

Irreversible ==
  \A p \in participants : (decision[p] = commit => decision[p] = commit) /\ (decision[p] = abort => decision[p] = abort)

EventualDecision ==
  <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

====