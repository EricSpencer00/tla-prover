---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote
VARIABLES reqsent, coordVote, coordDecision, coordAlive, coordFaulty
VARIABLES coordSend

vars == <<vote, alive, decision, faulty, sentVote,
          reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqsent \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordSend \in [participants -> {notsent, commit, abort}]

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqsent = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordSend = [p \in participants |-> notsent]

ReqVote(p) ==
  /\ coordAlive
  /\ ~reqsent[p]
  /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqsent[p]
  /\ coordVote[p] = waiting
  /\ sentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                reqsent, coordDecision, coordAlive, coordFaulty, coordSend>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqsent[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                reqsent, coordVote, coordAlive, coordFaulty, coordSend>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                       THEN commit
                       ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                reqsent, coordVote, coordAlive, coordFaulty, coordSend>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSend[p] = notsent
  /\ coordSend' = [coordSend EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                reqsent, coordVote, coordDecision, coordSend>>

SendVote(p) ==
  /\ alive[p]
  /\ reqsent[p]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ sentVote[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~reqsent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

DecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSend[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSend[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote,
                reqsent, coordVote, coordDecision, coordAlive, coordFaulty, coordSend>>

Next ==
  \/ \E p \in participants : ReqVote(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnNo(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoord(p)
  \/ \E p \in participants : Die(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordDie)
  /\ \A p \in participants :
       WF_vars(CoordBroadcast(p))
       /\ WF_vars(SendVote(p))
       /\ WF_vars(DecideFromCoord(p))
       /\ WF_vars(AbortOnNo(p))
       /\ WF_vars(AbortOnTimeout(p))
  /\ \A p \in participants : (Die(p) WF_vars(SendVote(p)))

Agreement ==
  ~(\E p1 \in participants : \E p2 \in participants :
       (decision[p1] = commit) /\ (decision[p2] = abort))

CommitValidity ==
  \A p \in participants : decision[p] = commit => (vote[p] = yes)

AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit) ~> (decision[p] = commit)
    /\ (decision[p] = abort) ~> (decision[p] = abort)

EventualDecision ==
  (\A p \in participants : decision[p] # undecided)
    \/ (\E p \in participants : faulty[p])
    \/ coordFaulty

====