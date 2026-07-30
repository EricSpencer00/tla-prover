---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB) by Babaoglu & Toueg.
\* The spec models a coordinator collecting participant votes and broadcasting
\* a commit/abort decision. Simple broadcast means the coordinator can crash
\* mid-broadcast and leave participants undecided -- the non-blocking liveness
\* property AC5 is therefore not guaranteed here.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decided, faulty, sentVote, coordRequested,
         coordReceived, coordSentDecision, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decided, faulty, sentVote, coordRequested,
          coordReceived, coordSentDecision, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordReceived \in [participants -> {yes, no, waiting}]
  /\ coordSentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordReceived = [p \in participants |-> waiting]
  /\ coordSentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

ReqVote(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordReceived, coordSentDecision,
                 coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordReceived[p] = waiting
  /\ sentVote[p]
  /\ coordReceived' = [coordReceived EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordRequested, coordSentDecision,
                 coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordReceived[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordRequested, coordReceived,
                 coordSentDecision, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordReceived[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordReceived[p] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordRequested, coordReceived, coordSentDecision,
                 coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSentDecision[p] = notsent
  /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordRequested, coordReceived,
                 coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                 coordRequested, coordReceived, coordSentDecision,
                 coordDecision>>

\* A participant can be slow to send its vote, but the fairness assumption
\* below forces it to send eventually -- a coordinator that has already
\* decided does not wait on a slow participant.
SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, coordRequested,
                 coordReceived, coordSentDecision,
                 coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordReceived,
                 coordSentDecision, coordDecision,
                 coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordReceived,
                 coordSentDecision, coordDecision,
                 coordAlive, coordFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ coordSentDecision[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = coordSentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordReceived,
                 coordSentDecision, coordDecision,
                 coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sentVote,
                 coordRequested, coordReceived,
                 coordSentDecision, coordDecision,
                 coordAlive, coordFaulty>>

\* Progress actions: sending votes, making decisions, broadcasting decisions.
\* Death actions are deliberately excluded from fairness so a crash can
\* happen silently at any moment (it is not a livelock).
Next ==
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p)
                                  \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p)
                                  \/ Die(p) \/ ReqVote(p) \/ RecvVote(p) \/ DetectFault(p)
  \/ MakeDecision \/ CoordDie
  \/ \E p \in participants : Broadcast(p)

Spec == Init /\ [][Next]_vars
             /\ WF_vars(\E p \in participants : SendVote(p))
             /\ WF_vars(\E p \in participants : AbortOnVote(p))
             /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))
             /\ WF_vars(MakeDecision)

AC1 == \A p, q \in participants : (decided[p] = commit) => (decided[q] # abort)

AC2 == (\E p \in participants : decided[p] = commit) => (\A p \in participants : vote[p] = yes)

AC3 == (\E p \in participants : decided[p] = abort) =>
        (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

AC4 == \A p \in participants : (decided[p] = commit) ~> (decided[p] = commit)
                                  /\ (decided[p] = abort) ~> (decided[p] = abort)

\* Simple broadcast does NOT guarantee the non-blocking property AC5, so it is
\* omitted here; instead we check a weaker eventual decision property.
AC5 == <>(\A p \in participants : decided[p] # undecided \/ \E p \in participants : faulty[p] \/ coordFaulty)

====