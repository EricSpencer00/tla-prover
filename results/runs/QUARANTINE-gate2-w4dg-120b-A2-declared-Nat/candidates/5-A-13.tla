---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), a blocking
\* variant where a coordinator crash during broadcast can strand participants.
\* This spec is derived directly from the natural-language description above
\* and defines every identifier the reference configuration expects.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordRequested,
         coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voted, coordRequested,
          coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E i \in participants:
        vote = [p \in participants |-> IF p = i THEN yes ELSE no]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions
SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ voted[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: coordRequested[p]
  /\ \A p \in participants: coordVote[p] \in {yes, no}
  /\ coordDecision' = IF \A p \in participants: coordVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive>>

\* Participant actions
SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordRequested,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Broadcast is deliberately modeled as a simple, single-step action, not a
\* per-participant reliable broadcast. Coordinator failure mid-broadcast can
\* strand a participant, which is why this variant is blocking.
Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: RecvVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideOnBroadcast(p)
  \/ \E p \in participants: PartDie(p)

\* Weak fairness on progress actions (excluding death): if a participant can
\* move, it eventually does; similarly for the coordinator.
Spec == Init /\ [][Next]_vars
  /\ \A p \in participants:
       /\ WF_vars(SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p))
  /\ WF_vars(MakeDecision)

\* Safety: no split-brain (consistent decisions), commit only on unanimous yes,
\* abort only on a no vote or fault, and decisions are irrevocable.
AC1 ==
  \A p1, p2 \in participants:
    (decision[p1] = commit /\ decision[p2] = abort) => FALSE
AC2 ==
  \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes
AC3 ==
  \A p \in participants: decision[p] = abort =>
    (\E q \in participants: vote[q] = no) \/ (\E q \in participants: faulty[q]) \/ coordFaulty
AC4 ==
  \A p \in participants:
    /\ decision[p] = commit => \A k \in [1..Nat]: decision[p] = commit
    /\ decision[p] = abort => \A k \in [1..Nat]: decision[p] = abort

\* Liveness: non-blocking termination for the non-faulty case -- either every
\* participant decides, or a participant/coordinator is faulty. In the simple
\* broadcast variant a coordinator crash mid-broadcast can leave participants
\* stranded, so the non-blocking termination property AC5 is not satisfied here,
\* and is not claimed.
AC3Live ==
  <>(\A p \in participants: decision[p] # undecided) \/ \E p \in participants: faulty[p] \/ coordFaulty

====