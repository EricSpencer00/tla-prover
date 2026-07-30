---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME no == ~yes

VARIABLES vote, alive, decision, faulty, voteSent,
         coordRequested, coordVote, coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, voteSent,
          coordRequested, coordVote, coordSent, coordDecision, coordAlive>>

\* A participant is undecided but has already made a unilateral abort decision.
Aborted == [decision |-> abort]

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE

\* The coordinator requests a participant's vote (only once per participant).
ReqVote(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                coordVote, coordSent, coordDecision>>

\* The coordinator receives a participant's vote.
RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : coordRequested[q]
  /\ coordVote[p] = waiting
  /\ voteSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                coordRequested, coordSent, coordDecision, coordAlive>>

\* The coordinator detects a participant fault and aborts.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : coordRequested[q]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                coordRequested, coordVote, coordSent, coordAlive>>

\* The coordinator makes its decision once all votes are in.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                coordRequested, coordVote, coordSent, coordAlive>>

\* The coordinator broadcasts its decision, one participant at a time.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                coordRequested, coordVote, coordDecision, coordAlive>>

\* The coordinator crashes and becomes faulty.
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ faulty' = [p \in participants |-> faulty[p]]
  /\ UNCHANGED <<vote, alive, decision, voteSent,
                coordRequested, coordVote, coordSent, coordDecision>>

\* A participant sends its (nondeterministically chosen) vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested,
                coordVote, coordSent, coordDecision, coordAlive>>

\* A participant unilaterally aborts because it voted no.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voteSent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordRequested,
                coordVote, coordSent, coordDecision, coordAlive>>

\* A participant aborts on timeout because the coordinator died without voting.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordRequested,
                coordVote, coordSent, coordDecision, coordAlive>>

\* A participant adopts the coordinator's decision once it is broadcast.
DecideOnCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordRequested,
                coordVote, coordSent, coordDecision, coordAlive>>

\* A participant crashes and becomes faulty.
PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordRequested,
                coordVote, coordSent, coordDecision, coordAlive>>

CoordStep == \E p \in participants : ReqVote(p) \/ RecvVote(p) \/ DetectFault(p)
              \/ Broadcast(p)

PartStep == \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnCoord(p)

Next ==
  \/ CoordStep \/ MakeDecision \/ CoordDie
  \/ PartStep \/ \E p \in participants : PartDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordStep) /\ WF_vars(PartStep)
        /\ WF_vars(DecideOnCoord)

\* Safety: no two participants ever decide differently.
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit is only possible when every participant voted yes.
CommitValidity ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* An abort is only possible with a no vote, a participant fault, or a coordinator fault.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\A p \in participants : vote[p] = yes) /\ ~\E p \in participants : faulty[p] /\ ~coordAlive

\* Decisions are irrevocable: a commit or abort decision, once made, is permanent.
Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit) => (decision[p] = commit)
    /\ (decision[p] = abort) => (decision[p] = abort)

\* Liveness: the protocol eventually reaches a decision state, a participant fault, or a coordinator fault.
DecisionReached ==
  <> ((\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ ~coordAlive)

====