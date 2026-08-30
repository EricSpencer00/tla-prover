--------------------------- MODULE ACP_SB ---------------------------
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  pstate,       \* [participants -> {"alive","faulty"}] : whether each participant is alive
  pvote,        \* [participants -> {yes,no}] : each participant's vote
  pdecided,     \* [participants -> {undecided,commit,abort}] : each participant's final decision
  psent,        \* [participants -> BOOLEAN] : whether each participant has sent its vote
  coordState,   \* "alive" or "faulty"
  coordVote,    \* [participants -> {yes,no,waiting}] : vote received from each participant
  coordDecided, \* {commit,abort,undecided} : coordinator's decision
  sentTo        \* [participants -> {notsent,commit,abort}] : decision broadcast to each participant

vars == <<pstate, pvote, pdecided, psent, coordState, coordVote, coordDecided, sentTo>>

TypeInv ==
  /\ pstate \in [participants -> {"alive","faulty"}]
  /\ pvote \in [participants -> {yes, no}]
  /\ pdecided \in [participants -> {undecided, commit, abort}]
  /\ psent \in [participants -> BOOLEAN]
  /\ coordState \in {"alive", "faulty"}
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordDecided \in {commit, abort, undecided}
  /\ sentTo \in [participants -> {notsent, commit, abort}]

Init ==
  /\ pstate = [pa \in participants |-> "alive"]
  /\ pvote = [pa \in participants |-> IF pa = CHOOSE x \in participants : TRUE THEN yes ELSE no]
  /\ pdecided = [pa \in participants |-> undecided]
  /\ psent = [pa \in participants |-> FALSE]
  /\ coordState = "alive"
  /\ coordVote = [pa \in participants |-> waiting]
  /\ coordDecided = undecided
  /\ sentTo = [pa \in participants |-> notsent]

\* Coordinator sends vote requests to all participants.
SentRequest(pa) ==
  /\ coordState = "alive"
  /\ coordVote[pa] = waiting
  /\ coordVote' = [coordVote EXCEPT ![pa] = waiting]
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordState, coordDecided, sentTo>>

\* Coordinator receives a vote from a participant that has sent it.
ReceiveVote(pa) ==
  /\ coordState = "alive"
  /\ coordDecided = undecided
  /\ coordVote[pa] = waiting
  /\ psent[pa]
  /\ coordVote' = [coordVote EXCEPT ![pa] = pvote[pa]]
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordState, coordDecided, sentTo>>

\* Coordinator detects a participant that crashed without voting, and aborts.
DetectFault(pa) ==
  /\ coordState = "alive"
  /\ coordDecided = undecided
  /\ coordVote[pa] = waiting
  /\ pstate[pa] = "faulty"
  /\ ~psent[pa]
  /\ coordDecided' = abort
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordState, coordVote, sentTo>>

\* Coordinator makes a decision once all votes are in.
Decide ==
  /\ coordState = "alive"
  /\ coordDecided = undecided
  /\ \A pa \in participants : coordVote[pa] # waiting
  /\ coordDecided' = IF \A pa \in participants : coordVote[pa] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordState, coordVote, sentTo>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
Broadcast(pa) ==
  /\ coordState = "alive"
  /\ coordDecided # undecided
  /\ sentTo[pa] = notsent
  /\ sentTo' = [sentTo EXCEPT ![pa] = coordDecided]
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordState, coordVote, coordDecided>>

\* Coordinator crashes.
CoordDie ==
  /\ coordState = "alive"
  /\ coordState' = "faulty"
  /\ UNCHANGED <<pstate, pvote, pdecided, psent, coordVote, coordDecided, sentTo>>

\* A participant sends its vote to the coordinator.
SendVote(pa) ==
  /\ pstate[pa] = "alive"
  /\ ~psent[pa]
  /\ psent' = [psent EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, pvote, pdecided, coordState, coordVote, coordDecided, sentTo>>

\* A participant decides abort unilaterally if its own vote is no.
AbortOnVote(pa) ==
  /\ pstate[pa] = "alive"
  /\ pdecided[pa] = undecided
  /\ psent[pa]
  /\ pvote[pa] = no
  /\ pdecided' = [pdecided EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, pvote, psent, coordState, coordVote, coordDecided, sentTo>>

\* A participant aborts on timeout because the coordinator died without asking.
AbortOnTimeout(pa) ==
  /\ pstate[pa] = "alive"
  /\ pdecided[pa] = undecided
  /\ coordState = "faulty"
  /\ pdecided' = [pdecided EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pstate, pvote, psent, coordState, coordVote, coordDecided, sentTo>>

\* A participant adopts the coordinator's broadcast decision.
DecideFromCoord(pa) ==
  /\ pstate[pa] = "alive"
  /\ pdecided[pa] = undecided
  /\ sentTo[pa] # notsent
  /\ pdecided' = [pdecided EXCEPT ![pa] = sentTo[pa]]
  /\ UNCHANGED <<pstate, pvote, psent, coordState, coordVote, coordDecided, sentTo>>

\* A participant crashes.
PartDie(pa) ==
  /\ pstate[pa] = "alive"
  /\ pstate' = [pstate EXCEPT ![pa] = "faulty"]
  /\ UNCHANGED <<pvote, pdecided, psent, coordState, coordVote, coordDecided, sentTo>>

Next ==
  \/ Decide
  \/ CoordDie
  \/ \E pa \in participants :
       SentRequest(pa) \/ ReceiveVote(pa) \/ DetectFault(pa) \/ Broadcast(pa)
         \/ SendVote(pa) \/ AbortOnVote(pa) \/ AbortOnTimeout(pa)
         \/ DecideFromCoord(pa) \/ PartDie(pa

\* Fairness assumptions: actions that can make progress are given weak fairness.
Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E pa \in participants : SendVote(pa))
  /\ WF_vars(\E pa \in participants : AbortOnVote(pa))
  /\ WF_vars(\E pa \in participants : AbortOnTimeout(pa))
  /\ WF_vars(\E pa \in participants : DecideFromCoord(pa))

\* Safety: No two participants ever reach conflicting final decisions.
Agreement ==
  \A pa1, pa2 \in participants :
    (pdecided[pa1] = commit /\ pdecided[pa2] = abort) => FALSE

\* Safety: Committing requires unanimity.
CommitValidity ==
  \A pa \in participants : pdecided[pa] = commit => \A q \in participants : pvote[q] = yes

\* Safety: Aborting requires a dissent, a faulty participant, or a faulty coordinator.
AbortValidity ==
  \A pa \in participants :
    pdecided[pa] = abort =>
      (\E q \in participants : pvote[q] = no) \/ (\E q \in participants : pstate[q] = "faulty") \/ (coordState = "faulty")

\* Safety: Irreversibility -- once a participant decides commit or abort it never flips.
Irreversible ==
  \A pa \in participants :
    /\ (pdecided[pa] = commit => pdecided' [pa] = commit)
    /\ (pdecided[pa] = abort => pdecided' [pa] = abort)

\* Liveness: the protocol always makes progress toward a decision or failure.
EventualResolution ==
  <> (\A pa \in participants : pdecided[pa] # undecided \/ coordState = "faulty" \/ (\E q \in participants : pstate[q] = "faulty"))

Theorem AC1 == Agreement
Theorem AC2 == CommitValidity
Theorem AC3 == AbortValidity
Theorem AC4 == Irreversible
===========================================================================