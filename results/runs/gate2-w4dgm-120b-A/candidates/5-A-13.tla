---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator holds the authoritative two-phase decision; participants may each
\* decide abort unilaterally (voluntary abort) or from the coordinator's broadcast.
\* Simple broadcast is a single-shot per participant channel, so a crash in the
\* middle can strand participants undecided -- the spec does NOT guarantee
\* termination, only that no two participants can decide differently.

VARIABLES partVote, partAlive, partDecision, partFaulty, partSent,
          coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<partVote, partAlive, partDecision, partFaulty, partSent,
           coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Init ==
  /\ partVote = [p \in participants |-> IF \E e \in {yes, no} : e = yes THEN yes ELSE no]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partSent = [p \in participants |-> FALSE]
  /\ coordAsked = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant (beginning of round one).
Ask(p) ==
  /\ coordAlive
  /\ ~coordAsked[p]
  /\ coordAsked' = [coordAsked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a participant's vote (a broadcast message into the
\* coordinator's mailbox -- applied at most once per participant).
Recv(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordAsked[p]
  /\ coordRecv[p] = waiting
  /\ partSent[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = partVote[p]]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordAsked, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Failure detection: a participant that died without sending its vote forces the
\* coordinator to abort (irrecoverable crash, not a timeout).
DetectFail(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordAsked[p]
  /\ coordRecv[p] = waiting
  /\ ~partAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordAlive, coordFaulty>>

\* Coordinator makes the decision once it has every vote and is still alive.
Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordAlive, coordFaulty>>

\* Simple broadcast: the coordinator sends its decision to a participant exactly
\* once.  A crash after some of these have gone out strands the rest undecided.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordAsked, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordDecision, coordFaulty>>

SendVote(p) ==
  /\ partAlive[p]
  /\ coordAsked[p]
  /\ partSent[p] = FALSE
  /\ partSent' = [partSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty,
                 coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Unanimous commit path is only possible if every participant actually voted
\* yes; if any voted no, the participant may abort on its own regardless of the
\* coordinator's broadcast.
AbortOnVote(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partSent[p]
  /\ partVote[p] = no
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnNoRequest(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~coordAsked[p]
  /\ coordFaulty
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partSent,
                 coordAsked, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partVote, partDecision, partSent, coordAsked, coordRecv,
                 coordSent, coordDecision, coordAlive, coordFaulty>>

\* Weak fairness is assumed on SendVote, Recv, Decide, Broadcast (progress
\* steps); death steps are not subject to fairness and may happen at any time.
CoordStep == Decide \/ CoordDie
PartStep(p) == SendVote(p) \/ AbortOnVote(p) \/ AbortOnNoRequest(p) \/ DecideFromBroadcast(p) \/ PartDie(p)

Next ==
  \/ \E p \in participants : Ask(p)
  \/ CoordStep
  \/ \E p \in participants : CoordStep
  \/ \E p \in participants : Recv(p)
  \/ \E p \in participants : Broadcast(p
  \/ \E p \in participants : DetectFail(p)
  \/ \E p \in participants : PartStep(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : SF_vars(PartStep(p))
  /\ SF_vars(CoordStep)

\* No two participants ever decide differently: commit is unanimous across
\* participants, and abort can only be reached through unanimity of yes plus a
\* coordinating abort, or through a vote of no / a crash.
DecisionAgreement ==
  \A p1, p2 \in participants :
    (partDecision[p1] = commit /\ partDecision[p2] = abort) => FALSE

\* A committed participant implies a unanimous yes vote.
CommitRequiresUnanimousYes ==
  \A p \in participants : (partDecision[p] = commit) => (\A q \in participants : partVote[q] = yes)

\* An aborted participant implies a no vote, a participant crash, or a coordinator crash.
AbortJustified ==
  \A p \in participants :
    (partDecision[p] = abort) =>
      (\E q \in participants : partVote[q] = no \/ partFaulty[q]) \/ coordFaulty

\* A participant decides at most once: commit and abort are mutually exclusive and
\* sticky, so a participant that commits never aborts and vice versa.
DecisionIrreversible ==
  \A p \in participants :
    (partDecision[p] = commit => partDecision[p] # abort) /\ (partDecision[p] = abort => partDecision[p] # commit)

TypeInv ==
  /\ partVote \in [participants -> {yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partSent \in [participants -> BOOLEAN]
  /\ coordAsked \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {waiting, yes, no}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

\* Commitment protocols are expected to terminate even when participants
\* crash; this simple-broadcast version does not satisfy that, so this is the
\* only liveness property the spec claims.
SomeDecideOrCrash ==
  <>(\A p \in participants : partDecision[p] # undecided) \/ coordFaulty \/ (\E p \in participants : partFaulty[p])

====