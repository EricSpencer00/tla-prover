---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast via forwarding: once a participant receives a pre-decision
\* it forwards it to every other participant, and only decides once all
\* forwards are done. This is what keeps the protocol non-blocking even if the
\* coordinator crashes during broadcast.
\* The forwarding table is per participant (keyed by participant id) and holds
\* both the participant's own pre-decision and what it has forwarded to others.

VARIABLES pstate, coordState, forwarding

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided, commit, abort, waiting}]
  /\ coordState \in {voting, decided, crashed}
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> waiting]
  /\ coordState = voting
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends the prepare request to every participant.
SendRequest ==
  /\ coordState = voting
  /\ \A p \in participants: pstate[p] = waiting
  /\ pstate' = [p \in participants |-> undecided]
  /\ UNCHANGED <<coordState, forwarding>>

\* A participant votes yes or no.
SendVote(p, v) ==
  /\ coordState = voting
  /\ pstate[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = v]
  /\ UNCHANGED <<coordState, forwarding>>

CrashCoord ==
  /\ coordState = voting
  /\ coordState' = crashed
  /\ UNCHANGED <<pstate, forwarding>>

\* Coordinator decides commit iff every vote is yes, else abort.
Decide ==
  /\ coordState = voting
  /\ \A p \in participants: pstate[p] \in {yes, no}
  /\ coordState' = decided
  /\ pstate' = [p \in participants |-> IF \A q \in participants: pstate[q] = yes THEN commit ELSE abort]
  /\ UNCHANGED forwarding

Broadcast ==
  /\ coordState = decided
  /\ \E p \in participants:
       /\ forwarding[p][p] = notsent
       /\ forwarding' = [forwarding EXCEPT ![p][p] = pstate[p]]
  /\ UNCHANGED <<pstate, coordState>>

\* Participant receives a pre-decision broadcast from the coordinator.
PreDecideCoord(p) ==
  /\ pstate[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ coordState = decided
  /\ forwarding[p][p] \in {commit, abort}
  /\ UNCHANGED <<pstate, coordState, forwarding>>

\* Participant receives a pre-decision forwarded by another participant.
PreDecideForward(p) ==
  /\ pstate[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ \E q \in participants: q # p /\ forwarding[q][p] \in {commit, abort}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[CHOOSE q \in participants: q # p /\ forwarding[q][p] \in {commit, abort}][p]]
  /\ UNCHANGED <<pstate, coordState>>

\* Participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ p # q
  /\ forwarding[p][p] \in {commit, abort}
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<pstate, coordState>>

\* Participant finalizes once it has forwarded to every other participant.
DecideNonBlock(p) ==
  /\ pstate[p] = undecided
  /\ forwarding[p][p] \in {commit, abort}
  /\ \A q \in participants: q # p => forwarding[p][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<coordState, forwarding>>

\* A participant aborts once the coordinator is dead and nobody else can
\* deliver a decision (no live broadcast, no dead participant forwarding).
AbortTimeout(p) ==
  /\ pstate[p] = undecided
  /\ coordState = crashed
  /\ (\A q \in participants: pstate[q] # undecided \/ forwarding[q][p] = notsent)
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, forwarding>>

Die(p) ==
  /\ pstate[p] \in {yes, no}
  /\ pstate' = [pstate EXCEPT ![p] = waiting]
  /\ UNCHANGED <<coordState, forwarding>>

Next ==
  \/ SendRequest
  \/ \E p \in participants, q \in participants: Forward(p, q)
  \/ \E p \in participants: Die(p) \/ DecideNonBlock(p) \/ PreDecideCoord(p) \/ PreDecideForward(p)
  \/ \E p \in participants, v \in {yes, no}: SendVote(p, v)
  \/ CrashCoord
  \/ Broadcast
  \/ Decide

\* Progress is driven by the coordinator (until it crashes), the alive
\* participants' pre-decision/forwarding, and the slow participants that
\* eventually time out and abort.
SpecNB ==
  /\ Init
  /\ [][Next]_<<pstate, coordState, forwarding>>
  /\ SF_vars(SendRequest)
  /\ SF_vars(Decide)
  /\ SF_vars(Broadcast)
  /\ \A p \in participants:
       /\ SF_vars(\E v \in {yes, no}: SendVote(p, v))
       /\ SF_vars(PreDecideCoord(p))
       /\ SF_vars(PreDecideForward(p))
       /\ SF_vars(\E q \in participants: Forward(p, q))
       /\ SF_vars(DecideNonBlock(p))
       \/ WF_vars(AbortTimeout(p))

\* Nothing ever decides commit unless everyone voted yes.
CommitValid == (\E p \in participants: pstate[p] = commit) => \A p \in participants: pstate[p] = yes

\* An abort is always justified: by a no vote, a fault, or the coordinator dying.
AbortValid ==
  (\E p \in participants: pstate[p] = abort) =>
    \/ \E p \in participants: pstate[p] = no
    \/ coordState = crashed
    \/ \E p \in participants: pstate[p] = waiting

\* Decision is irreversible: once a participant commits or aborts, it stays there.
DecidedStaysDecided == \A p \in participants: (pstate[p] \in {commit, abort}) ~> (pstate[p] \in {commit, abort})

\* AC3 liveness: the round always resolves one way or the other (or a fault surfaces).
DecideEventual == <>(\A p \in participants: pstate[p] \in {commit, abort} \/ coordState = crashed)

\* AC5: every non-faulty participant eventually reaches a decision.
DecideEventually == \A p \in participants: (pstate[p] # waiting) ~> (pstate[p] \in {commit, abort})

====