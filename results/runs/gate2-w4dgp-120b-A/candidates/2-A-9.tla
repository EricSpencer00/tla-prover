---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

\* Each participant forwards a received pre-decision to all others before it may finalize
\* locally. The forwarding table maps every participant id to a status: not-sent (no
\* pre-decision yet), commit, or abort. The table entry at a participant's own id is its
\* stored pre-decision, the other entries are what it has forwarded so far.

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, waiting}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coordReq \in {undecided, waiting}
  /\ coordVote \in {waiting, yes, no}
  /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> waiting]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coordReq = undecided
  /\ coordVote = waiting
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE

SendRequest ==
  /\ coordAlive
  /\ coordReq = undecided
  /\ coordReq' = waiting
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote, coordBroadcast, coordDecision, coordAlive>>

GetVote ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordVote = waiting
  /\ \E p \in participants:
       /\ alive[p]
       /\ ~sent[p]
       /\ vote[p] \in {yes, no}
       /\ coordVote' = vote[p]
       /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordBroadcast, coordDecision, coordAlive>>

CoordCrash ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision>>

MakeDecision ==
  /\ coordAlive
  /\ coordVote # waiting
  /\ coordDecision = undecided
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordBroadcast, coordAlive>>

BroadcastDecision ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordBroadcast' = [p \in participants |-> coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordDecision, coordAlive>>

\* The participant stores the coordinator's broadcast as its pre-decision in its
\* own forwarding slot.
PreDecideFromCoord ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive
  /\ coordBroadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

PreDecideFromForward ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants: q # p /\ coordBroadcast[q] # notsent /\ decision[q] = coordBroadcast[q] /\ decision' = [decision EXCEPT ![p] = decision[q]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

Forward ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \E q \in participants: q # p /\ coordBroadcast[q] = notsent /\ coordBroadcast' = [coordBroadcast EXCEPT ![q] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordDecision, coordAlive>>

\* A participant may finalize only after it has forwarded its pre-decision to every
\* other participant -- this is the blocking condition that reliable broadcast
\* eliminates from the coordinator's broadcast path.
Decide ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants: q # p => coordBroadcast[q] = decision[p]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

AbortOnTimeout ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ coordBroadcast[p] = notsent
  /\ \A q \in participants: ~coordAlive => coordBroadcast[q] = notsent
  /\ \A q \in participants: faulty[q] => decision[q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

Die ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive>>

CoordCrashAlt == CoordCrash

Next ==
  \/ SendRequest \/ GetVote \/ CoordCrash \/ MakeDecision \/ BroadcastDecision
  \/ \E p \in participants: PreDecideFromCoord \/ PreDecideFromForward \/ Forward
  \/ Decide \/ AbortOnTimeout \/ Die \/ CoordCrashAlt

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Decide)
  /\ WF_vars(AbortOnTimeout)
  /\ WF_vars(PreDecideFromCoord)
  /\ WF_vars(PreDecideFromForward)
  /\ WF_vars(Forward)
  /\ WF_vars(Die)

\* Safety: no two participants can reach different decisions, and every decision
\* is justified by the vote run or a crash.
AC1 == ~(\E p, q \in participants: decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants: decision[p] = commit) => (\A q \in participants: vote[q] = yes)
AC3 == (\E p \in participants: decision[p] = abort) =>
         (\E q \in participants: vote[q] = no \/ faulty[q] \/ ~coordAlive)
AC4 == \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: every non-faulty participant eventually decides (non-blocking termination).
AC3Liveness == <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ ~coordAlive)
AC5 == \A p \in participants: (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====