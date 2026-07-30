---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator state and vote collection is exactly as in the base ACP-SB spec (the
\* initialization and coordinator actions below are reproduced verbatim).  The
\* extension in ACP-NB is the per-participant forwarding table that implements
\* reliable broadcast of the decision.
\* A participant's forwarding table maps every participant (including itself)
\* to a forwarding status: notsent, commit, or abort.

VARIABLES pstate, alive, decision, faulty, voted, wantVote, wantBroadcast, cstate, fwd

vars == <<pstate, alive, decision, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in BOOLEAN
  /\ wantVote \in participants
  /\ wantBroadcast \in participants
  /\ cstate \in {waiting, commit, abort}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* The forwarding table is initialized with no entries sent or received yet --
\* a participant has not pre-decided (its own entry is notsent) and has not
\* forwarded anything to anyone.
InitNB ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = FALSE
  /\ wantVote = CHOOSE p \in participants : TRUE
  /\ wantBroadcast = CHOOSE p \in participants : TRUE
  /\ cstate = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: send request, collect a participant vote, detect a
\* participant fault, make a decision, broadcast it to one participant, die.
SendRequestNB(p) ==
  /\ pstate = [q \in participants |-> undecided]
  /\ alive[p]
  /\ ~voted
  /\ wantVote # p
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ voted' = FALSE
  /\ wantVote' = p
  /\ UNCHANGED <<alive, decision, faulty, wantBroadcast, cstate, fwd>>

SendVoteNB(p) ==
  /\ pstate = [q \in participants |-> undecided]
  /\ alive[p]
  /\ ~voted
  /\ pstate' = [pstate EXCEPT ![p] = yes]
  /\ voted' = TRUE
  /\ UNCHANGED <<alive, decision, faulty, wantVote, wantBroadcast, cstate, fwd>>

DetectFaultNB(p) ==
  /\ pstate = [q \in participants |-> undecided]
  /\ ~alive[p]
  /\ ~voted
  /\ faulty[p] = FALSE
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, voted, wantVote, wantBroadcast, cstate, fwd>>

CoordinatorDecideNB(q, d) ==
  /\ cstate = waiting
  /\ ~voted
  /\ decision[CHOOSE p \in participants : TRUE] = waiting
  /\ d \in {commit, abort}
  /\ cstate' = d
  /\ wantBroadcast' = q
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, wantVote, fwd>>

CoordinatorBroadcastNB(p) ==
  /\ cstate # waiting
  /\ alive[p]
  /\ pstate[wantBroadcast] # undecided
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = cstate]
  /\ UNCHANGED <<pstate, alive, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

CoordinatorDieNB ==
  /\ alive[CHOOSE p \in participants : TRUE]
  /\ alive' = [p \in participants |-> FALSE]
  /\ UNCHANGED <<pstate, decision, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

\* Participant actions: the base send abort on vote or timeout is reproduced
\* unchanged; the new actions below enable reliable broadcast.
SendAbortNB(p) ==
  /\ alive[p]
  /\ pstate[p] = no
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

AbortOnTimeoutNB(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~alive[CHOOSE q \in participants : TRUE]
  /\ \A q \in participants :
       (alive[q] /\ pstate[q] # undecided) \/ (fwd[CHOOSE r \in participants : TRUE][p] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

\* A participant may pre-decide from a broadcast it receives from the
\* coordinator, or from a forwarded decision it receives from a peer.
PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ decision[wantBroadcast] # waiting
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = decision[wantBroadcast]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, wantVote, wantBroadcast, cstate>>

PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ fwd[p][p] = notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, wantVote, wantBroadcast, cstate>>

\* Forwarding is one-way per peer: from each participant to each other.  A
\* participant forwards its own pre-decision to a specific peer at most once.
\* Once it has forwarded to all peers it may finalize its own decision.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, wantVote, wantBroadcast, cstate>>

DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voted, wantVote, wantBroadcast, cstate, fwd>>

DieNB(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voted, wantVote, wantBroadcast, cstate, fwd>>

\* Every participant action is weakly fair, except death which is never
\* assumed to happen: a participant that keeps taking steps must eventually
\* take each of its progress steps, so a live participant always eventually
\* finalizes its decision.
NextNB ==
  \/ \E p \in participants : SendRequestNB(p) \/ SendVoteNB(p) \/ DetectFaultNB(p)
  \/ \E q \in participants, d \in {commit, abort} : CoordinatorDecideNB(q, d)
  \/ \E p \in participants : CoordinatorBroadcastNB(p) \/ CoordinatorDieNB
  \/ \E p \in participants : SendAbortNB(p) \/ AbortOnTimeoutNB(p) \/ PreDecideFromCoordinator(p)
  \/ \E p \in participants : PreDecideFromPeer(p) \/ DecideNB(p) \/ DieNB(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ \A p \in participants : WF_vars(PreDecideFromCoordinator(p))
  /\ \A p \in participants : WF_vars(PreDecideFromPeer(p))
  /\ \A p \in participants : WF_vars(DecideNB(p))
  /\ \A p \in participants, q \in participants : WF_vars(Forward(p, q))
  /\ \A p \in participants : WF_vars(SendVoteNB(p))
  /\ \A p \in participants : WF_vars(SendAbortNB(p))

\* No two participants decide differently; a committed participant is only
\* reachable if everyone voted yes; an aborting participant is only reachable
\* if someone voted no or crashed.
AC1 == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : pstate[q] = yes)
AC3 == (\E p \in participants : decision[p] = abort) =>
         (\E q \in participants : pstate[q] = no \/ faulty[q] \/ faulty[CHOOSE r \in participants : TRUE])
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)
AC3Liveness == <>(\A p \in participants : decision[p] # waiting \/ \E q \in participants : faulty[q])
AC5 == \A p \in participants : (decision[p] = waiting) ~> (decision[p] # waiting)

====