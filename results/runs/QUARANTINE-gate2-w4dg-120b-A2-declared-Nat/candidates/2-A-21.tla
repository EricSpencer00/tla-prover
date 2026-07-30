---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* A participant's forwarding table carries one entry per participant
\* (including itself), each of which is the forwarding status for that
\* recipient. The entry at the participant's own index is the value it
\* has pre-decided on, whether from the coordinator directly or from
\* another participant's forwarding message.
\* notsent: no decision received or forwarded yet.
\* commit / abort: pre-decision stored, or decision forwarded.
RecurDom == [participants -> {notsent, commit, abort}]

VARIABLES vote, alive, decision, faulty, sentVote
VARIABLES coordinator, voteCollector, reqCollected
VARIABLES broadcastTo, forwarding, done

vars == <<vote, alive, decision, faulty, sentVote, coordinator,
          voteCollector, reqCollected, broadcastTo, forwarding, done>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordinator \in {commit, abort, waiting}
    /\ voteCollector \in {yes, no, undecided}
    /\ reqCollected \in BOOLEAN
    /\ broadcastTo \in [participants -> {notsent, commit, abort}]
    /\ forwarding \in [participants -> RecurDom]
    /\ done \in [participants -> BOOLEAN]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordinator = waiting
    /\ voteCollector = undecided
    /\ reqCollected = FALSE
    /\ broadcastTo = [p \in participants |-> notsent]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ done = [p \in participants |-> FALSE]

\* Coordinator actions are inherited from the base ACP-SB protocol.
SendRequest ==
    /\ coordinator = waiting
    /\ coordinator' = abort
    /\ reqCollected' = FALSE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  voteCollector, broadcastTo, forwarding, done>>

GetVote(p) ==
    /\ coordinator = abort
    /\ alive[p]
    /\ ~sentVote[p]
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, coordinator,
                  voteCollector, reqCollected, broadcastTo, forwarding, done>>

DetectFault(p) ==
    /\ coordinator = abort
    /\ ~sentVote[p]
    /\ vote[p] = yes
    /\ voteCollector # no
    /\ voteCollector' = yes
    /\ reqCollected' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  coordinator, broadcastTo, forwarding, done>>

MakeDecision ==
    /\ coordinator = abort
    /\ reqCollected
    /\ coordinator' = IF voteCollector = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  voteCollector, reqCollected, broadcastTo, forwarding, done>>

BroadcastDecision(p) ==
    /\ coordinator \in {commit, abort}
    /\ broadcastTo[p] = notsent
    /\ broadcastTo' = [broadcastTo EXCEPT ![p] = coordinator]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  coordinator, voteCollector, reqCollected, forwarding, done>>

CoordinatorDie ==
    /\ coordinator \in {commit, abort}
    /\ coordinator' = waiting
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  voteCollector, reqCollected, broadcastTo, forwarding, done>>

\* A participant pre-decides from a broadcast it received from the coordinator.
PreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastTo[p] # notsent
    /\ forwarding[p][p] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = broadcastTo[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  coordinator, voteCollector, reqCollected, broadcastTo, done>>

\* A participant pre-decides from a forwarding message from another participant.
PreDecideFromForwarding(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in participants :
         /\ q # p
         /\ forwarding[q][p] # notsent
         /\ forwarding[p][p] = notsent
         /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  coordinator, voteCollector, reqCollected, broadcastTo, done>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p]
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                  coordinator, voteCollector, reqCollected, broadcastTo, done>>

\* A participant decides once it has forwarded its pre-decision to everyone.
Decide(p) ==
    /\ alive[p]
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ done' = [done EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  coordinator, voteCollector, reqCollected,
                  broadcastTo, forwarding>>

\* A participant aborts on timeout once the coordinator is dead and
\* neither a broadcast nor a forwarding is available to it.
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordinator = waiting
    /\ broadcastTo[p] = notsent
    /\ \A q \in participants : forwarding[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ done' = [done EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  coordinator, voteCollector, reqCollected,
                  broadcastTo, forwarding>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote,
                  coordinator, voteCollector, reqCollected,
                  broadcastTo, forwarding, done>>

\* Progress requires fair treatment of the whole set of participant actions
\* (pre-deciding, forwarding, deciding, aborting), and of the coordinator
\* actions (making a decision, broadcasting it). Death transitions are
\* excluded from weak fairness so crashes cannot stall the model.
Next ==
    \/ SendRequest \/ CoordinatorDie \/ MakeDecision
    \/ \E p \in participants :
         \/ GetVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
         \/ PreDecideFromCoordinator(p) \/ PreDecideFromForwarding(p)
         \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
    /\ WF_vars(\E p \in participants : PreDecideFromForwarding(p))
    /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(MakeDecision)

\* Safety: no two participants can reach different decisions.
AC1 == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Validity: commit only with a unanimous yes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)

\* Validity: abort only on a no or on a failure.
AC3 == (\E p \in participants : decision[p] = abort) =>
          \/ \E q \in participants : vote[q] = no
          \/ \E q \in participants : faulty[q]
          \/ coordinator = waiting

\* Irrevocability: a decided participant never reverts.
AC4 == \A p \in participants : decision[p] \in {commit, abort} => done[p]

\* Liveness: either everyone decides, or someone fails, or the coordinator fails.
AC3Live == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordinator = waiting)

\* Liveness: the reliable broadcast guarantees every non-faulty participant decides.
AC5 == \A p \in participants : (alive[p] /\ ~done[p]) ~> done[p]

====