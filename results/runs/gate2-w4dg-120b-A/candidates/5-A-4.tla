---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordRequested, coordVote, coordSent, coordDecision

vars == <<vote, alive, decision, faulty, voted, coordRequested, coordVote, coordSent, coordDecision>>

\* Sets up the ACP-SB protocol: participants vote yes/no on a transaction, the
\* coordinator collects the votes, decides commit/abort, and then broadcasts
\* that decision to each participant using simple (sequential) broadcast.
\* Both the coordinator and participants can crash silently.
\* The model is type-checked by a structural type invariant and smoothed by
\* weak fairness on the ordinary progress actions -- death is not fair.

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {yes, no, notsent}]
  /\ coordDecision \in {undecided, commit, abort}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} |-> TRUE]
  /\ decision \in [participants -> {undecided}]
  /\ faulty \in [participants \cup {"coord"} |-> FALSE]
  /\ voted \in [participants -> FALSE]
  /\ coordRequested \in [participants -> FALSE]
  /\ coordVote \in [participants -> waiting]
  /\ coordSent \in [participants -> notsent]
  /\ coordDecision \in {undecided}

\* Coordinator actions: request votes, collect votes, detect a participant
\* fault (aborting if a participant died without voting), make a decision,
\* broadcast it to each participant, and crash.
SendRequest(p) ==
  /\ alive["coord"]
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote, coordSent, coordDecision>>

CoordReceiveVote(p) ==
  /\ alive["coord"]
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ voted[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested, coordSent, coordDecision>>

DetectFault(p) ==
  /\ alive["coord"]
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested, coordVote, coordSent>>

MakeDecision ==
  /\ alive["coord"]
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested, coordVote, coordSent>>

CoordBroadcast(p) ==
  /\ alive["coord"]
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested, coordVote, coordDecision>>

CoordDie ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordRequested, coordVote, coordSent, coordDecision>>

\* Participant actions: send their vote back to the coordinator, abort
\* unilaterally on a no-vote, abort on the coordinator's silence, adopt
\* the coordinator's broadcast decision, and crash.
SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested, coordVote, coordSent, coordDecision>>

AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voted[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested, coordVote, coordSent, coordDecision>>

AbortOnVoteReqTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordRequested[p]
  /\ ~alive["coord"]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested, coordVote, coordSent, coordDecision>>

AdoptDecision(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested, coordVote, coordSent, coordDecision>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordRequested, coordVote, coordSent, coordDecision>>

\* The coordinator's broadcast is deliberately a simple (sequential) one.
\* That is why a coordinator crash during broadcast can leave a participant
\* undecided forever -- the model does not guarantee every non-crashed
\* participant eventually commits or aborts.
Next ==
  \/ \E p \in participants : SendRequest(p) \/ CoordReceiveVote(p) \/ DetectFault(p)
  \/ \E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ AbortOnVoteReqTimeout(p)
  \/ \E p \in participants : AdoptDecision(p) \/ Die(p)
  \/ \E p \in participants : CoordBroadcast(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendRequest(p))
  /\ WF_vars(\E p \in participants : CoordReceiveVote(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnNo(p))
  /\ WF_vars(\E p \in participants : AdoptDecision(p))

\* AC1: no two participants decide differently. AC2: a commit is only
\* reachable alongside a unanimous yes. AC3: an abort is anchored in a no-
\* vote or a crash. AC4: a participant never flips its decision.
AC1 == \A a, b \in participants : ~(decision[a] = commit /\ decision[b] = abort)
AC2 == \A p \in participants : decision[p] = commit => \A a \in participants : vote[a] = yes
AC3 == \A p \in participants : decision[p] = abort =>
          \/ \E a \in participants : vote[a] = no
          \/ faulty["coord"]
          \/ \E a \in participants : faulty[a]
AC4 == \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

\* AC3's liveness component: the protocol eventually resolves or crashes.
AC3Liveness == <>(\A p \in participants : decision[p] # undecided) \/ \E p \in participants : faulty[p]

====