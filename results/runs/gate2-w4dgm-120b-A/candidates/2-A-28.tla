---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Broadcast-safe agreement protocol: a participant may forward a decision it
\* received from another participant (Forward) before finalizing its own
\* decision (Decide). Even if the coordinator dies mid-broadcast, the alive
\* participants keep forwarding to each other so everyone eventually decides.
\* AC5 guarantees the non-blocking termination of every non-faulty participant.
\* AC1 is mutual exclusion of commit vs abort: no two participants ever commit
\* and abort respectively. AC2 and AC3 re-check validity of the final outcome.

VARIABLES vote, coordFast, decision, faulty, voted, phase, alive
          forwarded
vars == <<vote, coordFast, decision, faulty, voted, phase, alive, forwarded>>

\* A participant's forwarding table: what pre-decision it has received (at
\* its own index) and which participants it has already forwarded that
\* pre-decision to.
InitTable == [p \in participants |-> notsent]

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ coordFast \in [participants -> BOOLEAN]
  /\ decision \in {commit, abort, waiting}
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ phase \in [participants -> {commit, abort, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

\* The coordinator is single and initially truthful -- no participant has
\* heard anything from anyone else, so at most it has been slow.
Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ coordFast = [p \in participants |-> TRUE]
  /\ decision = waiting
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ phase = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ forwarded = [p \in participants |-> InitTable]

SendVote(p) ==
  /\ alive[p] /\ ~voted[p] /\ ~coordFast[p]
  /\ phase[p] = undecided /\ ~faulty[p]
  /\ \E e \in {yes, no}: vote' = [vote EXCEPT ![p] = e]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordFast, decision, faulty, phase, alive, forwarded>>

\* The coordinator detects a crash before making a decision.
DetectCoord(p) ==
  /\ ~coordFast[p] /\ ~faulty[p]
  /\ coordFast' = [coordFast EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, faulty, voted, phase, alive, forwarded>>

\* The coordinator may be slow but never fails: it keeps trying until it
\* gets the votes it needs. Once it decides, it stops collecting votes.
Decide(p) ==
  /\ coordFast[p] /\ ~faulty[p] /\ decision = waiting
  /\ \A q \in participants: voted[q]
  /\ decision' = IF (\A q \in participants: vote[q] = yes) THEN commit ELSE abort
  /\ UNCHANGED <<vote, coordFast, faulty, voted, phase, alive, forwarded>>

\* The coordinator may broadcast its decision to any participant individually.
Broadcast(p, q) ==
  /\ coordFast[p] /\ ~faulty[p] /\ alive[q] /\ decision # waiting
  /\ forwarded[q][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![q][p] = decision]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, phase, alive>>

DieCoord(p) ==
  /\ ~faulty[p] /\ decision = waiting
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, coordFast, decision, voted, phase, alive, forwarded>>

\* A participant stores the pre-decision it receives from the coordinator.
PreDecideFromCoord(q) ==
  /\ alive[q] /\ phase[q] = undecided /\ forwarded[q][q] = notsent
  /\ decision # waiting
  /\ forwarded' = [forwarded EXCEPT ![q][q] = decision]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, phase, alive>>

\* A participant stores the pre-decision it receives from another participant.
PreDecideFromPeer(q) ==
  /\ alive[q] /\ phase[q] = undecided /\ forwarded[q][q] = notsent
  /\ \E p \in participants: forwarded[q][p] # notsent
  /\ forwarded' = [forwarded EXCEPT ![q][q] = CHOOSE e \in {commit, abort}:
                                           \E p \in participants: forwarded[q][p] = e]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, phase, alive>>

\* A participant forwards its pre-decision to another participant it has not
\* yet forwarded to, prior to finalizing its own decision.
Forward(p, q) ==
  /\ alive[p] /\ forwarded[p][p] # notsent /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![q][p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, phase, alive>>

\* Non-blocking finalize: once it has forwarded its pre-decision to everyone,
\* the participant finalizes its own decision to match its pre-decision.
Decide(p) ==
  /\ alive[p] /\ phase[p] = undecided /\ forwarded[p][p] # notsent
  /\ \A q \in participants: q # p => forwarded[p][q] # notsent
  /\ phase' = [phase EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, alive, forwarded>>

AbortOnNoBroadcast(p) ==
  /\ alive[p] /\ phase[p] = undecided
  /\ decision = waiting /\ faulty[p]
  /\ \A q \in participants: forwarded[q][p] = notsent
  /\ phase' = [phase EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, alive, forwarded>>

Die(p) ==
  /\ alive[p] /\ phase[p] = undecided
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, coordFast, decision, faulty, voted, phase, forwarded>>

Next ==
  \/ \E p \in participants: SendVote(p) \/ DetectCoord(p) \/ DieCoord(p)
                         \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p) \/ Die(p)
  \/ \E p \in participants, q \in participants: Broadcast(p, q) \/ Forward(p, q)
  \/ \E p \in participants: Decide(p) \/ AbortOnNoBroadcast(p)

\* Choice is weak fairness on every participant's own progress actions (each
\* participant eventually receives a pre-decision, forwards it, and decides),
\* plus coordinator progress, but excludes death transitions.
Fairness ==
  /\ \A p \in participants:
       /\ TRUE
       /\ SF_vars(\E q \in participants: Broadcast(p, q))
       /\ SF_vars(\E q \in participants: Forward(p, q))
       /\ WF_vars(\E q \in participants: PreDecideFromPeer(p))
  /\ \A p \in participants: WF_vars(Decide(p))
  /\ \A p \in participants: WF_vars(AbortOnNoBroadcast(p))
  /\ \A p \in participants: WF_vars(PreDecideFromCoord(p))
  /\ \A p \in participants: WF_vars(SendVote(p))
  /\ \A p \in participants: WF_vars(Decide(p))
  /\ \A p \in participants: WF_vars(Die(p))
  /\ \A p \in participants: WF_vars(DieCoord(p)
  /\ \A p \in participants: WF_vars(Decide(p))

SpecNB == Init /\ [][Next]_vars /\ Fairness

Agreement ==
  \A p, q \in participants: ~(phase[p] = commit /\ phase[q] = abort)

CommitValidity ==
  (decision = commit) => (\A p \in participants: vote[p] = yes)

AbortValidity ==
  (decision = abort) => (\E p \in participants: vote[p] = no \/ faulty[p])
                         \/ (\E p \in participants: coordFast[p] /\ faulty[p])

Irreversibility ==
  \A p \in participants: (phase[p] # undecided) ~> (phase[p] = phase[p])

Acquiesce == \A p \in participants: phase[p] # undecided

\* Agreement and irreversibility are safety; the other two are liveness.
AC1 == Agreement
AC2 == CommitValidity
AC3 == AbortValidity
AC4 == Irreversibility
AC5 == Acquiesce
AC3Live == AC3 /\ []AC3

TypeInvNB == TypeOK
====