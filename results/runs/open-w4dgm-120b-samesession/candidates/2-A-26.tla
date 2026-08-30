---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the simple broadcast protocol (ACP-SB) with a forwarding table per
\* participant, so that a crashed coordinator's decision still gets disseminated.
VARIABLES pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, calive, forwarding

vars == <<pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, calive, forwarding>>

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ palive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentvote \in [participants -> BOOLEAN]
    /\ cstate \in {yes, no}
    /\ cvote \in {yes, no, undecided}
    /\ broadcasted \in [participants -> {commit, abort, waiting}]
    /\ calive \in BOOLEAN
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ palive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentvote = [p \in participants |-> FALSE]
    /\ cstate = yes
    /\ cvote = undecided
    /\ broadcasted = [p \in participants |-> waiting]
    /\ calive = TRUE
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ calive
    /\ cvote = undecided
    /\ cvote' = yes
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, broadcasted, calive, forwarding>>

SendVote(p) ==
    /\ ~faulty[p]
    /\ palive[p]
    /\ ~sentvote[p]
    /\ cvote = yes
    /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, palive, decision, faulty, cstate, cvote, broadcasted, calive, forwarding>>

ParticipantVoteStep(p) == SendVote(p)

DetectFault ==
    /\ cvote = yes
    /\ sentvote[p] = FALSE
    /\ cstate' = no
    /\ UNCHANGED <<pstate, palive decision, faulty, sentvote, cvote, broadcasted, calive, forwarding>>

MakeDecision ==
    /\ calive
    /\ cvote = yes
    /\ \A p \in participants : sentvote[p]
    /\ cstate' = IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cvote, broadcasted, calive, forwarding>>

Broadcast ==
    /\ calive
    /\ cstate \in {commit, abort}
    /\ broadcasted' = [p \in participants |-> cstate]
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, cvote, calive, forwarding>>

Die ==
    /\ calive
    /\ calive' = FALSE
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, forwarding>>

\* A participant adopts a pre-decision only from the coordinator's broadcast.
PreDecideCoordinator(p) ==
    /\ palive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] = notsent
    /\ broadcasted[p] # waiting
    /\ forwarding' = [forwarding EXCEPT ![p][p] = broadcasted[p]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, calive>>

\* A participant adopts a pre-decision forwarded by another participant.
PreDecideForward(p) ==
    /\ palive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants : q # p /\ forwarding[q][p] # notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[CHOOSE q \in participants : q # p /\ forwarding[q][p] # notsent][p]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, calive>>

\* Forwarding is the only way a pre-decision reaches another participant.
Forward(p, q) ==
    /\ palive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<pstate, palive, decision, faulty, sentvote, cstate, cvote, broadcasted, calive>>

Decide(p) ==
    /\ palive[p]
    /\ ~faulty[p]
    /\ forwarding[p][p] # notsent
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<pstate, palive, faulty, sentvote, cstate, cvote, broadcasted, calive, forwarding>>

\* A participant aborts when the coordinator has died, no broadcast is available,
\* and no dead participant can still forward a decision to it.
AbortOnTimeout(p) ==
    /\ palive[p]
    /\ ~faulty[p]
    /\ decision[p] = waiting
    /\ ~calive
    /\ \A q \in participants : broadcasted[q] = waiting
    /\ \A q \in participants : ~(~palive[q] /\ \E r \in participants : forwarding[q][p] # notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, palive, faulty, sentvote, cstate, cvote, broadcasted, calive, forwarding>>

DieParticipant(p) ==
    /\ palive[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pstate, decision, sentvote, cstate, cvote, broadcasted, calive, forwarding>>

Next ==
    \/ SendRequest
    \/ DetectFault
    \/ MakeDecision
    \/ Broadcast
    \/ Die
    \/ \E p \in participants : ParticipantVoteStep(p)
    \/ \E p \in participants : PreDecideCoordinator(p)
    \/ \E p \in participants : PreDecideForward(p)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DieParticipant(p)

SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: no two participants ever reach opposite decisions.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
\* A commit is only reachable if every participant voted yes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : pstate[p] = yes)
\* An abort is only reachable if somebody voted no or somebody crashed.
AC3 == (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : pstate[p] = no) \/ (\E p \in participants : faulty[p]) \/ ~calive
\* Decision is permanent: a decided participant never reverts.
AC4 == \A p \in participants : (decision[p] # waiting) ~> (decision[p] = decision[p])

\* Liveness: the non-blocking guarantee -- every non-faulty participant eventually decides.
AC5 == \A p \in participants : (palive[p] /\ ~faulty[p]) ~> (decision[p] # waiting)

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5
====