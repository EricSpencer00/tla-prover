---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, or the decision being spread.
ExtDecision == {notsent, commit, abort}

VARIABLES vote, alive, decision, faulty, voteSent, pstate, csent, forwarded

vars == <<vote, alive, decision, faulty, voteSent, pstate, csent, forwarded>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ pstate \in {waiting, notsent}
    /\ csent \subseteq participants
    /\ forwarded \in [participants -> [participants -> ExtDecision]]

\* Forwarding entries for a participant start as not-sent; they are set
\* either by receiving the coordinator's broadcast or by peer forwarding.
InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ pstate = waiting
    /\ csent = {}
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator's broadcast flags a participant; that is the trigger,
\* not the delivery -- delivery is separate and may happen later or not.
BroadcastNB(p) ==
    /\ p \notin csent
    /\ csent' = csent \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, pstate, forwarded>>

\* A participant receives the coordinator's broadcast and stores it locally.
PreDecideCoord(p, d) ==
    /\ alive[p]
    /\ forwarded[p][p] = notsent
    /\ p \in csent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = d]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, pstate, csent>>

\* A participant receives a forwarded decision from another participant.
PreDecidePeer(p, q, d) ==
    /\ alive[p]
    /\ forwarded[p][p] = notsent
    /\ forwarded[q][p] = d
    /\ forwarded' = [forwarded EXCEPT ![p][p] = d]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, pstate, csent>>

\* A pre-decision is forwarded to another participant that has not yet seen it.
Forward(p, q) ==
    /\ alive[p]
    /\ forwarded[p][p] # notsent
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, pstate, csent>>

\* Only after every alive participant has been forwarded the pre-decision
\* may a participant commit or abort locally (non-blocking termination).
Decide(p) ==
    /\ alive[p]
    /\ forwarded[p][p] # notsent
    /\ \A q \in participants : ~alive[q] \/ forwarded[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, pstate, csent, forwarded>>

CoordDie == Die(coord)

Participate(p) ==
    /\ p \in participants
    /\ pstate = waiting
    /\ pstate' = notsent
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, csent, forwarded>>

\* A participant aborts on timeout when the coordinator is dead and no
\* live path from the coordinator exists (no broadcast, no peer forward).
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~alive[coord]
    /\ csent = {}
    /\ \A q \in participants : alive[q] => \A r \in participants : forwarded[r][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, pstate, csent, forwarded>>

Die(n) ==
    /\ alive[n]
    /\ ~faulty[n]
    /\ alive' = [alive EXCEPT ![n] = FALSE]
    /\ faulty' = [faulty EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, pstate, csent, forwarded>>

Vote(p, v) ==
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, pstate, csent, forwarded>>

VoteSome == \E p \in participants, v \in {yes, no} : Vote(p, v)

DecideSome == \E p \in participants : Decide(p)

Next ==
    \/ VoteSome
    \/ \E p \in participants, q \in participants :
        Forward(p, q) \/ PreDecidePeer(p, q, commit) \/ PreDecidePeer(p, q, abort)
    \/ \E p \in participants, d \in {commit, abort} : PreDecideCoord(p, d)
    \/ DecideSome
    \/ \E p \in participants : AbortOnTimeout(p) \/ Die(p) \/ Participate(p)
    \/ CoordDie

SpecNB ==
    /\ InitNB
    /\ [][Next]_vars
    /\ WF_vars(VoteSome)
    /\ WF_vars(DecideSome)
    /\ WF_vars(CoordDie)

\* No two participants may reach different decisions.
AgreementNB == \A a, b \in participants : ~(decision[a] = commit /\ decision[b] = abort)

\* A commit requires unanimity; an abort is explained by a no vote or a fault.
CommitValidNB == \A a \in participants : decision[a] = commit => (\A b \in participants : vote[b] = yes)

AbortValidNB ==
    \A a \in participants :
        decision[a] = abort =>
            \E b \in participants :
                \/ vote[b] = no
                \/ faulty[b]
                \/ ~alive[coord]

IrrevocabilityNB ==
    \A a \in participants :
        decision[a] # undecided =>
            (decision[a] = commit \/ decision[a] = abort)

\* Every non-faulty participant eventually decides.
EventualDecisionNB == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

\* The trivial outcome: all decided, or some fault occurred.
OutcomesExhausted == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ ~alive[coord])

====