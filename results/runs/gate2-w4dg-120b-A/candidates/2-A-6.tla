---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* Non-Blocking Atomic Commitment with reliable broadcast forwarding.
\* Participants forward received decisions to every other participant before
\* finalizing locally, so no alive participant is left hanging if the
\* coordinator crashes mid-broadcast. Derived from the simple broadcast
\* variant (ACP-SB); the grammar below must match the reference .cfg exactly.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES prevote, alive, decision, faulty, vsent, coordState, forwards

vars == <<prevote, alive, decision, faulty, vsent, coordState, forwards>>

Phases == {"req", "vote", "broadcast", "decide", "dead"}
States == {waiting, commit, abort}

Entry == union of [States \cup {notsent}]
Table == [participants -> Entry]

TypeInvNB ==
    /\ prevote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants \cup {"coordinator"} -> BOOLEAN]
    /\ decision \in [participants -> States \cup {waiting}]
    /\ faulty \in [participants \cup {"coordinator"} -> BOOLEAN]
    /\ vsent \in [participants -> BOOLEAN]
    /\ coordState \in [Phases]
    /\ forwards \in [participants -> Table]

InitEntry ==
    /\ prevote = [p \in participants |-> undecided]
    /\ alive = [p \in participants \cup {"coordinator"} |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants \cup {"coordinator"} |-> FALSE]
    /\ vsent = [p \in participants |-> FALSE]
    /\ coordState = [phase |-> "req"]
    /\ forwards = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions; identical to the simple broadcast variant.
SendRequest ==
    /\ coordState.phase = "req"
    /\ coordState' = [coordState EXCEPT !.phase = "vote"]
    /\ UNCHANGED <<prevote, alive, decision, faulty, vsent, forwards>>

GetVote(p) ==
    /\ alive[p]
    /\ coordState.phase = "vote"
    /\ ~vsent[p]
    /\ \E v \in {yes, no} : prevote' = [prevote EXCEPT ![p] = v]
    /\ vsent' = [vsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, coordState, forwards>>

CoordDetectFault ==
    /\ coordState.phase \in {"req", "vote"}
    /\ \E p \in participants : ~alive[p]
    /\ coordState' = [coordState EXCEPT !.phase = "dead"]
    /\ UNCHANGED <<prevote, alive, decision, faulty, vsent, forwards>>

MakeDecision ==
    /\ coordState.phase = "vote"
    /\ \A p \in participants : prevote[p] = yes
    /\ coordState' = [coordState EXCEPT !.phase = "broadcast"]
    /\ UNCHANGED <<prevote, alive, decision, faulty, vsent, forwards>>

BroadcastDecision ==
    /\ coordState.phase = "broadcast"
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = waiting
         /\ decision' = [decision EXCEPT ![p] = commit]
    /\ UNCHANGED <<prevote, alive, vsent, coordState, forwards, faulty>>

CoordDie ==
    /\ alive["coordinator"]
    /\ alive' = [alive EXCEPT !["coordinator"] = FALSE]
    /\ coordState' = [coordState EXCEPT !.phase = "dead"]
    /\ faulty' = [faulty EXCEPT !["coordinator"] = TRUE]
    /\ UNCHANGED <<prevote, decision, vsent, forwards>>

\* Participant actions: the reliable broadcast extension.
PreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ forwards[p][p] = notsent
    /\ \E q \in participants : alive[q] /\ decision[q] # waiting /\ decision[q] # waiting
    /\ forwards' = [forwards EXCEPT ![p][p] = decision[q]]

PreDecideFromPeer(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ forwards[p][p] = notsent
    /\ \E q \in participants :
         /\ alive[q]
         /\ q # p
         /\ forwards[q][p] # notsent
         /\ forwards' = [forwards EXCEPT ![p][p] = forwards[q][p]]
    /\ UNCHANGED <<prevote, alive, decision, faulty, vsent, coordState>>

Forward(p, q) ==
    /\ alive[p]
    /\ p # q
    /\ forwards[p][p] # notsent
    /\ forwards[p][q] = notsent
    /\ forwards' = [forwards EXCEPT ![p][q] = forwards[p][p]]
    /\ UNCHANGED <<prevote, alive, decision, faulty, vsent, coordState>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ \A q \in participants : q # p => forwards[p][q] # notsent
    /\ forwards[p][p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = forwards[p][p]]
    /\ UNCHANGED <<prevote, alive, faulty, vsent, coordState, forwards>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ ~alive["coordinator"]
    /\ \A q \in participants : decision[q] = waiting
    /\ \A q \in participants : \A r \in participants :
         (r # q /\ ~alive[r]) => forwards[r][q] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<prevote, alive, faulty, vsent, coordState, forwards>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<prevote, decision, vsent, coordState, forwards>>

Next ==
    \/ SendRequest \/ CoordDetectFault \/ MakeDecision \/ BroadcastDecision \/ CoordDie
    \/ \E p \in participants :
         GetVote(p) \/ PreDecideFromCoordinator(p) \/ PreDecideFromPeer(p)
         \/ AbortOnTimeout(p) \/ Die(p) \/ Decide(p) \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ InitEntry
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p) \/ PreDecideFromPeer(p))
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p) \/ AbortOnTimeout(p))

\* Safety: decisions agree, commits need unanimous yes-votes, aborts need a vote
\* no, a participant fault, or a coordinator fault, and decisions are final.
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants : decision[p] = commit => \A q \in participants : prevote[q] = yes

AbortValidity ==
    \A p \in participants : decision[p] = abort => (\/ \E q \in participants : prevote[q] = no
                                                    \/ \E q \in participants : faulty[q]
                                                    \/ faulty["coordinator"])

Irreversible ==
    \A p \in participants :
        /\ decision[p] = commit => \A k \in 0..3 : decision[p] = decision[p]
        /\ decision[p] = abort => \A k \in 0..3 : decision[p] = decision[p]

\* Liveness: every non-faulty participant eventually decides (the NB guarantee).
AllDecided == \A p \in participants : decision[p] # waiting

DecideAll == <>(AllDecided \/ \E p \in participants : faulty[p] \/ faulty["coordinator"])

SpecTerminating ==
    \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting)

====