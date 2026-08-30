---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Non-blocking atomic commitment with reliable broadcast: a participant
\* forwards the coordinator's decision to all others before finalizing
\* locally, guaranteeing termination even if the coordinator crashes.
\* Every participant carries a forwarding table: the decision it received
\* (at its own index) and what it has forwarded to each other participant.
VARIABLES pstate, alive, decision, faulty, votesent, coordState, fwd

TypeInv == /\ pstate \in [participants -> {yes, no, undecided}]
           /\ alive \in [participants -> BOOLEAN]
           /\ decision \in [participants -> {waiting, commit, abort}]
           /\ faulty \in [participants -> BOOLEAN]
           /\ votesent \in [participants -> BOOLEAN]
           /\ coordState \in {waiting, voted, broadcast, decided, crashed}
           /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init == /\ pstate = [p \in participants |-> undecided]
        /\ alive = [p \in participants |-> TRUE]
        /\ decision = [p \in participants |-> waiting]
        /\ faulty = [p \in participants |-> FALSE]
        /\ votesent = [p \in participants |-> FALSE]
        /\ coordState = waiting
        /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendVote(p) == /\ alive[p]
               /\ ~votesent[p]
               /\ pstate[p] = undecided
               /\ \E v \in {yes, no} : pstate' = [pstate EXCEPT ![p] = v]
               /\ votesent' = [votesent EXCEPT ![p] = TRUE]
               /\ UNCHANGED <<alive, decision, faulty, coordState, fwd>>

CoordDecideCommit == /\ coordState = voted
                     /\ \A p \in participants : pstate[p] = yes
                     /\ coordState' = decided
                     /\ decision' = [p \in participants |-> commit]
                     /\ UNCHANGED <<pstate, alive, faulty, votesent, fwd>>

CoordDecideAbort == /\ coordState = voted
                    /\ \E p \in participants : pstate[p] = no
                    /\ coordState' = decided
                    /\ decision' = [p \in participants |-> abort]
                    /\ UNCHANGED <<pstate, alive, faulty, votesent, fwd>>

CoordBroadcast == /\ coordState = decided
                  /\ coordState' = broadcast
                  /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, fwd>>

SendRequest == /\ coordState = waiting
               /\ coordState' = voted
               /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, fwd>>

\* Coordinator crashes silently during broadcast.
CoordDie == /\ coordState \in {voted, broadcast}
            /\ coordState' = crashed
            /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, fwd>>

\* A participant receives the coordinator's decision (first hop).
PreDecideCoord(p) == /\ alive[p]
                     /\ decision[p] = waiting
                     /\ coordState = broadcast
                     /\ fwd[p][p] = notsent
                     /\ fwd' = [fwd EXCEPT ![p][p] = decision[p]]
                     /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, coordState>>

\* A participant receives a forwarded decision from another participant.
PreDecideFwd(p) == /\ alive[p]
                    /\ decision[p] = waiting
                    /\ \E q \in participants :
                         /\ q # p
                         /\ fwd[q][p] # notsent
                         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
                    /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, coordState>>

Forward(p, q) == /\ alive[p]
                  /\ decision[p] # waiting
                  /\ alive[q]
                  /\ fwd[p][q] = notsent
                  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
                  /\ UNCHANGED <<pstate, alive, decision, faulty, votesent, coordState>>

Decide(p) == /\ alive[p]
             /\ decision[p] # waiting
             /\ \A q \in participants : q # p => fwd[p][q] = decision[p]
             /\ decision' = [decision EXCEPT ![p] = decision[p]]
             /\ UNCHANGED <<pstate, alive, faulty, votesent, coordState, fwd>>

AbortTimeout == /\ coordState = crashed
                /\ \A q \in participants : alive[q] => decision[q] = waiting
                /\ \A q \in participants : ~alive[q] =>
                                      \A r \in participants : fwd[q][r] = notsent
                /\ decision' = [p \in participants |-> abort]
                /\ UNCHANGED <<pstate, alive, faulty, votesent, coordState, fwd>>

Die(p) == /\ alive[p]
           /\ alive' = [alive EXCEPT ![p] = FALSE]
           /\ faulty' = [faulty EXCEPT ![p] = TRUE]
           /\ UNCHANGED <<pstate, decision, votesent, coordState, fwd>>

Next == \/ SendRequest \/ CoordDecideCommit \/ CoordDecideAbort \/ CoordBroadcast
        \/ CoordDie \/ AbortTimeout
        \/ \E p \in participants :
             \/ SendVote(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ Die(p)
             \/ \E q \in participants : Forward(p, q)

SpecNB == /\ Init /\ [][Next]_<<pstate, alive, decision, faulty, votesent, coordState, fwd>>
          /\ TRUE

\* Safety: agreement, commit/abort validity, and irrevocability.
\* Liveness: every non-faulty participant eventually decides.
TypeInvNB == TypeInv
Agreement == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
CommitValid == (\E p \in participants : decision[p] = commit) => \A q \in participants : pstate[q] = yes
AbortValid == (\E p \in participants : decision[p] = abort) =>
                 (\E q \in participants : pstate[q] = no) \/ (\E p \in participants : faulty[p]) \/ (coordState \in {crashed, decided})
Irreversible == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)
DecideEventually == \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] = commit \/ decision[p] = abort)

Properties == Agreement /\ CommitValid /\ AbortValid /\ Irreversible /\ DecideEventually

====