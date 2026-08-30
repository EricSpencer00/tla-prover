---- MODULE ACP_NB ----
EXTENDS Integers, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, cstate, voteRecv, broadcast

vars == <<vote, alive, decision, faulty, sentVote, cstate, voteRecv, broadcast>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \subseteq participants
    /\ sentVote \subseteq participants
    /\ cstate \in {waiting, vote, broadcast, decided}
    /\ voteRecv \in [participants -> {yes, no, undecided}]
    /\ broadcast \in [participants -> {yes, no, notsent}]

\* A single coordinator drives the first phase; every participant also implements
\* a reliable broadcast that forwards what it heard before finalizing locally,
\* so that a crash of the coordinator mid-broadcast cannot strand an undecided
\* participant forever.
Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ sentVote = {}
    /\ cstate = waiting
    /\ voteRecv = [p \in participants |-> undecided]
    /\ broadcast = [p \in participants |-> notsent]

SendRequest ==
    /\ cstate = waiting
    /\ cstate' = vote
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, voteRecv, broadcast>>

SendVote(p) ==
    /\ cstate = vote
    /\ p \in participants
    /\ alive[p]
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, cstate, voteRecv, broadcast>>

\* The coordinator splits on unanimity versus a single no vote.
DecideCoord ==
    /\ cstate = vote
    /\ \A p \in participants : vote[p] # undecided
    /\ broadcast' = [p \in participants |-> vote[p]]
    /\ cstate' = broadcast
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, voteRecv>>

CrashCoord ==
    /\ cstate \in {vote, broadcast}
    /\ cstate' = decided
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, voteRecv, broadcast>>

\* A participant receives the coordinator's broadcast and records the
\* pre-decision in its own forwarding table.
PreDecideFromCoord(p) ==
    /\ alive[p]
    /\ broadcast[p] # notsent
    /\ voteRecv[p] = undecided
    /\ voteRecv' = [voteRecv EXCEPT ![p] = broadcast[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cstate, broadcast>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFromPeer(p) ==
    /\ alive[p]
    /\ voteRecv[p] = undecided
    /\ \E q \in participants :
         /\ alive[q]
         /\ broadcast[q] # notsent
         /\ voteRecv[p] = notsent
         /\ voteRecv' = [voteRecv EXCEPT ![p] = broadcast[q]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cstate, broadcast>>

Forward(p, q) ==
    /\ alive[p]
    /\ alive[q]
    /\ p # q
    /\ broadcast[p] # notsent
    /\ broadcast[q] = notsent
    /\ broadcast' = [broadcast EXCEPT ![q] = broadcast[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cstate, voteRecv>>

Decide(p) ==
    /\ alive[p]
    /\ voteRecv[p] # undecided
    /\ \A q \in participants : broadcast[q] \in {voteRecv[p], notsent}
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = IF voteRecv[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, cstate, voteRecv, broadcast>>

\* With the coordinator silent and no undecided recipient left anywhere, an
\* undecided participant must abort rather than waiting forever.
AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ cstate = decided
    /\ \A q \in participants : broadcast[q] # notsent
    /\ \A q \in participants : (q \in faulty) => (alive[p] => broadcast[q] = notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, cstate, voteRecv, broadcast>>

Die(p) ==
    /\ alive[p]
    /\ p \notin faulty
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<vote, decision, sentVote, cstate, voteRecv, broadcast>>

Next ==
    \/ SendRequest \/ DecideCoord \/ CrashCoord
    \/ \E p \in participants :
         \/ SendVote(p) \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
         \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(SendRequest)
    /\ WF_vars(DecideCoord)
    /\ WF_vars(CrashCoord)
    /\ \A p \in participants :
         /\ WF_vars(SendVote(p))
         /\ WF_vars(PreDecideFromCoord(p))
         /\ WF_vars(PreDecideFromPeer(p))
         /\ WF_vars(Decide(p))
         /\ WF_vars(AbortOnTimeout(p))

\* Safety: two participants can never be driven to opposite decisions.
Agreement ==
    \A p \in participants : \A q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

DecideComplete == \A p \in participants : decision[p] # undecided

\* Liveness: the reliable broadcast that every participant performs guarantees
\* the non-blocking property -- every non-faulty participant reaches a decision.
NonBlocking == \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

====