---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: a participant stores a pre-decision in its own forwarding
\* table entry (cur) before forwarding it to every other, and finalizes only
\* once it has forwarded to all. This is what guarantees termination without a
\* coordinator, since a live participant can still learn the decision from a peer.

VARIABLES vote, alive, decision, faulty, sent, coord

vars == <<vote, alive, decision, faulty, sent, coord>>

\* sent[p][q] is what p has forwarded to q: notsent, commit, or abort.
Init && Voting == 0

TypeInv ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \subseteq participants
    /\ sent \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ coord \in [req |-> BOOLEAN, v -> {yes, no, undecided}, bc |-> BOOLEAN,
                  d |-> {commit, abort, waiting}, alive |-> BOOLEAN, faulty |-> BOOLEAN]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = {}
    /\ sent = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coord = [req |-> FALSE, v |-> undecided, bc |-> FALSE, d |-> waiting, alive |-> TRUE, faulty |-> FALSE]

SendReq ==
    /\ coord.alive
    /\ ~coord.faulty
    /\ coord.req = FALSE
    /\ coord' = [coord EXCEPT !.req = TRUE, !.v = undecided, !.bc = FALSE, !.d = waiting]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

GetVote(p) ==
    /\ coord.alive
    /\ coord.req
    /\ coord.v = undecided
    /\ alive[p]
    /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, sent, coord>>

CoordDetectFault(p) ==
    /\ coord.alive
    /\ alive[p]
    /\ vote[p] = undecided
    /\ coord.v # undecided
    /\ coord.v # vote[p]
    /\ coord' = [coord EXCEPT !.v = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

MakeDecision ==
    /\ coord.alive
    /\ coord.req
    /\ coord.v # undecided
    /\ coord.d = waiting
    /\ coord' = [coord EXCEPT !.d = IF coord.v = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

Broadcast ==
    /\ coord.alive
    /\ coord.d # waiting
    /\ coord.bc = FALSE
    /\ coord' = [coord EXCEPT !.bc = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

Die ==
    /\ coord.alive
    /\ coord' = [coord EXCEPT !.alive = FALSE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

CoordPreempt ==
    /\ coord.alive
    /\ coord.faulty
    /\ coord' = [coord EXCEPT !.alive = FALSE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

CoordFaulty ==
    /\ coord.alive
    /\ coord' = [coord EXCEPT !.faulty = TRUE]
    /\ UNCHANGED <<vote, alive decision, faulty, sent>>

VoteFaulty(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ coord.faulty
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<vote, decision, sent, coord>>

\* Pre-decision from the coordinator's broadcast.
PreDecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ sent[p][p] = notsent
    /\ coord.alive
    /\ coord.bc
    /\ coord.d # waiting
    /\ sent' = [sent EXCEPT ![p][p] = coord.d]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

\* Pre-decision from a peer's forwarding.
PreDecidePeer(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ sent[p][p] = notsent
    /\ \E r \in participants :
         /\ sent[r][p] # notsent
         /\ sent' = [sent EXCEPT ![p][p] = sent[r][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

Forward(p, q) ==
    /\ alive[p]
    /\ sent[p][p] # notsent
    /\ sent[p][q] = notsent
    /\ sent' = [sent EXCEPT ![p][q] = sent[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

DecideNB(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ sent[p][p] # notsent
    /\ \A q \in participants : sent[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = sent[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

\* Abort on timeout when the coordinator is dead and no live source remains.
AbortNow(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ coord.alive = FALSE
    /\ (\A q \in participants : sent[q][p] = notsent \/ q \in faulty)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

Next ==
    \/ SendReq \/ MakeDecision \/ Broadcast \/ Die \/ CoordPreempt \/ CoordFaulty
    \/ \E p \in participants :
         \/ GetVote(p) \/ CoordDetectFault(p) \/ VoteFaulty(p) \/ PreDecideCoord(p)
         \/ PreDecidePeer(p) \/ DecideNB(p) \/ AbortNow(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : MakeDecision)
    /\ WF_vars(\E p \in participants : Broadcast)
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : DecideNB(p))
    /\ WF_vars(\E p \in participants : AbortNow(p))

\* AC1: two participants cannot disagree on commit/abort.
Agreement ==
    \A p, q \in participants :
        ~(decision[p] = commit /\ decision[q] = abort)

CommitValid ==
    (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AbortValid ==
    (\E p \in participants : decision[p] = abort) =>
        (\E q \in participants : vote[q] = no) \/ faulty # {} \/ coord.faulty

Irreversible ==
    \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

EventualDecision ==
    \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] # waiting)

SpecProperties == Agreement /\ CommitValid /\ AbortValid /\ Irreversible /\ EventualDecision

====