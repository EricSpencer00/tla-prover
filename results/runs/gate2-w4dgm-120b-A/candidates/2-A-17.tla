---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: what pre-decision a participant has received, and
\* which other participants it has already forwarded that pre-decision to.
Forwarding == [participants -> {notsent, commit, abort}]

VARIABLES vote, alive, decision, faulty, sent, coord

vars == <<vote, alive, decision, faulty, sent, coord>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {waiting, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> Forwarding]
    /\ coord \in [req |-> BOOLEAN, vote |-> {yes, no, undecided},
                  bc |-> {yes, no, undecided}, dec |-> {commit, abort},
                  alive |-> BOOLEAN, faulty |-> BOOLEAN]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coord = [req |-> FALSE, vote |-> undecided, bc |-> undecided,
                dec |-> commit, alive |-> TRUE, faulty |-> FALSE]

\* Coordinator gathers all live votes before preparing a decision.
SendReq ==
    /\ coord.alive /\ ~coord.faulty /\ ~coord.req
    /\ \E v \in {yes, no} : coord.vote' = v
    /\ coord' = [coord EXCEPT !.req = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

\* Vote travels to the coordinator; no ordering between participants and the
\* coordinator is assumed.
GetVote(p) ==
    /\ coord.alive /\ ~coord.faulty /\ coord.req
    /\ alive[p] /\ vote[p] = undecided
    /\ coord.vote' = vote[p]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

DetectFault ==
    /\ coord.alive /\ ~coord.faulty /\ coord.req
    /\ coord.vote # undecided
    /\ coord.vote # coord.bc
    /\ coord.bc' = coord.vote
    /\ coord.faulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

\* Coordinator makes the call once it has a consistent view (it may have missed
\* some votes), and starts broadcasting to all participants.
MakeDecision ==
    /\ coord.alive /\ ~coord.faulty /\ coord.req /\ coord.bc # undecided
    /\ coord.dec' = IF coord.bc = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coord>>

Broadcast(p) ==
    /\ coord.alive /\ coord.dec # commit
    /\ sent[p][p] = notsent
    /\ sent' = [sent EXCEPT ![p][p] = coord.dec]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

Die ==
    /\ coord.alive
    /\ coord' = [coord EXCEPT !.alive = FALSE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent>>

\* A participant votes yes or no once; it never changes its vote.
SendVote(p) ==
    /\ alive[p] /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, sent, coord>>

AbortOnVote(p) ==
    /\ alive[p] /\ decision[p] = waiting /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

AbortOnTimeoutReq(p) ==
    /\ alive[p] /\ decision[p] = waiting /\ coord.req /\ coord.faulty
    /\ sent[p][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

\* New: receive the coordinator's pre-decision directly via broadcast.
PreDecideFromCoord(p) ==
    /\ alive[p] /\ decision[p] = waiting
    /\ sent[p][p] # notsent
    /\ sent' = [sent EXCEPT ![p][p] = sent[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

\* New: receive a forwarded pre-decision from any other participant.
PreDecideFromPeer(p) ==
    /\ alive[p] /\ decision[p] = waiting
    /\ \E q \in participants :
         /\ q # p /\ sent[q][p] # notsent
         /\ sent[p][p] = notsent
         /\ sent' = [sent EXCEPT ![p][p] = sent[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

\* New: forward own pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p] /\ alive[q] /\ p # q
    /\ sent[p][p] # notsent /\ sent[p][q] = notsent
    /\ sent' = [sent EXCEPT ![p][q] = sent[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, coord>>

\* New: finalize only once every other participant has been forwarded to.
Decide(p) ==
    /\ alive[p] /\ decision[p] = waiting
    /\ sent[p][p] # notsent
    /\ \A q \in participants : sent[p][q] = sent[p][p]
    /\ decision' = [decision EXCEPT ![p] = sent[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

AbortOnTimeoutBoom(p) ==
    /\ alive[p] /\ decision[p] = waiting
    /\ coord.faulty /\ coord.bc = notsent
    /\ \A q \in participants : ~alive[q] \/ sent[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coord>>

DieP(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, coord>>

Next ==
    \/ SendReq \/ DetectFault \/ MakeDecision \/ Die
    \/ \E p \in participants : GetVote(p) \/ SendVote(p)
    \/ \E p \in participants : AbortOnVote(p) \/ AbortOnTimeoutReq(p)
    \/ \E p \in participants : Broadcast(p) \/ DieP(p)
    \/ \E p \in participants : PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p) \/ AbortOnTimeoutBoom(p)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Decide(one))
    /\ SF_vars(PreDecideFromCoord(one))
    /\ SF_vars(PreDecideFromPeer(one))
    /\ WF_vars(Forward(one, two))
    /\ SF_vars(SendReq)
    /\ WF_vars(DetectFault)

\* No two participants ever disagree about the outcome of the transaction.
AC1 == \A p \in participants, q \in participants : (decision[p] = commit) => (decision[q] = commit)

AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 == (\E p \in participants : decision[p] = abort) =>
         (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coord.faulty

Decided == {p \in participants : decision[p] # waiting}

\* Termination: either everyone decides, or some participant/coord crashes.
AC3Live == <> (Decided = participants \/ (\E p \in participants : faulty[p]) \/ coord.faulty)

\* Every non-faulty participant eventually reaches its decision.
AC5 == \A p \in participants : ~faulty[p] ~> (decision[p] # waiting)

AC4 == \A p \in participants : (decision[p] # waiting) ~> (decision[p] = decision[p])

====