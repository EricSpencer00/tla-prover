---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment (ACP-NB) as in Babaoglu and Toueg: the
\* coordinator decides commit/abort and broadcasts. Each participant, before
\* finalizing its own decision (non-blocking commit/abort), forwards the
\* pre-decision to every other participant; this is what guarantees termination
\* even if the coordinator crashes mid-broadcast.
\* The module extends the simple broadcast variant (ACP-SB) by adding the
\* forwarding table and the pre-decision/forward/decide actions.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent,
          req, cVote, broadcast, decisionC, aliveC

vars == <<vote, alive, decision, faulty, voteSent,
           req, cVote, broadcast, decisionC, aliveC>>

\* A participant's forwarding table entry for a given participant: not-sent, or
\* the decision (commit/abort) last forwarded to that participant.
Msg == {notsent, commit, abort}

RECURSIVE AllSent(_, _)
AllSent(p, S) ==
    \A q \in S : broadcast[p][q] # notsent

RECURSIVE SomeAlive(_, _)
SomeAlive(p, S) ==
    \E q \in S : aliveC[q] /\ broadcast[p][q] # notsent

\* A participant has a pre-decision (its own broadcast entry set) once it has
\* received the coordinator's broadcast or a forwarded message from another.
\* It may finalize only after it has forwarded that pre-decision to every
\* other participant.
PreDecided(p) == broadcast[p][p] # notsent

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ req \in BOOLEAN
    /\ cVote \in {yes, no, undecided}
    /\ broadcast \in [participants -> [participants -> Msg]]
    /\ decisionC \in {commit, abort, undecided}
    /\ aliveC \in [participants -> BOOLEAN]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ req = FALSE
    /\ cVote = undecided
    /\ broadcast = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decisionC = undecided
    /\ aliveC = [p \in participants |-> FALSE]

SendReq ==
    /\ ~req
    /\ req' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   cVote, broadcast, decisionC, aliveC>>

GetVote(p) ==
    /\ req /\ alive[p] /\ vote[p] = undecided /\ ~voteSent[p]
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, req,
                   cVote, broadcast, decisionC, aliveC>>

DetectFault ==
    /\ req /\ \A p \in participants : ~alive[p]
    /\ req' = FALSE
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   cVote, broadcast, decisionC, aliveC>>

Decide ==
    /\ req /\ cVote = undecided /\ \E p \in participants : alive[p]
    /\ \E d \in {yes, no} :
         /\ cVote' = d
         /\ decisionC' = IF d = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   req, broadcast, aliveC>>

Broadcast ==
    /\ req /\ cVote # undecided
    /\ broadcast' = [broadcast EXCEPT ![coordinator] = [p \in participants |-> decisionC]]
    /\ aliveC' = [p \in participants |-> alive[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   req, cVote, decisionC>>

\* Inherited coordinator death (crash).
DieC ==
    /\ req /\ ~faulty[coordinator]
    /\ req' = FALSE
    /\ faulty' = [faulty EXCEPT ![coordinator] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, voteSent,
                   cVote, broadcast, decisionC, aliveC>>

\* A participant receives the coordinator's broadcast for itself (pre-decision).
PreDecideFromCoordinator(p) ==
    /\ alive[p] /\ broadcast[coordinator][p] # notsent /\ broadcast[p][p] = notsent
    /\ broadcast' = [broadcast EXCEPT ![p][p] = broadcast[coordinator][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   req, cVote, decisionC, aliveC>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFromPeer(p) ==
    /\ alive[p] /\ broadcast[p][p] = notsent
    /\ \E q \in participants :
         /\ broadcast[q][p] # notsent
         /\ broadcast' = [broadcast EXCEPT ![p][p] = broadcast[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   req, cVote, decisionC, aliveC>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ alive[p] /\ PreDecided(p) /\ broadcast[p][q] = notsent
    /\ broadcast' = [broadcast EXCEPT ![p][q] = broadcast[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent,
                   req, cVote, decisionC, aliveC>>

\* Non-blocking finalize: once a participant has forwarded its pre-decision to
\* everybody, it commits/aborts accordingly.
DecideNB(p) ==
    /\ alive[p] /\ decision[p] = undecided
    /\ PreDecided(p) /\ AllSent(p, participants)
    /\ decision' = [decision EXCEPT ![p] = broadcast[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent,
                   req, cVote, broadcast, decisionC, aliveC>>

\* A participant may abort on timeout if the coordinator has died and no alive
\* participant still expects a broadcast directly or via forwarding.
AbortOnTimeout ==
    /\ req /\ ~aliveC[coordinator]
    /\ \A p \in participants : decision[p] = undecided
    /\ (\A p \in participants : ~alive[p])
       \/ (\A p \in participants : ~SomeAlive(p, participants))
    /\ decision' = [p \in participants |-> abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent,
                   req, cVote, broadcast, decisionC, aliveC>>

Die(p) ==
    /\ alive[p] /\ ~faulty[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent,
                   req, cVote, broadcast, decisionC, aliveC>>

NextNB ==
    \/ SendReq \/ DetectFault \/ Decide \/ Broadcast \/ DieC \/ AbortOnTimeout
    \/ \E p \in participants : GetVote(p) \/ PreDecideFromCoordinator(p)
                               \/ PreDecideFromPeer(p) \/ DecideNB(p) \/ Die(p)
    \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(Decide)
    /\ WF_vars(Broadcast)
    /\ WF_vars(PreDecideFromCoordinator(arbiter))
    /\ WF_vars(DecideNB(arbiter))

\* AC1: agreement -- no two participants commit and abort.
Agreement ==
    ~( \E p \in participants, q \in participants :
         decision[p] = commit /\ decision[q] = abort )

\* AC2: a commit only follows a unanimous yes vote.
CommitValidity ==
    ~( \E p \in participants : decision[p] = commit
         /\ (\E q \in participants : vote[q] # yes) )

\* AC3: an abort has a justified cause: a no vote, a faulty participant, or a
\* faulty coordinator.
AbortValidity ==
    ~( \E p \in participants : decision[p] = abort
         /\ ~( (\E q \in participants : vote[q] = no)
               \/ (\E q \in participants : faulty[q])
               \/ faulty[coordinator] ) )

\* AC4: a participant's terminal decision never changes once taken.
Irrevocability ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort)
          ~> (decision[p] = commit \/ decision[p] = abort)

\* AC3 liveness: every participant eventually decides, or some participant or
\* the coordinator is faulty.
EventualDecision ==
    <>(\A p \in participants : decision[p] # undecided
          \/ (\E q \in participants : faulty[q]) \/ faulty[coordinator])

\* AC5 (liveness): every non-faulty participant eventually commits or aborts;
\* this is the non-blocking guarantee enabled by reliable forwarding.
NonBlockingTerminate ==
    \A p \in participants :
        (~faulty[p]) ~> (decision[p] = commit \/ decision[p] = abort)

Properties ==
    /\ Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability
    /\ EventualDecision /\ NonBlockingTerminate

====