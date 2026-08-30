---------------------------- MODULE ACP_NB ----------------------------
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  pc,         \* coordinator phase: idle | collecting | decided
  vote,       \* [participants -> {yes, no, undecided}]: each vote
  alive,      \* [participants -> BOOLEAN]: true while a participant is alive
  decision,   \* [participants -> {commit, abort, undecided}]: each decision
  faulty,     \* set of participants/crashed coordinator
  sent,       \* [participants -> BOOLEAN]: vote already sent to coordinator
  pstate,     \* coordinator's own vote/broadcast/decision/alive/faulty record
  fwd         \* [participants -> [participants -> {notsent, commit, abort}]]:
              \* participant forwarding table

vars == <<pc, vote, alive, decision, faulty, sent, pstate, fwd>>

TypeOK ==
  /\ pc \in {"idle", "collecting", "decided"}
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \subseteq participants
  /\ sent \in [participants -> BOOLEAN]
  /\ pstate \in [req : BOOLEAN, vote : {yes, no}, bc : {commit, abort, undecided},
                 dec : {commit, abort, undecided}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pc = "idle"
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sent = [p \in participants |-> FALSE]
  /\ pstate = [req |-> FALSE, vote |-> undecided, bc |-> undecided,
               dec |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator: request participants to vote.
Ask ==
  /\ pc = "idle"
  /\ pstate' = [pstate EXCEPT !.req = TRUE]
  /\ pc' = "collecting"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

\* Participant: send a yes/no vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ pstate.req
  /\ vote[p] = undecided
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, pstate, fwd>>

\* Coordinator: collect a vote it has not yet recorded.
CollectVote(p) ==
  /\ alive[p]
  /\ sent[p]
  /\ pstate.vote = undecided
  /\ pstate' = [pstate EXCEPT !.vote = vote[p]]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, fwd>>

\* Coordinator: a participant crashes silently during collection; the coordinator
\* detects it and annotations the detection.
DetectFault(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ pstate' = [pstate EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<pc, vote, decision, sent, fwd>>

\* Coordinator: make a commit or abort decision once a vote is recorded.
Decide ==
  /\ pc = "collecting"
  /\ pstate.vote # undecided
  /\ pc' = "decided"
  /\ pstate' = [pstate EXCEPT !.bc = IF pstate.vote = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

\* Coordinator: broadcast its decision to a participant.
Broadcast(p) ==
  /\ pc = "decided"
  /\ pstate.bc # undecided
  /\ pstate' = [pstate EXCEPT !.dec = pstate.bc]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, fwd>>

\* Coordinator crashes silently.
CoordDie ==
  /\ pstate.alive
  /\ pstate' = [pstate EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ pstate' = [pstate EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, fwd>>

\* Participant: on receiving the coordinator broadcast first, store the
\* pre-decision in its own forwarding entry.
PreDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pstate.dec # undecided
  /\ fwd' = [fwd EXCEPT ![p][p] = pstate.dec]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, pstate>>

\* Participant: on receiving a forwarded pre-decision first, store it.
FwdPreDecide(p) ==
  \E q \in participants :
    /\ q # p
    /\ alive[p]
    /\ decision[p] = undecided
    /\ fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, pstate>>

\* Participant: once it has a pre-decision, forward it to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pc, vote, alive, decision, faulty, sent, pstate>>

\* Participant: once it has forwarded its pre-decision to everyone else, finalize
\* its own decision (non-blocking, never waits on the coordinator).
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pc, vote, alive, faulty, sent, pstate, fwd>>

\* Participant: abort by timeout once the coordinator is silent and no forwarding
\* can help.
AbortTimeout ==
  /\ \A p \in participants : ~alive[p]
  /\ \A p \in participants : decision[p] = undecided
  /\ \A p \in participants : \A q \in participants : fwd[p][q] = notsent
  /\ decision' = [p \in participants |-> abort]
  /\ UNCHANGED <<pc, vote, alive, faulty, sent, pstate, fwd>>

\* Participant silently crashes.
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<pc, vote, decision, sent, pstate, fwd>>

Next ==
  \/ Ask \/ Decide \/ CoordDie \/ AbortTimeout
  \/ \E p \in participants :
       SendVote(p) \/ CollectVote(p) \/ DetectFault(p) \/ Broadcast(p)
         \/ PreDecide(p) \/ FwdPreDecide(p) \/ Decide(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Decide)

\* Safety: no two participants ever reach different decisions.
Agreement ==
  \A p, q \in participants :
    (decision[p] # undecided /\ decision[q] # undecided) => decision[p] = decision[q]

\* Safety: a commit requires everyone to have voted yes.
CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Safety: an abort requires at least one no vote, or a faulty participant, or a
\* faulty coordinator.
AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ faulty # {}
      \/ pstate.faulty

\* Safety: once decided, a decision never flips.
Irreversibility ==
  \A p \in participants :
    decision[p] # undecided => [p \in faulty => decision[p] = abort]

\* Liveness: every non-faulty participant eventually decides.
EventualDecision ==
  \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

\* Liveness: either everyone decides, or some participant is faulty, or the
\* coordinator is faulty.
EventualResolution ==
  ( \A p \in participants : decision[p] # undecided )
    \/ (faulty # {})
    \/ pstate.faulty

\* The model checking configuration (in the enclosing .cfg file) must name the
\* following exactly: CONSTANTS participants, yes, no, undecided, commit, abort,
\* waiting, notsent; SPECIFICATION SpecNB; INVARIANTS TypeInvNB.
TypeInvNB == TypeOK
===========================================================================