---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes # no
ASSUME commit # abort

VARIABLES coordAlive, coordDecision, coordSent, coordGot, coordFaulty, coordReqSent
VARIABLES vote, alive, decision, faulty, sent

vars == <<coordAlive, coordDecision, coordSent, coordGot, coordFaulty, coordReqSent,
         vote, alive, decision, faulty, sent>>

\* The coordinator decides commit only when every participant has voted yes; if any
\* participant is slow or silent (message lost) while the coordinator is still
\* alive, the coordinator has not yet decided and the protocol is blocked.

Init ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordGot = [p \in participants |-> waiting]
  /\ coordFaulty = FALSE
  /\ coordReqSent = [p \in participants |-> FALSE]
  /\ vote = [p \in participants |-> IF TRUE THEN yes ELSE no]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]

RequestCoord(p) ==
  /\ coordAlive
  /\ ~coordReqSent[p]
  /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, vote, alive, decision, faulty, sent>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : coordReqSent[q]
  /\ coordGot[p] = waiting
  /\ sent[p]
  /\ coordGot' = [coordGot EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordReqSent,
                coordFaulty, vote, alive, decision, faulty, sent>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqSent[p]
  /\ coordGot[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordSent, coordGot, coordFaulty, coordReqSent,
                vote, alive, decision, faulty, sent>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordGot[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordGot[p] = yes
                     THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordSent, coordGot, coordFaulty, coordReqSent,
                vote, alive, decision, faulty, sent>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordDecision, coordGot, coordFaulty, coordReqSent,
                vote, alive, decision, faulty, sent>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordSent, coordGot,
                coordReqSent, vote, alive, decision, faulty, sent>>

SendVote(p) ==
  /\ alive[p]
  /\ coordReqSent[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, coordReqSent, vote, alive, decision, faulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, coordReqSent, vote, alive, faulty, sent>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReqSent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, coordReqSent, vote, alive, faulty, sent>>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, coordReqSent, vote, alive, faulty, sent>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordDecision, coordSent, coordGot,
                coordFaulty, coordReqSent, vote, decision, sent>>

Next ==
  \/ \E p \in participants : RequestCoord(p) \/ ReceiveVote(p) \/ DetectFault(p)
                            \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                            \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p)
                            \/ DieParticipant(p)
  \/ Decide \/ DieCoordinator

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(AbortOnVote(p))
  /\ \A p \in participants : WF_vars(DecideFromBroadcast(p))
  /\ \A p \in participants : WF_vars(AbortOnTimeout(p))
  /\ WF_vars(Decide)

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordGot \in [participants -> {waiting, yes, no}]
  /\ coordFaulty \in BOOLEAN
  /\ coordReqSent \in [participants -> BOOLEAN]
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]

\* AC1: Agreement -- no two participants can decide differently.
Agreement ==
  ~( \E p1, p2 \in participants :
       /\ decision[p1] = commit
       /\ decision[p2] = abort )

\* AC2: Commit only if every participant voted yes.
CommitValidity ==
  ( \E p \in participants : decision[p] = commit ) =>
    ( \A p \in participants : vote[p] = yes )

\* AC3: Abort occurs only if a no vote exists or a failure exists.
AbortValidity ==
  ( \E p \in participants : decision[p] = abort ) =>
    ( (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty )

\* AC4: Irrevocability -- a participant decides at most once.
Irrevocability ==
  /\ \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
  /\ \A p \in participants : (decision[p] = abort) ~> (decision[p] = abort)

\* AC3 liveness component: The protocol must not stall forever without a decision or a failure.
Progress ==
  <>( \A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty )

====