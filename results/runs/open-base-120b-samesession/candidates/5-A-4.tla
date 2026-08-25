---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
          vote, alive, sentVote, decision

(* ---------------------------------------------------------------------- *)
(* Type invariant *)

TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ Req \in [participants -> BOOLEAN]
    /\ VoteReceived \in [participants -> {yes, no, waiting}]
    /\ BroadcastSent \in [participants -> {commit, abort, notsent}]
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ Req = [p \in participants |-> FALSE]
    /\ VoteReceived = [p \in participants |-> waiting]
    /\ BroadcastSent = [p \in participants |-> notsent]
    /\ \A p \in participants:
          /\ vote[p] \in {yes, no}
          /\ alive[p] = TRUE
          /\ sentVote[p] = FALSE
          /\ decision[p] = undecided

(* ---------------------------------------------------------------------- *)
(* Coordinator actions *)

SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~Req[p]
    /\ Req' = [Req EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, VoteReceived, BroadcastSent,
                  vote, alive, sentVote, decision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ Req[p]
    /\ VoteReceived[p] = waiting
    /\ sentVote[p]
    /\ VoteReceived' = [VoteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, BroadcastSent,
                  vote, alive, sentVote, decision>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ Req[p]
    /\ VoteReceived[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, Req, VoteReceived, BroadcastSent,
                  vote, alive, sentVote, decision>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: VoteReceived[p] # waiting
    /\ IF \A p \in participants: VoteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, Req, VoteReceived, BroadcastSent,
                  vote, alive, sentVote, decision>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ BroadcastSent[p] = notsent
    /\ BroadcastSent' = [BroadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived,
                  vote, alive, sentVote, decision>>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, Req, VoteReceived, BroadcastSent,
                  vote, alive, sentVote, decision>>

(* ---------------------------------------------------------------------- *)
(* Participant actions *)

SendVote(p) ==
    /\ alive[p]
    /\ ~sentVote[p]
    /\ Req[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
                  vote, alive, decision>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
                  vote, alive, sentVote>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~Req[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
                  vote, alive, sentVote>>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ BroadcastSent[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = BroadcastSent[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived,
                  BroadcastSent, vote, alive, sentVote>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
                  vote, sentVote, decision>>

(* ---------------------------------------------------------------------- *)
(* Grouped actions for fairness *)

CoordinatorProgress ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)

ParticipantProgress ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordinatorDie

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init /\
    [][Next]_<<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
               vote, alive, sentVote, decision>> /\
    WF_<<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
          vote, alive, sentVote, decision>>(CoordinatorProgress) /\
    WF_<<coordAlive, coordDecision, Req, VoteReceived, BroadcastSent,
          vote, alive, sentVote, decision>>(ParticipantProgress)

====