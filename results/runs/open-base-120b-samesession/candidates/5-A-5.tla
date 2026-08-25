---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision,
          reqSent, voteReceived, broadcastSent,
          alive, faulty, vote, sentVote, decision

(*-------------------------------------------------------------------*)
(* Type Invariant *)
TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ reqSent \in [participants -> BOOLEAN]
  /\ voteReceived \in [participants -> {yes, no, waiting}]
  /\ broadcastSent \in [participants -> {commit, abort, notsent}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ vote \in [participants -> {yes, no}]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]

(*-------------------------------------------------------------------*)
(* Initial state *)
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ reqSent = [p \in participants |-> FALSE]
  /\ voteReceived = [p \in participants |-> waiting]
  /\ broadcastSent = [p \in participants |-> notsent]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ vote \in [participants -> {yes, no}]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ decision = [p \in participants |-> undecided]

(*-------------------------------------------------------------------*)
(* Coordinator actions *)

SendRequest(p) ==
  /\ coordAlive
  /\ ~ reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote, decision >>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ voteReceived[p] = waiting
  /\ sentVote[p] = TRUE
  /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, broadcastSent,
                 alive, faulty, vote, sentVote, decision >>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ voteReceived[p] = waiting
  /\ alive[p] = FALSE
  /\ faulty[p] = TRUE
  /\ coordDecision' = abort
  /\ UNCHANGED << coordAlive, coordFaulty, reqSent,
                 voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote, decision >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: voteReceived[p] \in {yes, no}
  /\ \/ ( \A p \in participants: voteReceived[p] = yes
        /\ coordDecision' = commit )
     \/ ( \E p \in participants: voteReceived[p] = no
        /\ coordDecision' = abort )
  /\ UNCHANGED << coordAlive, coordFaulty, reqSent,
                 voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote, decision >>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived,
                 alive, faulty, vote, sentVote, decision >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << coordDecision, reqSent, voteReceived,
                 broadcastSent, alive, faulty, vote, sentVote, decision >>

(*-------------------------------------------------------------------*)
(* Participant actions *)

SendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ ~ sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived, broadcastSent,
                 alive, faulty, vote, decision >>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote >>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ reqSent[p] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote >>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcastSent[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived, broadcastSent,
                 alive, faulty, vote, sentVote >>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                 reqSent, voteReceived, broadcastSent,
                 vote, sentVote, decision >>

(*-------------------------------------------------------------------*)
(* Progress actions for fairness *)

CoordProgress ==
  ( \E p \in participants:
        SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) )
  \/ MakeDecision

ParticipantProgress(p) ==
  SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p)

(*-------------------------------------------------------------------*)
(* Next-state relation *)

Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideOnBroadcast(p)
  \/ \E p \in participants: ParticipantDie(p)

(*-------------------------------------------------------------------*)
(* Specification *)

vars == << coordAlive, coordFaulty, coordDecision,
          reqSent, voteReceived, broadcastSent,
          alive, faulty, vote, sentVote, decision >>

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ \A p \in participants: WF_vars(ParticipantProgress(p))

====