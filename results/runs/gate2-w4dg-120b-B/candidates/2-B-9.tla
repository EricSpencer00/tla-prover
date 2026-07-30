---- MODULE W4DG120b2m2p1t1 ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS participants

\* Non-blocking ACP (ACP_NB) is expressed as an extension of ACP_SB: 
\* a participant first receives ("predecides") on a broadcasted decision, 
\* forwards it to the others, and only then actually decides. The addition
\* compared to ACP_SB is the per-participant "decision" record.

\* A message that has been delivered is never overwritten: every message in
\* the system has a single owner (the participant that actually sent it)
\* and no participant ever rewrites a message it has already received.

TypeInvCoordinator ==
  coordinator \in [
    vote : [ participants -> {"yes", "no", "waiting"}],
    healthy : BOOLEAN,
    alive : BOOLEAN,
    decision : {"undecided", "commit", "abort"},
    broadcast : [ participants -> {"notsent", "commit", "abort"}],
    request : [ participants -> BOOLEAN ]
  ]

TypeInvParticipant ==
  participant \in [
    vote : {"yes", "no"},
    alive : BOOLEAN,
    decision : {"undecided", "commit", "abort"},
    faulty : BOOLEAN,
    voteSent : BOOLEAN,
    forward : [ participants -> {"notsent", "commit", "abort"}]
  ]

TypeInv == TypeInvCoordinator /\ TypeInvParticipant

InitCoordinator ==
  [ vote |-> [p \in participants |-> "waiting"],
    healthy |-> TRUE,
    alive |-> TRUE,
    decision |-> "undecided",
    broadcast |-> [p \in participants |-> "notsent"],
    request |-> [p \in participants |-> FALSE]
  ]

InitParticipant ==
  [ vote |-> "yes",
    alive |-> TRUE,
    decision |-> "undecided",
    faulty |-> FALSE,
    voteSent |-> FALSE,
    forward |-> [p \in participants |-> "notsent"]
  ]

\* The broadcast wire is reliable: every broadcast message is delivered to
\* its target exactly once, and once delivered it is never overwritten.
\* A predecision is only sent to a target that has not yet received it.

\* A "predecide" from the coordinator, delivered to a participant's inbox.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = "notsent"
  /\ coordinator.broadcast[i] # "notsent"
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* A forwarded predecision, delivered to a participant's inbox.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = "notsent"
  /\ participant[j].forward[i] # "notsent"
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* The full inbox of participant i is forwarded to participant j.
\* The narrowest assignment possible is used here: the owner of the
\* message (the source participant) is the only one that may rewrite it,
\* and only for a target participant it has not yet reached.
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # "notsent"
  /\ participant[i].forward[j] = "notsent"
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* The final decision, taken after every predecision has been forwarded.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = participant[i].forward[i]]
  /\ UNCHANGED <<coordinator>>

\* A participant aborts on a timeout, if the coordinator has died and
\* nothing has reached it yet -- this is the only way a correct
\* participant is allowed to abort in this protocol.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ coordinator.broadcast[i] = "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED <<coordinator>>

Next == \E i \in participants, j \in participants : preDecide(i) \/ preDecideOnForward(i, j) \/ forward(i, j) \/ decideNB(i) \/ abortOnTimeout(i)

Spec == InitCoordinator /\ [][Next]_<<coordinator, participant>>

\* No message is ever silently overwritten: whenever an action rewrites a
\* delivered message, the target participant's inbox must have been empty.
NoLostUpdate == \A i \in participants : \A j \in participants : preDecide(i) \/ preDecideOnForward(i, j) \/ forward(i, j) ~> (participant[i].forward[j] # "notsent")
====