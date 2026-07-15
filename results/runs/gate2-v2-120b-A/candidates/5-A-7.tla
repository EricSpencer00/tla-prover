---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    participants, \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort, \* Decision values
    waiting, notsent   \* Message‑state markers

(*-----------------------------------------------------------------
  Types (for readability; not exposed as separate constants)
-----------------------------------------------------------------*)
Vote      == {yes, no}
Decision  == {undecided, commit, abort}
MsgState  == {waiting, notsent}
BoolOr   == BOOLEAN

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator has crashed
    coordDec,            \* Coordinator's decision (undecided/commit/abort)

    reqSent,             \* Set of participants to which a vote request has been sent
    votesReceived,       \* [p \in participants -> waiting \cup {yes,no}]
    broadcastSent,       \* [p \in participants -> notsent \cup {commit,abort}]

    partAlive,           \* [p \in participants -> BOOLEAN] (TRUE = alive)
    partFaulty,          \* [p \in participants -> BOOLEAN] (TRUE = crashed)
    partVote,            \* [p \in participants -> Vote]
    partDec,             \* [p \in participants -> Decision]
    partSentVote         \* [p \in participants -> BOOLEAN] (TRUE = vote already sent)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* A participant is "ready" to send its vote when it has received a request
ReadyToVote(p) == p \in reqSent

\* A participant decides commit only when it adopts the coordinator's broadcast
AdoptsCommit(p) == coordDec = commit /\ broadcastSent[p] = commit

\* A participant decides abort either by its own vote=no or by adopting abort broadcast
AdoptsAbort(p) == (partVote[p] = no /\ partSentVote[p]) \/ (coordDec = abort /\ broadcastSent[p] = abort)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDec = undecided
    /\ reqSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF Random() % 2 = 0 THEN yes ELSE no]
    /\ partDec = [p \in participants |-> undecided]
    /\ partSentVote = [p \in participants |-> FALSE]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \notin reqSent
    /\ reqSent' = reqSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    votesReceived, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partDec, partSentVote>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ p \in reqSent
    /\ votesReceived[p] = waiting
    /\ partAlive[p] = TRUE
    /\ partSentVote[p] = TRUE
    /\ votesReceived' = [votesReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partDec, partSentVote>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ p \in reqSent
    /\ (votesReceived[p] = waiting)
    /\ partAlive[p] = FALSE
    /\ coordDec' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty,
                    reqSent, votesReceived,
                    broadcastSent, partAlive, partFaulty,
                    partVote, partDec, partSentVote>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ reqSent = participants
    /\ \A p \in participants: votesReceived[p] # waiting
    /\ IF \A p \in participants: votesReceived[p] = yes
          THEN coordDec' = commit
          ELSE coordDec' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty,
                    reqSent, votesReceived,
                    broadcastSent, partAlive, partFaulty,
                    partVote, partDec, partSentVote>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDec]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived,
                    partAlive, partFaulty, partVote,
                    partDec, partSentVote>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDec, reqSent, votesReceived,
                    broadcastSent, partAlive, partFaulty,
                    partVote, partDec, partSentVote>>

PartSendVote(p) ==
    /\ partAlive[p]
    /\ ReadyToVote(p)
    /\ partSentVote[p] = FALSE
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partDec>>

PartAbortOnNo(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ partSentVote[p] = TRUE
    /\ partVote[p] = no
    /\ partDec' = [partDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartAbortOnCoordFail ==
    /\ coordFaulty
    /\ \A p \in participants: partDec[p] = undecided
    /\ \E p \in participants: partAlive[p] = TRUE
    /\ \A p \in participants:
          /\ partAlive[p] = TRUE
          /\ partDec[p] = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartDecideFromCoord(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ partDec' = [partDec EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived, broadcastSent,
                    partAlive, partFaulty, partVote,
                    partSentVote>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDec,
                    reqSent, votesReceived, broadcastSent,
                    partVote, partDec, partSentVote>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ PartAbortOnCoordFail
    \/ \E p \in participants: PartDecideFromCoord(p)
    \/ \E p \in participants: PartDie(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDec,
                           reqSent, votesReceived, broadcastSent,
                           partAlive, partFaulty, partVote,
                           partDec, partSentVote>>

(*-----------------------------------------------------------------
  Type invariant (ensuring variables stay in their domains)
-----------------------------------------------------------------*)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDec \in Decision
    /\ reqSent \subseteq participants
    /\ votesReceived \in [participants -> (Vote \cup {waiting})]
    /\ broadcastSent \in [participants -> (Decision \cup {notsent})]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> Vote]
    /\ partDec \in [participants -> Decision]
    /\ partSentVote \in [participants -> BOOLEAN]

(*-----------------------------------------------------------------
  Safety invariant: Agreement (no commit vs abort mix)
-----------------------------------------------------------------*)
Agree ==
    \A p, q \in participants :
        (partDec[p] = commit) => (partDec[q] # abort)

=============================================================================