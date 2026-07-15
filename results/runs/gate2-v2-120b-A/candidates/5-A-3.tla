---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* ---------------------------------------------------------------------- *)
(* Types and derived sets                                                  *)
(* ---------------------------------------------------------------------- *)

Values == {yes, no}
Decisions == {undecided, commit, abort}
SendStatus == {notsent, sent}
PartStatus == {alive, faulty}
CoordStatus == {alive, faulty}
VoteMap == [p \in participants -> Values]
DecisionMap == [p \in participants -> Decisions]
VotedMap == [p \in participants -> BOOLEAN]
DecisionSentMap == [p \in participants -> SendStatus]
SentVoteMap == [p \in participants -> BOOLEAN]
RequestSentMap == [p \in participants -> BOOLEAN]
VoteReceivedMap == [p \in participants -> (Values \cup {waiting})]

(* ---------------------------------------------------------------------- *)
(* Variables                                                               *)
(* ---------------------------------------------------------------------- *)
VARIABLES
    partAlive,          \* [p \in participants -> BOOLEAN]  (true = alive)
  , partFaulty,         \* [p \in participants -> BOOLEAN]  (true = faulty)
  , partVote,           \* [p \in participants -> Values]
  , partDecision,       \* [p \in participants -> Decisions]
  , partSentVote,       \* [p \in participants -> BOOLEAN] (has sent its vote)
  , coordAlive,         \* BOOLEAN
  , coordFaulty,        \* BOOLEAN
  , requestSent,        \* [p \in participants -> BOOLEAN] (request sent)
  , voteReceived,       \* [p \in participants -> (Values \cup {waiting})]
  , coordDecision,      \* Decisions
  , decisionSent        \* [p \in participants -> SendStatus]

(* ---------------------------------------------------------------------- *)
(* Helper definitions                                                     *)
(* ---------------------------------------------------------------------- *)

ParticipantSet == participants
AllSentVotes   == \A p \in participants: voteReceived[p] # waiting

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> CHOOSE v \in Values : TRUE]
    /\ partDecision = [p \in participants |-> undecided]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ decisionSent = [p \in participants |-> notsent]

(* ---------------------------------------------------------------------- *)
(* Actions                                                                *)
(* ---------------------------------------------------------------------- *)

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    voteReceived, coordDecision, decisionSent >>

CoordRecvVote(p) ==
    /\ coordAlive
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ partSentVote[p]
    /\ voteReceived' = [voteReceived EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    requestSent, coordDecision, decisionSent >>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ ~partAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    requestSent, voteReceived, decisionSent,
                    partSentVote >>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: voteReceived[p] # waiting
    /\ IF \A p \in participants: voteReceived[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    requestSent, voteReceived, decisionSent,
                    partSentVote >>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ decisionSent[p] = notsent
    /\ decisionSent' = [decisionSent EXCEPT ![p] = sent]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    requestSent, voteReceived, coordDecision,
                    partSentVote >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, requestSent, voteReceived,
                    coordDecision, decisionSent >>

PartSendVote(p) ==
    /\ partAlive[p]
    /\ requestSent[p]
    /\ ~partSentVote[p]
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partDecision,
                    partSentVote, coordAlive, coordFaulty,
                    requestSent, voteReceived, coordDecision,
                    decisionSent >>

PartAbortOnNo(p) ==
    /\ partAlive[p]
    /\ partSentVote[p]
    /\ partVote[p] = no
    /\ partDecision[p] = undecided
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partSentVote,
                    coordAlive, coordFaulty, requestSent, voteReceived,
                    coordDecision, decisionSent >>

PartAbortOnCoordDead(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordAlive
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partSentVote,
                    coordAlive, coordFaulty, requestSent, voteReceived,
                    coordDecision, decisionSent, partDecision >>

PartDecideOnBroadcast(p) ==
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ decisionSent[p] = sent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << partAlive, partFaulty, partVote, partSentVote,
                    coordAlive, coordFaulty, requestSent, voteReceived,
                    coordDecision, decisionSent, partDecision >>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << partVote, partDecision, partSentVote,
                    coordAlive, coordFaulty, requestSent, voteReceived,
                    coordDecision, decisionSent >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation                                                     *)
(* ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnCoordDead(p)
    \/ \E p \in participants: PartDecideOnBroadcast(p)
    \/ \E p \in participants: PartDie(p)

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<< partAlive, partFaulty, partVote,
                         partDecision, partSentVote,
                         coordAlive, coordFaulty,
                         requestSent, voteReceived,
                         coordDecision, decisionSent >>

(* ---------------------------------------------------------------------- *)
(* Type invariant (optional but useful)                                    *)
(* ---------------------------------------------------------------------- *)
TypeInv ==
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> Values]
    /\ partDecision \in [participants -> Decisions]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> (Values \cup {waiting})]
    /\ coordDecision \in Decisions
    /\ decisionSent \in [participants -> SendStatus]

(* ---------------------------------------------------------------------- *)
(* Safety invariants                                                       *)
(* ---------------------------------------------------------------------- *)

(* AC1: No two participants decide differently *)
Agree ==
    \A p,q \in participants :
        (partDecision[p] = commit => partDecision[q] = commit) /\
        (partDecision[p] = abort  => partDecision[q] = abort)

(* AC2: Commit validity *)
CommitValidity ==
    \A p \in participants :
        partDecision[p] = commit => \A q \in participants: partVote[q] = yes

(* AC3: Abort validity *)
AbortValidity ==
    \A p \in participants :
        partDecision[p] = abort =>
            (\E q \in participants: partVote[q] = no) \/
            (\E q \in participants: partFaulty[q]) \/
            coordFaulty

(* AC4: Irrevocability *)
Irrevocability ==
    \A p \in participants :
        (partDecision[p] = commit => [] (partDecision[p] = commit)) /\
        (partDecision[p] = abort  => [] (partDecision[p] = abort))

(* ---------------------------------------------------------------------- *)
(* The identifier required by the .cfg file                                 *)
(* ---------------------------------------------------------------------- *)
INVARIANTS == TypeInv

=============================================================================