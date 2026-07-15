---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants (must be declared in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT participants
CONSTANT yes, no, undecided, commit, abort, waiting, notsent

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    coordAlive,                \* TRUE iff coordinator is alive
    coordFaulty,               \* TRUE iff coordinator has crashed
    coordDecision,             \* cooperative decision: undecided, commit or abort
    sentRequest,               \* set of participants to which a vote request has been sent
    receivedVote,              \* mapping p \in participants |-> yes/no/WAITING
    sentDecision,              \* set of participants to which the decision has been broadcast
    partAlive,                 \* mapping p \in participants |-> BOOLEAN (alive?)
    partFaulty,                \* mapping p \in participants |-> BOOLEAN (crashed?)
    partVote,                  \* mapping p \in participants |-> yes/no (the vote chosen at start)
    partDecision,              \* mapping p \in participants |-> undecided/commit/abort
    partVotedSent              \* set of participants that have already sent their vote

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Participants == participants
YesNo        == {yes, no}
DecisionVals == {undecided, commit, abort}
CoordState   == [ sentRequest   : SUBSET Participants,
                 receivedVote  : [Participants -> YesNo \/ {waiting}],
                 sentDecision  : SUBSET Participants,
                 decision      : DecisionVals,
                 alive         : BOOLEAN,
                 faulty        : BOOLEAN ]

PartState    == [ alive    : BOOLEAN,
                 faulty   : BOOLEAN,
                 vote     : YesNo,
                 decision : DecisionVals,
                 votedSent: BOOLEAN ]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ sentRequest = {}
    /\ sentDecision = {}
    /\ receivedVote = [p \in Participants |-> waiting]
    /\ partAlive = [p \in Participants |-> TRUE]
    /\ partFaulty = [p \in Participants |-> FALSE]
    /\ partVote = [p \in Participants |-> CHOOSE v \in YesNo : TRUE] \* nondeterministic yes/no
    /\ partDecision = [p \in Participants |-> undecided]
    /\ partVotedSent = {}

(*--------------------------------------------------------------------
  Coordinator actions
--------------------------------------------------------------------*)

SendRequest(p) ==
    /\ coordAlive = TRUE
    /\ p \in Participants
    /\ p \notin sentRequest
    /\ sentRequest' = sentRequest \cup {p}
    /\ UNCHANGED <<coordDecision, receivedVote, sentDecision,
                   coordFaulty, coordAlive,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

ReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ p \in sentRequest
    /\ receivedVote[p] = waiting
    /\ partVotedSent[p] = TRUE
    /\ partAlive[p] = TRUE
    /\ receivedVote' = [receivedVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, sentDecision,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

DetectFault(p) ==
    /\ coordAlive = TRUE
    /\ p \in sentRequest
    /\ receivedVote[p] = waiting
    /\ partAlive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, sentRequest, receivedVote,
                   sentDecision,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

MakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in Participants: receivedVote[p] # waiting
    /\ IF \A p \in Participants: receivedVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, sentRequest, receivedVote,
                   sentDecision,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

BroadcastDecision(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # undecided
    /\ p \in sentRequest
    /\ p \notin sentDecision
    /\ sentDecision' = sentDecision \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, sentRequest, receivedVote,
                   sentDecision,
                   partAlive, partFaulty, partVote,
                   partDecision, partVotedSent>>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)

SendVote(p) ==
    /\ partAlive[p] = TRUE
    /\ p \notin partVotedSent
    /\ p \in sentRequest            \* request already received
    /\ partVotedSent' = partVotedSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote, sentDecision,
                   partAlive, partFaulty, partVote,
                   partDecision>>

AbortOnVote(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ partVotedSent[p] = TRUE
    /\ partVote[p] = no
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote, sentDecision,
                   partAlive, partFaulty, partVote,
                   partVotedSent>>

AbortOnTimeout(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ sentRequest = {}
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote, sentDecision,
                   partAlive, partFaulty, partVote,
                   partVotedSent>>

DecideFromBroadcast(p) ==
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ p \in sentDecision
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote, sentDecision,
                   partAlive, partFaulty, partVote,
                   partVotedSent>>

PartDie(p) ==
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   sentRequest, receivedVote, sentDecision,
                   partVote, partDecision, partVotedSent>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in Participants: SendRequest(p)
    \/ \E p \in Participants: ReceiveVote(p)
    \/ \E p \in Participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in Participants: BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in Participants: SendVote(p)
    \/ \E p \in Participants: AbortOnVote(p)
    \/ \E p \in Participants: AbortOnTimeout(p)
    \/ \E p \in Participants: DecideFromBroadcast(p)
    \/ \E p \in Participants: PartDie(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         sentRequest, receivedVote, sentDecision,
                         partAlive, partFaulty, partVote,
                         partDecision, partVotedSent>>

(*--------------------------------------------------------------------
  Type invariant (ensures variables stay within expected domains)
--------------------------------------------------------------------*)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionVals
    /\ sentRequest \subseteq Participants
    /\ sentDecision \subseteq Participants
    /\ receivedVote \in [Participants -> YesNo \/ {waiting}]
    /\ partAlive \in [Participants -> BOOLEAN]
    /\ partFaulty \in [Participants -> BOOLEAN]
    /\ partVote \in [Participants -> YesNo]
    /\ partDecision \in [Participants -> DecisionVals]
    /\ partVotedSent \subseteq Participants

(*--------------------------------------------------------------------
  Safety invariants (optional, not required by the cfg but useful)
--------------------------------------------------------------------*)
(* Agreement / Consistency *)
Consistent ==
    \A p, q \in Participants :
        (partDecision[p] = commit) => (partDecision[q] = commit)

(* Commit validity *)
CommitValid ==
    \A p \in Participants :
        partDecision[p] = commit => \A q \in Participants : partVote[q] = yes

(* Abort validity *)
AbortValid ==
    \A p \in Participants :
        partDecision[p] = abort =>
            \/ \E q \in Participants : partVote[q] = no
            \/ \E q \in Participants : partFaulty[q] = TRUE
            \/ coordFaulty = TRUE

(* Irrevocability *)
Irrevocable ==
    \A p \in Participants :
        (partDecision[p] = commit => [] (partDecision[p] = commit)) /\
        (partDecision[p] = abort  => [] (partDecision[p] = abort))

=============================================================================