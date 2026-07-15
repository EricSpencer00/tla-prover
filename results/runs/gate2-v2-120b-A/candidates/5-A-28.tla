---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    \* Coordinator state
    coordAlive,               \* TRUE iff coordinator is alive
    coordDecision,            \* one of {undecided, commit, abort}
    coordRequests,            \* subset of participants to whom a vote request was sent
    coordVotes,               \* [p \in participants |-> waiting] or yes/no
    coordSentDecision,        \* [p \in participants |-> notsent] or commit/abort
    \* Participant state
    alive,                    \* [p \in participants |-> BOOLEAN]
    vote,                     \* [p \in participants |-> yes/no]
    sentVote,                 \* [p \in participants |-> BOOLEAN] (has participant sent its vote)
    decision                 \* [p \in participants |-> undecided/commit/abort]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
VoteSet == {yes, no}
DecisionSet == {undecided, commit, abort}
CoordDecisionSet == {undecided, commit, abort}
RequestState == BOOLEAN
SentDecisionState == {notsent, commit, abort}
CoordVoteState == {waiting} \cup VoteSet

(* Type invariant (not the safety invariant) *)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in CoordDecisionSet
    /\ coordRequests \subseteq participants
    /\ coordVotes \in [participants -> CoordVoteState]
    /\ coordSentDecision \in [participants -> SentDecisionState]
    /\ alive \in [participants -> BOOLEAN]
    /\ vote \in [participants -> VoteSet]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decision \in [participants -> DecisionSet]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordRequests = {}
    /\ coordVotes = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]
    /\ alive = [p \in participants |-> TRUE]
    /\ vote = [p \in participants |-> CHOOSE v \in VoteSet : TRUE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

(* Coordinator actions *)

CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin coordRequests
    /\ coordRequests' = coordRequests \cup {p}
    /\ UNCHANGED <<coordAlive, coordDecision, coordVotes,
                    coordSentDecision, alive, vote,
                    sentVote, decision>>

CoordRecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordRequests
    /\ coordVotes[p] = waiting
    /\ sentVote[p] = TRUE
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordSentDecision, alive, vote,
                    sentVote, decision>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in coordRequests
    /\ coordVotes[p] = waiting
    /\ alive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordRequests, coordVotes,
                    coordSentDecision, alive, vote,
                    sentVote, decision>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVotes[p] # waiting
    /\ IF \A p \in participants: coordVotes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordRequests, coordVotes,
                    coordSentDecision, alive, vote,
                    sentVote, decision>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ p \in participants
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, alive, vote,
                    sentVote, decision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, coordRequests, coordVotes,
                    coordSentDecision, alive, vote,
                    sentVote, decision>>

(* Participant actions *)

PartSendVote(p) ==
    /\ alive[p]
    /\ p \in participants
    /\ p \in coordRequests
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, coordSentDecision,
                    alive, vote, decision>>

PartAbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p] = TRUE
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, coordSentDecision,
                    alive, vote, sentVote>>

PartAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin coordRequests
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, coordSentDecision,
                    alive, vote, sentVote>>

PartDecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSentDecision[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, coordSentDecision,
                    alive, vote, sentVote>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordRequests,
                    coordVotes, coordSentDecision,
                    vote, sentVote, decision>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

Spec == Init /\ [][Next]_<<coordAlive, coordDecision, coordRequests,
                         coordVotes, coordSentDecision,
                         alive, vote, sentVote, decision>>

(*-----------------------------------------------------------------
  Safety invariants (required by the description)
-----------------------------------------------------------------*)
(* AC1: No two participants decide differently *)
AC1 ==
    \A p, q \in participants:
        (decision[p] = commit => decision[q] = commit) /\
        (decision[p] = abort  => decision[q] = abort)  /\
        (decision[p] = undecided => decision[q] = undecided \/ decision[q] \in {commit, abort})

(* AC2: If any participant decides commit, then all participants voted yes *)
AC2 ==
    \A p \in participants:
        decision[p] = commit => \A q \in participants: vote[q] = yes

(* AC3: If any participant decides abort, then either some vote was no, or some participant is faulty, or coordinator is faulty *)
AC3 ==
    \A p \in participants:
        decision[p] = abort =>
            (\E q \in participants: vote[q] = no) \/
            (\E q \in participants: ~alive[q]) \/
            (~coordAlive)

(* AC4: Irrevocability – decisions are monotonic *)
AC4 ==
    \A p \in participants:
        (decision[p] = commit => []<>(decision[p] = commit)) /\
        (decision[p] = abort  => []<>(decision[p] = abort))

(* The overall safety invariant required by the reference cfg *)
Safety == AC1 /\ AC2 /\ AC3 /\ AC4

=============================================================================