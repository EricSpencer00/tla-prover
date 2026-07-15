---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

(* ------------------------------------------------------------------------ *)
(* Constants ----------------------------------------------------------------*)
CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort, waiting, notsent

(* ------------------------------------------------------------------------ *)
(* Types --------------------------------------------------------------------*)
Participant == participants

VoteVal == {yes, no}
Decision == {commit, abort, undecided}
ForwardStatus == {notsent, commit, abort}

(* ------------------------------------------------------------------------ *)
(* Variables ----------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* BOOLEAN: coordinator is alive
    coordFaulty,         \* BOOLEAN: coordinator is faulty (crashed with fault)
    coordRequest,        \* BOOLEAN: true when request sent, false otherwise
    coordDecision,       \* Decision made by coordinator (undecided until set)
    votes,               \* [Participant -> VoteVal], votes cast by participants
    votesSent,           \* [Participant -> BOOLEAN], true if vote sent
    forwardTable,        \* [Participant -> [Participant -> ForwardStatus]]
    participantAlive,    \* [Participant -> BOOLEAN]
    participantFaulty,   \* [Participant -> BOOLEAN]
    participantDecision  \* [Participant -> Decision]

(* ------------------------------------------------------------------------ *)
(* Helper definitions -------------------------------------------------------*)
AllForwarded(p) ==
    \A q \in participants : forwardTable[p][q] # notsent

AllPreDecided ==
    \A p \in participants :
        forwardTable[p][p] # notsent

AnyParticipantFaulty ==
    \E p \in participants : participantFaulty[p]

CoordinatorFaulty ==
    coordFaulty

AnyVoteNo ==
    \E p \in participants : votes[p] = no

AllVotedYes ==
    \A p \in participants : votes[p] = yes

AllAliveDecided ==
    \A p \in participants :
        participantAlive[p] => participantDecision[p] # undecided

(* ------------------------------------------------------------------------ *)
(* Initial state ------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordRequest = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> yes]          \* initial placeholder; will be set by votes
    /\ votesSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

(* ------------------------------------------------------------------------ *)
(* Actions ------------------------------------------------------------------*)

(* Participant sends its vote to the coordinator *)
SendVote(p) ==
    /\ participantAlive[p]
    /\ ~votesSent[p]
    /\ participantDecision[p] = undecided
    /\ votesSent' = [votesSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, forwardTable,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Coordinator receives a vote (modeled as immediate effect on votes map) *)
RecvVote(p, v) ==
    /\ coordAlive
    /\ votesSent[p]
    /\ v \in VoteVal
    /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED << coordFaulty, coordRequest, coordDecision,
                    votesSent,
                    forwardTable,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Coordinator decides based on collected votes *)
CoordDecide ==
    /\ coordAlive
    /\ \A p \in participants : votesSent[p]
    /\ coordDecision' =
        IF \A p \in participants : votes[p] = yes
           THEN commit
           ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest,
                    votes, votesSent,
                    forwardTable,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Coordinator broadcasts decision to a participant p *)
CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Participant receives pre-decision directly from coordinator *)
PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwardTable[p][p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    forwardTable,
                    participantAlive, participantFaulty >>

(* Participant receives forwarded pre-decision from q *)
PreDecideFromForward(p, q) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwardTable[q][p] # notsent
    /\ forwardTable[p][p] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Participant forwards its pre-decision to q *)
Forward(p, q) ==
    /\ participantAlive[p]
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* Participant makes final decision after forwarding to all others *)
Decide(p) ==
    /\ participantAlive[p]
    /\ AllForwarded(p)
    /\ participantDecision[p] = undecided
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    forwardTable,
                    participantAlive, participantFaulty >>

(* Abort on timeout when coordinator dead and no forward received *)
AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          forwardTable[q][p] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    forwardTable,
                    participantAlive, participantFaulty >>

(* Participant crashes (becomes faulty) *)
Die(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent,
                    forwardTable,
                    participantDecision >>

(* Coordinator crashes (becomes faulty) *)
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordRequest, coordDecision,
                    votes, votesSent,
                    forwardTable,
                    participantAlive, participantFaulty,
                    participantDecision >>

(* ------------------------------------------------------------------------ *)
(* Next-state relation ------------------------------------------------------*)
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : \E v \in VoteVal : RecvVote(p, v)
    \/ CoordDecide
    \/ \E p \in participants : CoordBroadcast(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p, q \in participants : PreDecideFromForward(p, q)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordDie

(* ------------------------------------------------------------------------ *)
(* Specification ------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordRequest, coordDecision,
                    votes, votesSent, forwardTable,
                    participantAlive, participantFaulty,
                    participantDecision>>

(* ------------------------------------------------------------------------ *)
(* Type invariant -----------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordRequest \in BOOLEAN
    /\ coordDecision \in Decision
    /\ votes \in [Participant -> VoteVal]
    /\ votesSent \in [Participant -> BOOLEAN]
    /\ participantAlive \in [Participant -> BOOLEAN]
    /\ participantFaulty \in [Participant -> BOOLEAN]
    /\ participantDecision \in [Participant -> Decision]
    /\ forwardTable \in [Participant -> [Participant -> ForwardStatus]]

(* ------------------------------------------------------------------------ *)
(* Safety invariants --------------------------------------------------------*)
(* AC1: Agreement *)
Agree ==
    \A p, q \in participants :
        (participantDecision[p] = commit) => (participantDecision[q] = commit)

(* AC2: Commit validity *)
CommitValidity ==
    ( \E p \in participants : participantDecision[p] = commit )
    => AllVotedYes

(* AC3: Abort validity *)
AbortValidity ==
    ( \E p \in participants : participantDecision[p] = abort )
    => ( AnyVoteNo \/ AnyParticipantFaulty \/ CoordinatorFaulty )

(* AC4: Irrevocability *)
Irrevocable ==
    \A p \in participants :
        ( participantDecision[p] = commit => participantDecision[p]' = commit ) /\
        ( participantDecision[p] = abort  => participantDecision[p]' = abort )

(* The .cfg will refer to TypeInvNB as the only INVARIANT, but we keep the others
   defined for completeness. *)

====