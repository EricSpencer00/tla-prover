---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

(* -------------------------------------------------------------------------- *)
(*  Constants (set in the .cfg)                                               *)
(* -------------------------------------------------------------------------- *)
CONSTANTS
    participants, \* set of participant identifiers
    yes, no,               \* vote values
    undecided, commit, abort, waiting, notsent \* status values
                                          
(* -------------------------------------------------------------------------- *)
(*  Basic value sets                                                          *)
(* -------------------------------------------------------------------------- *)
VoteValues     == {yes, no}
DecisionValues == {commit, abort}
StatusVals     == {undecided, commit, abort}
CoordStatusVals == {waiting, notsent, commit, abort}
ForwardStatus  == {notsent, commit, abort}

(* -------------------------------------------------------------------------- *)
(*  Variables                                                                 *)
(* -------------------------------------------------------------------------- *)
VARIABLES
    coord_alive,            \* TRUE if coordinator is up
    coord_faulty,           \* TRUE if coordinator has crashed
    coord_request,          \* TRUE when request has been sent
    coord_votes,            \* set of participants that have voted
    coord_decision,         \* decision chosen by coordinator (or UNDECIDED)
    coord_broadcasted,      \* set of participants that have been sent the decision
    \* Participant state variables (maps each participant to a value):
    p_alive,                \* [p |-> TRUE/FALSE]
    p_faulty,               \* [p |-> TRUE/FALSE]
    p_vote,                 \* [p |-> yes/no/Undecided]
    p_decision,             \* [p |-> undecided/commit/abort]
    p_forward,              \* [p |-> [q |-> notsent/commit/abort]]
    p_predec                \* [p |-> commit/abort/Undecided]  (pre‑decision)

(* -------------------------------------------------------------------------- *)
(*  Helper definitions                                                       *)
(* -------------------------------------------------------------------------- *)
Undecided == "Undecided"

Init ==
  /\ coord_alive = TRUE
  /\ coord_faulty = FALSE
  /\ coord_request = FALSE
  /\ coord_votes = {}
  /\ coord_decision = Undecided
  /\ coord_broadcasted = {}
  /\ p_alive = [p \in participants |-> TRUE]
  /\ p_faulty = [p \in participants |-> FALSE]
  /\ p_vote = [p \in participants |-> Undecided]
  /\ p_decision = [p \in participants |-> undecided]
  /\ p_forward = [p \in participants |-> [q \in participants |-> notsent]]
  /\ p_predec = [p \in participants |-> Undecided]

(* -------------------------------------------------------------------------- *)
(*  Coordinator actions                                                       *)
(* -------------------------------------------------------------------------- *)

CoordSendReq ==
  /\ coord_alive
  /\ ~coord_request
  /\ coord_request' = TRUE
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_votes,
                 coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward, p_predec>>

CoordReceiveVote(p) ==
  /\ coord_alive
  /\ coord_request
  /\ p \in participants
  /\ p_alive[p]
  /\ p_vote[p] \in VoteValues
  /\ coord_votes' = coord_votes \cup {p}
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward, p_predec>>

CoordMakeDecision ==
  /\ coord_alive
  /\ coord_request
  /\ coord_votes = participants
  /\ coord_decision' = IF \A p \in participants: p_vote[p] = yes
                       THEN commit
                       ELSE abort
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward, p_predec>>

CoordBroadcast ==
  /\ coord_alive
  /\ coord_decision \in DecisionValues
  /\ coord_broadcasted' = participants
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward, p_predec>>

CoordDie ==
  /\ coord_alive
  /\ coord_faulty' = TRUE
  /\ coord_alive' = FALSE
  /\ UNCHANGED <<coord_request, coord_votes, coord_decision,
                 coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward, p_predec>>

(* -------------------------------------------------------------------------- *)
(*  Participant actions                                                       *)
(* -------------------------------------------------------------------------- *)

ParticipantSendVote(p) ==
  /\ p \in participants
  /\ p_alive[p]
  /\ p_vote[p] = Undecided
  /\ coord_request
  /\ p_vote' = [p_vote EXCEPT ![p] = IF p \in coord_votes THEN p_vote[p] ELSE yes]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_decision,
                 p_forward, p_predec>>

ParticipantPreDecFromCoord(p) ==
  /\ p \in participants
  /\ p_alive[p]
  /\ p_predec[p] = Undecided
  /\ p \in coord_broadcasted
  /\ p_predec' = [p_predec EXCEPT ![p] = coord_decision]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward>>

ParticipantPreDecFromPeer(p, q) ==
  /\ p \in participants
  /\ q \in participants
  /\ p <> q
  /\ p_alive[p]
  /\ p_predec[p] = Undecided
  /\ p_forward[q][p] \in {commit, abort}
  /\ p_predec' = [p_predec EXCEPT ![p] = p_forward[q][p]]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_decision,
                 p_forward>>

ParticipantForward(p, q) ==
  /\ p \in participants
  /\ q \in participants
  /\ p <> q
  /\ p_alive[p]
  /\ p_predec[p] \in {commit, abort}
  /\ p_forward[p][q] = notsent
  /\ p_forward' = [p_forward EXCEPT ![p][q] = p_predec[p]]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_predec,
                 p_decision>>

ParticipantDecide(p) ==
  /\ p \in participants
  /\ p_alive[p]
  /\ p_predec[p] \in {commit, abort}
  /\ \A q \in participants \ {p}: p_forward[p][q] = p_predec[p]
  /\ p_decision' = [p_decision EXCEPT ![p] = p_predec[p]]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_forward, p_predec>>

ParticipantAbortTimeout(p) ==
  /\ p \in participants
  /\ p_alive[p]
  /\ p_decision[p] = undecided
  /\ ~coord_alive
  /\ \A q \in participants: q \notin coord_broadcasted
  /\ \A q \in participants: \A r \in participants :
        (p_forward[q][r] # notsent) => FALSE
  /\ p_decision' = [p_decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_alive, p_faulty, p_vote, p_forward, p_predec>>

ParticipantDie(p) ==
  /\ p \in participants
  /\ p_alive[p]
  /\ p_faulty' = [p_faulty EXCEPT ![p] = TRUE]
  /\ p_alive' = [p_alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                 coord_votes, coord_decision, coord_broadcasted,
                 p_vote, p_decision, p_forward, p_predec>>

(* -------------------------------------------------------------------------- *)
(*  NEXT relation (disjunction of all possible steps)                         *)
(* -------------------------------------------------------------------------- *)
Next ==
  \/ CoordSendReq
  \/ \E p \in participants: CoordReceiveVote(p)
  \/ CoordMakeDecision
  \/ CoordBroadcast
  \/ CoordDie
  \/ \E p \in participants: ParticipantSendVote(p)
  \/ \E p \in participants: ParticipantPreDecFromCoord(p)
  \/ \E p, q \in participants: p # q /\ ParticipantPreDecFromPeer(p, q)
  \/ \E p, q \in participants: p # q /\ ParticipantForward(p, q)
  \/ \E p \in participants: ParticipantDecide(p)
  \/ \E p \in participants: ParticipantAbortTimeout(p)
  \/ \E p \in participants: ParticipantDie(p)

(* -------------------------------------------------------------------------- *)
(*  Specification                                                             *)
(* -------------------------------------------------------------------------- *)
SpecNB == Init /\ [][Next]_<<coord_alive, coord_faulty, coord_request,
                        coord_votes, coord_decision, coord_broadcasted,
                        p_alive, p_faulty, p_vote, p_decision,
                        p_forward, p_predec>>

(* -------------------------------------------------------------------------- *)
(*  Type invariant (simple typing)                                            *)
(* -------------------------------------------------------------------------- *)
TypeInvNB ==
  /\ coord_alive \in BOOLEAN
  /\ coord_faulty \in BOOLEAN
  /\ coord_request \in BOOLEAN
  /\ coord_votes \subseteq participants
  /\ coord_decision \in DecisionValues \cup {Undecided}
  /\ coord_broadcasted \subseteq participants
  /\ p_alive \in [participants -> BOOLEAN]
  /\ p_faulty \in [participants -> BOOLEAN]
  /\ p_vote \in [participants -> (VoteValues \cup {Undecided})]
  /\ p_decision \in [participants -> StatusVals]
  /\ p_forward \in [participants -> [participants -> ForwardStatus]]
  /\ p_predec \in [participants -> (DecisionValues \cup {Undecided})]

(* -------------------------------------------------------------------------- *)
(*  AC1: Agreement (no commit vs abort)                                       *)
(* -------------------------------------------------------------------------- *)
AC1 ==
  \A p, q \in participants :
    (p_decision[p] = commit) => (p_decision[q] \in {commit, undecided})

(* -------------------------------------------------------------------------- *)
(*  AC2: Commit validity                                                      *)
(* -------------------------------------------------------------------------- *)
AC2 ==
  \A p \in participants :
    (p_decision[p] = commit) => (\A q \in participants : p_vote[q] = yes)

(* -------------------------------------------------------------------------- *)
(*  AC3: Abort validity                                                      *)
(* -------------------------------------------------------------------------- *)
AC3 ==
  \A p \in participants :
    (p_decision[p] = abort) =>
      (\E q \in participants : p_vote[q] = no) \/
      (\E q \in participants : p_faulty[q]) \/
      coord_faulty

(* -------------------------------------------------------------------------- *)
(*  AC4: Irrevocability                                                       *)
(* -------------------------------------------------------------------------- *)
AC4 ==
  \A p \in participants :
    (p_decision[p] = commit) => (p_decision[p]' = commit) /\
    (p_decision[p] = abort) => (p_decision[p]' = abort)

(* -------------------------------------------------------------------------- *)
(*  AC5: Non‑blocking termination (liveness)                                 *)
(* -------------------------------------------------------------------------- *)
AC5 ==
  \A p \in participants :
    (p_alive[p] /\ ~p_faulty[p]) => <> (p_decision[p] \in {commit, abort})

(* -------------------------------------------------------------------------- *)
(*  PROPERTY (alias for the liveness property required by the .cfg)           *)
(* -------------------------------------------------------------------------- *)
PROPERTY == AC5

(* -------------------------------------------------------------------------- *)
(*  The set of invariants exported for the .cfg                                *)
(* -------------------------------------------------------------------------- *)
INVARIANTS == TypeInvNB

====