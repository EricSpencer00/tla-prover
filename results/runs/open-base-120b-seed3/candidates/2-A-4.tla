---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (provided by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS 
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort, waiting, \* decision values
    notsent         \* forwarding status indicating nothing sent

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES 
    coordAlive,          \* coordinator liveness
    coordFaulty,         \* coordinator faulty flag
    coordDecision,       \* coordinator's decision (waiting, commit, abort)
    participantAlive,    \* [p \in participants |-> BOOLEAN]
    participantFaulty,   \* [p \in participants |-> BOOLEAN]
    participantVote,     \* [p \in participants |-> {yes,no}]
    participantDecision, \* [p \in participants |-> {undecided, commit, abort}]
    forwarded            \* [p \in participants |-> [q \in participants |-> {notsent, commit, abort}]]

vars == << coordAlive, coordFaulty, coordDecision,
          participantAlive, participantFaulty,
          participantVote, participantDecision,
          forwarded >>

(*-----------------------------------------------------------------
  Type invariant (used by the .cfg file)
-----------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {waiting, commit, abort}
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

(*-----------------------------------------------------------------
  Coordinator actions (inherited from ACP‑SB)
-----------------------------------------------------------------*)
(* The coordinator may decide (commit/abort) after collecting votes.
   For brevity we just allow a nondeterministic decision when alive. *)
CoordDecide ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED << coordAlive, coordFaulty, participantAlive,
                    participantFaulty, participantVote,
                    participantDecision, forwarded >>

(* The coordinator may crash. *)
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, participantAlive,
                    participantFaulty, participantVote,
                    participantDecision, forwarded >>

(*-----------------------------------------------------------------
  Participant actions
-----------------------------------------------------------------*)

(* (1) Pre‑decide from coordinator *)
PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwarded[p][p] = notsent
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ forwarded' = [forwarded EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

(* (2) Pre‑decide from forwarding by another participant *)
PreDecideFromFwd(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwarded[p][p] = notsent
    /\ \E q \in participants : q # p /\ forwarded[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                \E q \in participants : q # p /\ forwarded[q][p] = d
       IN forwarded' = [forwarded EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

(* (3) Forward to a specific other participant *)
Forward(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ forwarded[p][p] \in {commit, abort}
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, participantDecision >>

(* (4) Decide locally after having forwarded to everyone *)
Decide(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwarded[p][p] \in {commit, abort}
    /\ \A q \in participants : q # p => forwarded[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, forwarded >>

(* (5) Abort on timeout (coordinator dead and no information) *)
AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          ( participantAlive[q] => \A r \in participants : forwarded[q][r] = notsent )
    /\ \A q \in participants :
          ( ~participantAlive[q] => \A r \in participants : forwarded[q][r] = notsent )
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, forwarded >>

(* (6) Participant crashes *)
ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantVote, participantDecision, forwarded >>

(* (7) Send vote to coordinator – abstracted (does not affect other vars) *)
SendVote(p) ==
    /\ participantAlive[p]
    /\ UNCHANGED vars

(* (8) Abort locally on receiving a “no” vote from the coordinator – abstracted *)
AbortOnNo(p) ==
    /\ participantAlive[p]
    /\ participantVote[p] = no
    /\ participantDecision[p] = undecided
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantVote, forwarded >>

(*-----------------------------------------------------------------
  Next-state relation (disjunction of all possible actions)
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : (p # q) /\ Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnNo(p)
    \/ CoordDecide
    \/ CoordDie

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariants (the .cfg file expects TypeInvNB)
-----------------------------------------------------------------*)
INVARIANTS TypeInvNB

====