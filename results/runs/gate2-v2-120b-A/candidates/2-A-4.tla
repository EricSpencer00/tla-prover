---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ------------------------------------------------------------------------- *)
(* Type definitions *)
(* ------------------------------------------------------------------------- *)

Participant == participants
ParticipantSet == participants

Decision == {commit, abort, undecided}
PreDecision == {commit, abort, undecided}
Vote == {yes, no}
CoordState == {"idle", "requestSent", "receiving", "decisionMade", "broadcasting", "dead"}
ForwardStatus == {notsent, commit, abort}

(* ------------------------------------------------------------------------- *)
(* Variables *)
(* ------------------------------------------------------------------------- *)

VARIABLES
    coord_state,          \* State of the coordinator
    coord_decision,       \* Decision made by coordinator (commit/abort)
    coord_alive,          \* TRUE if coordinator is alive
    coord_faulty,         \* TRUE if coordinator is known to be faulty
    votes,                \* [p \in Participant -> Vote], votes sent by participants
    vote_sent,            \* [p \in Participant -> BOOLEAN], whether participant has sent its vote
    participant_state,    \* [p \in Participant -> {"alive", "dead"}]
    participant_decision, \* [p \in Participant -> Decision]
    faulty,               \* [p \in Participant -> BOOLEAN], participant fault flag
    forwarding,           \* [p \in Participant -> [q \in Participant -> ForwardStatus]]
    forwarded_to,         \* [p \in Participant -> SUBSET Participant], set of participants to which p has already forwarded
    predecided            \* [p \in Participant -> BOOLEAN], whether p has stored a pre‑decision

(* ------------------------------------------------------------------------- *)
(* Helper definitions *)
(* ------------------------------------------------------------------------- *)

Alive(p) == participant_state[p] = "alive"
Dead(p)  == participant_state[p] = "dead"

AllAlive == { p \in Participant : Alive(p) }
AllDead  == { p \in Participant : Dead(p) }

PreDecisions(p) == forwarding[p][p] \in {commit, abort}

(* ------------------------------------------------------------------------- *)
(* Initial state *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ coord_state = "idle"
    /\ coord_decision = undecided
    /\ coord_alive = TRUE
    /\ coord_faulty = FALSE
    /\ votes = [p \in Participant |-> yes]   \* arbitrary initial vote
    /\ vote_sent = [p \in Participant |-> FALSE]
    /\ participant_state = [p \in Participant |-> "alive"]
    /\ participant_decision = [p \in Participant |-> undecided]
    /\ faulty = [p \in Participant |-> FALSE]
    /\ forwarding = [p \in Participant |-> [q \in Participant |-> notsent]]
    /\ forwarded_to = [p \in Participant |-> {}]
    /\ predecided = [p \in Participant |-> FALSE]

(* ------------------------------------------------------------------------- *)
(* Coordinator actions (inherited from ACP‑SB) *)
(* ------------------------------------------------------------------------- *)

SendRequest ==
    /\ coord_state = "idle"
    /\ coord_state' = "requestSent"
    /\ UNCHANGED << coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

ReceiveVote(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ /\ votes[p] \in {yes, no}
       /\ vote_sent[p] = FALSE
    /\ vote_sent' = [vote_sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

DetectFault(p) ==
    /\ p \in Participant
    /\ Dead(p)
    /\ /\ ~faulty[p]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    forwarding, forwarded_to, predecided >>

MakeDecision ==
    /\ coord_state = "receiving"
    /\ coord_state' = "decisionMade"
    /\ coord_decision' = IF \A p \in Participant : votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << coord_alive, coord_faulty, votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

BroadcastDecision ==
    /\ coord_state = "decisionMade"
    /\ coord_state' = "broadcasting"
    /\ UNCHANGED << coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

CoordDie ==
    /\ coord_alive = TRUE
    /\ coord_alive' = FALSE
    /\ coord_state' = "dead"
    /\ UNCHANGED << coord_decision, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

(* ------------------------------------------------------------------------- *)
(* Participant actions introduced for ACP‑NB *)
(* ------------------------------------------------------------------------- *)

SendVote(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ vote_sent[p] = FALSE
    /\ vote_sent' = [vote_sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, participant_state, participant_decision,
                    faulty, forwarding, forwarded_to, predecided >>

PreDecideFromCoord(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ ~predecided[p]
    /\ coord_state = "broadcasting"
    /\ forwarding[p][p] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = 
          IF coord_decision = commit THEN commit ELSE abort]
    /\ predecided' = [predecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarded_to >>

PreDecideFromForward(q,p) ==
    /\ q \in Participant
    /\ p \in Participant
    /\ p # q
    /\ Alive(p) /\ Alive(q)
    /\ ~predecided[p]
    /\ forwarding[q][p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ predecided' = [predecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, forwarded_to >>

Forward(p,q) ==
    /\ p \in Participant
    /\ q \in Participant
    /\ p # q
    /\ Alive(p) /\ Alive(q)
    /\ forwarding[p][p] \in {commit, abort}
    /\ q \notin forwarded_to[p]
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ forwarded_to' = [forwarded_to EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, participant_decision,
                    faulty, predecided >>

Decide(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ predecided[p]
    /\ \A q \in Participant : q = p \/ q \in forwarded_to[p]
    /\ participant_decision' = [participant_decision EXCEPT ![p] = 
          IF forwarding[p][p] = commit THEN commit ELSE abort]
    /\ predecided' = [predecided EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, faulty,
                    forwarding, forwarded_to >>

AbortOnTimeout(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ \A q \in Participant : participant_decision[q] = undecided
    /\ coord_alive = FALSE
    /\ \A q \in Participant : forwarding[q][p] = notsent
    /\ participant_decision' = [participant_decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_state, faulty,
                    forwarding, forwarded_to, predecided >>

ParticipantDie(p) ==
    /\ p \in Participant
    /\ Alive(p)
    /\ participant_state' = [participant_state EXCEPT ![p] = "dead"]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coord_state, coord_decision, coord_alive, coord_faulty,
                    votes, vote_sent,
                    participant_decision,
                    forwarding, forwarded_to, predecided >>

(* ------------------------------------------------------------------------- *)
(* Next-state relation *)
(* ------------------------------------------------------------------------- *)

CoordinatorActions ==
    \/ SendRequest
    \/ \E p \in Participant : ReceiveVote(p)
    \/ \E p \in Participant : DetectFault(p)
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordDie

ParticipantActions ==
    \/ \E p \in Participant : SendVote(p)
    \/ \E p \in Participant : PreDecideFromCoord(p)
    \/ \E p,q \in Participant : PreDecideFromForward(p,q)
    \/ \E p,q \in Participant : Forward(p,q)
    \/ \E p \in Participant : Decide(p)
    \/ \E p \in Participant : AbortOnTimeout(p)
    \/ \E p \in Participant : ParticipantDie(p)

Next ==
    \/ CoordinatorActions
    \/ ParticipantActions

(* ------------------------------------------------------------------------- *)
(* Specification *)
(* ------------------------------------------------------------------------- *)

SpecNB == Init /\ [][Next]_<<coord_state, coord_decision, coord_alive, coord_faulty,
                        votes, vote_sent,
                        participant_state, participant_decision,
                        faulty, forwarding, forwarded_to, predecided>>

(* ------------------------------------------------------------------------- *)
(* Type invariant (minimal, asserts that all variables stay within expected domains) *)
(* ------------------------------------------------------------------------- *)

TypeInvNB ==
    /\ coord_state \in {"idle", "requestSent", "receiving", "decisionMade",
                        "broadcasting", "dead"}
    /\ coord_decision \in Decision
    /\ coord_alive \in BOOLEAN
    /\ coord_faulty \in BOOLEAN
    /\ votes \in [Participant -> Vote]
    /\ vote_sent \in [Participant -> BOOLEAN]
    /\ participant_state \in [Participant -> {"alive", "dead"}]
    /\ participant_decision \in [Participant -> Decision]
    /\ faulty \in [Participant -> BOOLEAN]
    /\ forwarding \in [Participant -> [Participant -> ForwardStatus]]
    /\ forwarded_to \in [Participant -> SUBSET Participant]
    /\ predecided \in [Participant -> BOOLEAN]

=============================================================================