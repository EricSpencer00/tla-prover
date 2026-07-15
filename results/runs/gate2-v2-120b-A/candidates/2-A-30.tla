---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no, undecided,
    commit, abort, waiting,
    notsent

(* ---------------------------------------------------------------------- *)
(* Types *)
TypeSet == {yes, no}
Decision == {commit, abort}
ParticipantState == {waiting, commit, abort}
ForwardStatus == {notsent, commit, abort}

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES
    votes,               \* [p \in participants -> {yes,no}]
    voteSent,            \* [p \in participants -> BOOLEAN] (has participant sent its vote)
    coordAlive,          \* BOOLEAN, coordinator alive?
    coordFaulty,         \* BOOLEAN, coordinator faulty flag
    coordDecision,       \* Decision \cup {undecided}
    broadcastSent,       \* [p \in participants -> BOOLEAN] (has coordinator broadcasted to p)
    decision,            \* [p \in participants -> ParticipantState]
    forwarding,          \* [p \in participants -> [q \in participants -> ForwardStatus]]
    alive                \* [p \in participants -> BOOLEAN] (participant alive flag)

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
ParticipantSet == participants

PreDecideFromCoord(p) ==
    /\ coordAlive
    /\ broadcastSent[p]
    /\ forwarding[p][p] = notsent
    /\ forwarding[p][p]' = coordDecision
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, decision,
                    forwarding, alive>>

PreDecideFromPeer(p) ==
    \E r \in participants :
        /\ p # r
        /\ forwarding[r][p] # notsent
        /\ forwarding[p][p] = notsent
        /\ forwarding[p][p]' = forwarding[r][p]
        /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, decision,
                    forwarding, alive>>

Forward(p, q) ==
    /\ p # q
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding[p][q]' = forwarding[p][p]
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, decision,
                    forwarding, alive>>

Decide(p) ==
    /\ forwarding[p][p] # notsent
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision[p] = waiting
    /\ decision[p]' = IF forwarding[p][p] = commit THEN commit ELSE abort
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, forwarding, alive>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = waiting
    /\ ~coordAlive
    /\ \A r \in participants : ~broadcastSent[r]
    /\ \A r \in participants :
          ( ~alive[r] ) => \A s \in participants :
                forwarding[r][s] = notsent
    /\ decision[p]' = abort
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, forwarding, alive>>

Die(p) ==
    /\ alive[p]
    /\ alive[p]' = FALSE
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, broadcastSent, decision, forwarding>>

(* ---------------------------------------------------------------------- *)
(* Base actions for coordinator (simplified from ACP-SB) *)

CoordRequestBroadcast ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : broadcastSent[p] = FALSE
    /\ broadcastSent' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    coordDecision, decision, forwarding, alive>>

CoordCollectVotes ==
    /\ coordAlive
    /\ \A p \in participants : voteSent[p]
    /\ coordDecision' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<votes, voteSent, coordAlive, coordFaulty,
                    broadcastSent, decision, forwarding, alive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<votes, voteSent, coordDecision, broadcastSent,
                    decision, forwarding, alive>>

(* ---------------------------------------------------------------------- *)
(* Participant actions *)

SendVote(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ votes' = [votes EXCEPT ![p] = yes] \* (for simplicity, always vote yes)
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    broadcastSent, decision, forwarding, alive>>

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ votes = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> waiting]
    /\ alive = [p \in participants |-> TRUE]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromPeer(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordRequestBroadcast
    \/ CoordCollectVotes
    \/ CoordDie

(* ---------------------------------------------------------------------- *)
(* Specification *)

SpecNB == Init /\ [][Next]_<<votes, voteSent, coordAlive, coordFaulty,
                           coordDecision, broadcastSent, decision,
                           forwarding, alive>>

(* ---------------------------------------------------------------------- *)
(* Type invariant (captures all variable domains) *)

TypeInvNB ==
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ decision \in [participants -> ParticipantState]
    /\ alive \in [participants -> BOOLEAN]
    /\ forwarding \in [participants -> [participants -> ForwardStatus]]

=============================================================================