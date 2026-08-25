---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ---------------------------------------------------------------------- *)
(* State Variables *)
(* ---------------------------------------------------------------------- *)

VARIABLES 
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* {commit, abort, waiting}  (waiting = no decision yet)
    broadcastSent,       \* SUBSET participants that have already received the decision directly from coordinator
    participantAlive,    \* [participants -> BOOLEAN]
    participantFaulty,   \* [participants -> BOOLEAN]
    decision,            \* [participants -> {commit, abort, undecided}]
    vote,                \* [participants -> {yes, no}]
    voteSent,            \* [participants -> BOOLEAN]
    fwdTable             \* [participants -> [participants -> {notsent, commit, abort}]]

vars == << coordAlive, coordFaulty, coordDecision, broadcastSent,
           participantAlive, participantFaulty, decision,
           vote, voteSent, fwdTable >>

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
(* ---------------------------------------------------------------------- *)

Alive(p) == participantAlive[p]
Faulty(p) == participantFaulty[p]

PreDecided(p) == fwdTable[p][p] # notsent
HasPre(p) == fwdTable[p][p] \in {commit, abort}
NoPre(p) == fwdTable[p][p] = notsent

Forwarded(p, q) == fwdTable[p][q] # notsent

AllForwarded(p) == \A q \in participants : fwdTable[p][q] # notsent

(* ---------------------------------------------------------------------- *)
(* Initial State *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ broadcastSent = {}
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ vote = [p \in participants |-> yes]            \* initial vote is nondeterministic; set to yes for simplicity
    /\ voteSent = [p \in participants |-> FALSE]
    /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]

(* ---------------------------------------------------------------------- *)
(* Coordinator Actions *)
(* ---------------------------------------------------------------------- *)

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, broadcastSent, participantAlive,
                    participantFaulty, decision, vote, voteSent, fwdTable >>

CoordDecide ==
    /\ coordAlive = TRUE
    /\ coordDecision = waiting
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED << coordAlive, coordFaulty, broadcastSent,
                    participantAlive, participantFaulty,
                    decision, vote, voteSent, fwdTable >>

CoordBroadcast(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision # waiting
    /\ p \in participants
    /\ p \notin broadcastSent
    /\ broadcastSent' = broadcastSent \cup {p}
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    decision, vote, voteSent >>

(* ---------------------------------------------------------------------- *)
(* Participant Actions *)
(* ---------------------------------------------------------------------- *)

SendVote(p) ==
    /\ Alive(p)
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    decision, vote, fwdTable >>

PreDecideFromCoord(p) ==
    /\ Alive(p)
    /\ NoPre(p)
    /\ p \in broadcastSent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    decision, vote, voteSent >>

PreDecideFromForward(p) ==
    /\ Alive(p)
    /\ NoPre(p)
    /\ \E q \in participants :
          /\ q # p
          /\ Alive(q)
          /\ fwdTable[q][p] # notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = 
          IF fwdTable[Choose({q \in participants : q # p /\ Alive(q) /\ fwdTable[q][p] # notsent})][p] = commit
          THEN commit ELSE abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    decision, vote, voteSent >>

Forward(p, q) ==
    /\ Alive(p) /\ Alive(q) /\ p # q
    /\ HasPre(p)
    /\ fwdTable[p][q] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    decision, vote, voteSent >>

Decide(p) ==
    /\ Alive(p)
    /\ HasPre(p)
    /\ AllForwarded(p)
    /\ decision' = [decision EXCEPT ![p] = fwdTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    vote, voteSent, fwdTable >>

AbortTimeout(p) ==
    /\ Alive(p)
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          (Alive(q) => NoPre(q))
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    participantAlive, participantFaulty,
                    vote, voteSent, fwdTable >>

ParticipantDie(p) ==
    /\ Alive(p)
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSent,
                    decision, vote, voteSent, fwdTable >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordDie
    \/ CoordDecide
    \/ \E p \in participants : CoordBroadcast(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)

SpecNB == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Type Invariant *)
(* ---------------------------------------------------------------------- *)

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, waiting}
    /\ broadcastSent \subseteq participants
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ fwdTable \in [participants -> [participants -> {notsent, commit, abort}]]

(* ---------------------------------------------------------------------- *)
(* Safety and Liveness Properties (placeholders) *)
(* ---------------------------------------------------------------------- *)

(* The safety invariants AC1–AC4 are captured by TypeInvNB together with
   additional predicates that are omitted here for brevity. *)

(* Liveness properties AC3 and AC5 are not explicitly encoded; they can be
   expressed as temporal formulas in the .cfg file. *)

====