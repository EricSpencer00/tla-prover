---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*------------------------------*)
(* State variables *)
(*------------------------------*)
VARIABLES 
    coordAlive,            \* BOOLEAN  (TRUE = coordinator up)
    coordFaulty,           \* BOOLEAN  (TRUE = coordinator has crashed)
    coordDecision,         \* {undecided, commit, abort}
    broadcastSet,          \* SUBSET participants (participants that have already received the decision directly from the coordinator)
    votesRecvd,            \* SUBSET participants (votes that have been received by the coordinator)

    vote,                  \* [participants -> {yes,no}]
    voteSent,              \* [participants -> BOOLEAN]   (TRUE when the participant has already sent its vote)

    participantAlive,      \* [participants -> BOOLEAN]   (TRUE = participant up)
    participantFaulty,     \* [participants -> BOOLEAN]   (TRUE = participant has crashed)

    fwd,                   \* [participants -> [participants -> {notsent, commit, abort}]]
                            \* fwd[p][q] = what p has forwarded to q (or notsent)
    decision               \* [participants -> {undecided, commit, abort}]

vars == << coordAlive, coordFaulty, coordDecision, broadcastSet, votesRecvd,
           vote, voteSent,
           participantAlive, participantFaulty,
           fwd, decision >>

(*------------------------------*)
(* Initial state *)
(*------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcastSet = {}
    /\ votesRecvd = {}
    /\ vote = [p \in participants |-> yes]    \* initially may be any, nondeterminism introduced later
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decision = [p \in participants |-> undecided]

(*------------------------------*)
(* Helper definitions *)
(*------------------------------*)
AllVotesReceived ==
    \A p \in participants : votesRecvd[p] = TRUE

AllAliveParticipants ==
    { p \in participants : participantAlive[p] }

AllForwarded(p) ==
    \A q \in participants : fwd[p][q] # notsent

PreDecision(p) ==
    fwd[p][p] # notsent

(*------------------------------*)
(* Coordinator actions *)
(*------------------------------*)
SendVote(p) ==
    /\ participantAlive[p]
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, participantAlive, participantFaulty,
                    fwd, decision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ participantAlive[p]
    /\ voteSent[p] = TRUE
    /\ votesRecvd' = votesRecvd \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    vote, voteSent, participantAlive, participantFaulty,
                    fwd, decision >>

MakeDecision ==
    /\ coordAlive
    /\ \A p \in participants : p \in votesRecvd \/ ~participantAlive[p]   \* all alive participants have voted
    /\ coordDecision' = 
          IF \A p \in participants : (p \in votesRecvd => vote[p] = yes)
          THEN commit
          ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, broadcastSet, votesRecvd,
                    vote, voteSent, participantAlive, participantFaulty,
                    fwd, decision >>

Broadcast(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin broadcastSet
    /\ broadcastSet' = broadcastSet \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, votesRecvd,
                    vote, voteSent, participantAlive, participantFaulty,
                    fwd, decision >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, broadcastSet, votesRecvd,
                    vote, voteSent, participantAlive, participantFaulty,
                    fwd, decision >>

(*------------------------------*)
(* Participant actions *)
(*------------------------------*)
PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ fwd[p][p] = notsent
    /\ p \in broadcastSet
    /\ coordDecision # undecided
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    participantAlive, participantFaulty,
                    decision >>

PreDecideFromFwd(p) ==
    /\ participantAlive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ fwd[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                 \E q \in participants : q # p /\ fwd[q][p] = d
        IN
       fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    participantAlive, participantFaulty,
                    decision >>

Forward(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ fwd[p][p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    participantAlive, participantFaulty,
                    decision >>

Decide(p) ==
    /\ participantAlive[p]
    /\ fwd[p][p] \in {commit, abort}
    /\ AllForwarded(p)
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    participantAlive, participantFaulty,
                    fwd >>

AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A r \in participants : r \notin broadcastSet   \* no alive participant has received a direct broadcast
    /\ \A q \in participants :
          ~participantAlive[q] => 
            \A r \in participants :
                participantAlive[r] => fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    participantAlive, participantFaulty,
                    fwd >>

PartDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, broadcastSet,
                    votesRecvd, vote, voteSent,
                    fwd, decision >>

(*------------------------------*)
(* Next-state relation *)
(*------------------------------*)
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : PartDie(p)

(*------------------------------*)
(* Type invariants *)
(*------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ broadcastSet \subseteq participants
    /\ votesRecvd \subseteq participants
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decision \in [participants -> {undecided, commit, abort}]

(*------------------------------*)
(* Specification *)
(*------------------------------*)
SpecNB ==
    Init /\ [][Next]_vars

(*------------------------------*)
(* Properties (place‑holders for model‑checker) *)
(*------------------------------*)
PROPERTY1 == TRUE   \* placeholder for safety AC1 etc.
PROPERTY2 == TRUE   \* placeholder for liveness AC5 etc.

====