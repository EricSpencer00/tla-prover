---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordDecision, broadcasted, participantsAlive, decision, fwd

vars == <<coordAlive, coordDecision, broadcasted, participantsAlive, decision, fwd>>

(*---------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ broadcasted = FALSE
    /\ participantsAlive = participants
    /\ decision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

(*---------------------------------------------------------------------*)
(* Coordinator actions *)

CoordDecide ==
    /\ coordAlive
    /\ ~broadcasted
    /\ coordDecision' \in {commit, abort}
    /\ broadcasted' = TRUE
    /\ UNCHANGED <<participantsAlive, decision, fwd>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, broadcasted, participantsAlive, decision, fwd>>

(*---------------------------------------------------------------------*)
(* Participant actions *)

PreDecideFromCoord(p) ==
    /\ p \in participantsAlive
    /\ coordAlive
    /\ broadcasted
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, broadcasted, participantsAlive, decision>>

Forward(p, q) ==
    /\ p \in participantsAlive
    /\ q \in participantsAlive
    /\ p # q
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordDecision, broadcasted, participantsAlive, decision>>

Decide(p) ==
    /\ p \in participantsAlive
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants : q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<coordAlive, coordDecision, broadcasted, participantsAlive, fwd>>

AbortTimeout(p) ==
    /\ p \in participantsAlive
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A a \in participantsAlive : fwd[a][a] = notsent
    /\ \A d \in participants \ participantsAlive :
          \A a \in participantsAlive : fwd[d][a] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, broadcasted, participantsAlive, fwd>>

ParticipantDie(p) ==
    /\ p \in participantsAlive
    /\ participantsAlive' = participantsAlive \ {p}
    /\ UNCHANGED <<coordAlive, coordDecision, broadcasted, decision, fwd>>

(*---------------------------------------------------------------------*)
(* Next-state relation *)

Next ==
    \/ CoordDecide
    \/ CoordDie
    \/ \E p \in participantsAlive : PreDecideFromCoord(p)
    \/ \E p \in participantsAlive : \E q \in participantsAlive : (p # q) /\ Forward(p, q)
    \/ \E p \in participantsAlive : Decide(p)
    \/ \E p \in participantsAlive : AbortTimeout(p)
    \/ \E p \in participantsAlive : ParticipantDie(p)

(*---------------------------------------------------------------------*)
(* Specification *)

SpecNB == Init /\ [] [Next]_vars

(*---------------------------------------------------------------------*)
(* Type invariant *)

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcasted \in BOOLEAN
    /\ participantsAlive \subseteq participants
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ fwd \in [participants -> [participants -> {commit, abort, notsent}]]

=============================================================================