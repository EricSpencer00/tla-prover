---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive,          \* BOOLEAN – coordinator is up
    coordFaulty,         \* BOOLEAN – coordinator has crashed
    coordDecision,       \* {commit, abort, undecided}
    coordState,          \* {waiting, commit, abort}
    coordBroadcast,      \* SUBSET participants – to whom the decision has been sent
    participantAlive,    \* SUBSET participants – participants that are up
    participantFaulty,   \* SUBSET participants – participants that have crashed
    participantDecision, \* [participants -> {commit, abort, undecided}]
    forwarding           \* [participants -> [participants -> {commit, abort, notsent}]]

vars == <<coordAlive, coordFaulty, coordDecision, coordState,
          coordBroadcast, participantAlive, participantFaulty,
          participantDecision, forwarding>>

(*---------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordState = waiting
    /\ coordBroadcast = {}
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

(*---------------------------------------------------------------------*)
(* Participant actions *)

PreDecideFromCoord(p) ==
    /\ p \in participantAlive
    /\ p \in coordBroadcast
    /\ forwarding[p][p] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  participantAlive, participantFaulty, participantDecision>>

PreDecideFromFwd(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ \E r \in participants :
          /\ forwarding[r][p] # notsent
          /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[r][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  participantAlive, participantFaulty, participantDecision>>

Forward(p,q) ==
    /\ p \in participantAlive
    /\ q \in participants \ {p}
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  participantAlive, participantFaulty, participantDecision>>

Decide(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] # notsent
    /\ \A q \in participants \ {p} : forwarding[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  participantAlive, participantFaulty, forwarding>>

AbortTimeout(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ (coordFaulty \/ ~coordAlive)
    /\ \A a \in participantAlive : forwarding[a][a] = notsent
    /\ \A r \in participants \ participantAlive :
          \A a \in participantAlive : forwarding[r][a] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  participantAlive, participantFaulty, forwarding>>

ParticipantDie(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordState,
                  coordBroadcast, participantDecision, forwarding>>

(*---------------------------------------------------------------------*)
(* Coordinator actions (only crash is modelled; others are omitted) *)

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordState, coordBroadcast,
                  participantAlive, participantFaulty,
                  participantDecision, forwarding>>

(*---------------------------------------------------------------------*)
(* The overall step relation *)

Next ==
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordDie

(*---------------------------------------------------------------------*)
(* Type invariant *)

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordState \in {waiting, commit, abort}
    /\ coordBroadcast \subseteq participants
    /\ participantAlive \subseteq participants
    /\ participantFaulty = participants \ participantAlive
    /\ participantDecision \in [participants -> {commit, abort, undecided}]
    /\ forwarding \in [participants -> [participants -> {commit, abort, notsent}]]

(*---------------------------------------------------------------------*)
(* Specification *)

SpecNB == Init /\ [][Next]_vars

====