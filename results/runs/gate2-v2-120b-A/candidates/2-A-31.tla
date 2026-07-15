---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

(*) -- constants (will be instantiated in the .cfg)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    \* --- Base protocol state ---
    coordAlive, coordFaulty, coordDecision,
    participantAlive, participantFaulty,
    participantVote, participantDecision,
    decisionSent,          \* mapping from participant to whether a broadcast from coordinator was sent
    \* --- Reliable broadcast state ---
    forwardTable           \* mapping: participant -> [dest -> {notsent, commit, abort}]

(* Type definitions for readability *)
ROLES == {"Coordinator", "Participant"}

PreDecisions == {"commit", "abort"}

(* ------------------------------------------------------------------------- *)
(* Initialization                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantVote   = [p \in participants |-> undecided]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ decisionSent = [p \in participants |-> FALSE]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

(* A participant has received a pre‑decision (either from coordinator or forwarding) *)
PreReceived(p) ==
    /\ participantAlive[p]
    /\ \/ forwardTable[p][p] = "commit"
       \/ forwardTable[p][p] = "abort"

(* The pre‑decision stored at p's own entry *)
PreDecision(p) ==
    IF forwardTable[p][p] = "commit" THEN "commit"
    ELSIF forwardTable[p][p] = "abort" THEN "abort"
    ELSE "none"

(* Whether p has already forwarded its pre‑decision to every other participant *)
AllForwarded(p) ==
    /\ participantAlive[p]
    /\ \A q \in participants \ {p} :
          forwardTable[p][q] = forwardTable[p][p]

(* ------------------------------------------------------------------------- *)
(* Actions                                                                   *)
(* ------------------------------------------------------------------------- *)

(* --- Coordinator actions (inherited from ACP‑SB) -------------------------- *)

SendRequest ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ participantVote' = [p \in participants |-> undecided]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantDecision, decisionSent, forwardTable>>

ReceiveVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantVote[p] = undecided
    /\ participantVote' = [participantVote EXCEPT ![p] = 
            IF Random() % 2 = 0 THEN yes ELSE no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantDecision, decisionSent, forwardTable>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ \A p \in participants : participantVote[p] # undecided
    /\ coordDecision' = IF \A p \in participants : participantVote[p] = yes
                         THEN "commit" ELSE "abort"
    /\ UNCHANGED <<coordAlive, coordFaulty,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   decisionSent, forwardTable>>

Broadcast ==
    /\ coordAlive
    /\ coordDecision # "none"
    /\ decisionSent' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   forwardTable>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   decisionSent, forwardTable>>

(* --- Participant base actions (send vote, abort on timeout from coordinator) --- *)

SendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantVote[p] = undecided
    /\ participantVote' = [participantVote EXCEPT ![p] = 
            IF Random() % 2 = 0 THEN yes ELSE no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantDecision, decisionSent, forwardTable>>

AbortOnCoordTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ ~\E q \in participants : decisionSent[q]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, decisionSent, forwardTable>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantVote, participantDecision,
                   decisionSent, forwardTable>>

(* --- New reliable‑broadcast actions --------------------------------------- *)

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~PreReceived(p)
    /\ decisionSent[p]
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = 
            IF coordDecision = "commit" THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   decisionSent>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~PreReceived(p)
    /\ \E q \in participants \ {p} :
          forwardTable[q][p] # notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = 
            IF \E q \in participants \ {p} : forwardTable[q][p] = "commit"
               THEN "commit"
               ELSE "abort"]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   decisionSent>>

Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ participantAlive[p]
    /\ PreReceived(p)
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, participantDecision,
                   decisionSent>>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ AllForwarded(p)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = PreDecision(p)]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   participantAlive, participantFaulty,
                   participantVote, decisionSent, forwardTable>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ \E p \in participants : AbortOnCoordTimeout(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p, q \in participants : p # q /\ Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ SendRequest
    \/ \E p \in participants : ReceiveVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie

(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         participantAlive, participantFaulty,
                         participantVote, participantDecision,
                         decisionSent, forwardTable>>

(* ------------------------------------------------------------------------- *)
(* Safety invariant (type correctness and protocol constraints)             *)
(* ------------------------------------------------------------------------- *)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"none", "commit", "abort"}
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes, no, undecided}]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ decisionSent \in [participants -> BOOLEAN]
    /\ forwardTable \in [participants -> [participants -> {notsent, "commit", "abort"}]]

(* ------------------------------------------------------------------------- *)
(* Theorem (optional)                                                         *)
(* ------------------------------------------------------------------------- *)
THEOREM SpecImpliesTypeInv == SpecNB => []TypeInvNB

====