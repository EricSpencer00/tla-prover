---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision,
         votes, alive, faulty, decisions, forward

(* ------------------------------------------------------------------------ *)
(* Type invariant                                                            *)
(* ------------------------------------------------------------------------ *)
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {commit, abort, waiting}
  /\ votes \in [participants -> {yes, no}]
  /\ alive \in SUBSET participants
  /\ faulty \in SUBSET participants
  /\ decisions \in [participants -> {undecided, commit, abort}]
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

(* ------------------------------------------------------------------------ *)
(* Initial state                                                             *)
(* ------------------------------------------------------------------------ *)
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = waiting
  /\ votes = [p \in participants |-> yes]      \* initial vote is irrelevant; will be set by participants
  /\ alive = participants
  /\ faulty = {}
  /\ decisions = [p \in participants |-> undecided]
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

(* ------------------------------------------------------------------------ *)
(* Coordinator actions                                                       *)
(* ------------------------------------------------------------------------ *)

CoordMakeDecision ==
  /\ coordAlive
  /\ coordDecision = waiting
  /\ coordDecision' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, votes, alive, faulty, decisions, forward>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, votes, alive, faulty, decisions, forward>>

(* ------------------------------------------------------------------------ *)
(* Participant actions                                                       *)
(* ------------------------------------------------------------------------ *)

SendVote(p) ==
  /\ p \in alive
  /\ votes' = [votes EXCEPT ![p] = CHOOSE v \in {yes,no}: TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, decisions, forward>>

PreDecideFromCoord(p) ==
  /\ p \in alive
  /\ forward[p][p] = notsent
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, alive, faulty, decisions>>

PreDecideFromFwd(p) ==
  /\ p \in alive
  /\ forward[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ forward[q][p] # notsent
        /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, alive, faulty, decisions>>

Forward(p,q) ==
  /\ p \in alive
  /\ q \in participants
  /\ p # q
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, alive, faulty, decisions>>

Decide(p) ==
  /\ p \in alive
  /\ forward[p][p] # notsent
  /\ \A q \in participants : forward[p][q] # notsent
  /\ decisions' = [decisions EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, alive, faulty, forward>>

AbortTimeout(p) ==
  /\ p \in alive
  /\ decisions[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants :
        ~(q \in alive) \/ forward[q][p] = notsent          \* no alive participant has received a broadcast
  /\ \A d \in participants :
        ~(d \in faulty) \/ \A r \in participants : forward[d][r] = notsent
  /\ decisions' = [decisions EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, alive, faulty, forward>>

ParticipantDie(p) ==
  /\ p \in alive
  /\ alive' = alive \ {p}
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, decisions, forward>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------ *)

Next ==
  \/ \E p \in participants : SendVote(p)
  \/ CoordMakeDecision
  \/ CoordDie
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants : PreDecideFromFwd(p)
  \/ \E p \in participants : \E q \in participants : Forward(p,q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortTimeout(p)
  \/ \E p \in participants : ParticipantDie(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------ *)

SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                     votes, alive, faulty, decisions, forward>>

====