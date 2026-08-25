---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* --------------------------------------------------------------------- *)
(*  State variables                                                    *)
(* --------------------------------------------------------------------- *)

VARIABLES
    coordAlive,          \* BOOLEAN  – is the coordinator up?
    coordFaulty,         \* BOOLEAN  – has the coordinator crashed?
    coordDecision,       \* {commit, abort, undecided}
    coordBroadcasted,    \* [participants -> BOOLEAN]  – broadcast sent to each participant?
    votes,               \* [participants -> VoteVal]   – vote cast by each participant
    voteSent,            \* [participants -> BOOLEAN]  – has a vote been sent?
    participantAlive,    \* [participants -> BOOLEAN]  – is a participant up?
    participantFaulty,   \* [participants -> BOOLEAN]  – has a participant crashed?
    preDecision,         \* [participants -> {commit, abort, undecided}]
    decision,            \* [participants -> {commit, abort, undecided}]
    forward              \* [participants -> [participants -> {commit, abort, notsent}]]

(* auxiliary set for vote values *)
VoteVal == {yes, no, none}

(* --------------------------------------------------------------------- *)
(*  Initial state                                                       *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = [p \in participants |-> FALSE]
    /\ votes = [p \in participants |-> none]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ preDecision = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

(* --------------------------------------------------------------------- *)
(*  Actions                                                             *)
(* --------------------------------------------------------------------- *)

ParticipantSendVote(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ LET v == CHOOSE vv \in {yes, no} : TRUE IN
       /\ votes' = [votes EXCEPT ![p] = v]
       /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  coordBroadcasted, participantAlive,
                  participantFaulty, preDecision, decision, forward>>

CoordinatorMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: voteSent[p]
    /\ coordDecision' = IF \A p \in participants: votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  preDecision, decision, forward>>

CoordinatorBroadcast ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ coordBroadcasted' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  votes, voteSent, participantAlive, participantFaulty,
                  preDecision, decision, forward>>

PreDecFromCoord(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ preDecision[p] = undecided
    /\ coordBroadcasted[p]
    /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  decision, forward>>

PreDecFromForward(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ preDecision[p] = undecided
    /\ \E q \in participants: forward[q][p] # notsent
    /\ LET d == IF forward[CHOOSE q \in participants:
                         forward[q][p] # notsent][p] = commit
                 THEN commit
                 ELSE abort
       IN preDecision' = [preDecision EXCEPT ![p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  decision, forward>>

Forward(p, q) ==
    /\ p \in participants /\ q \in participants
    /\ participantAlive[p]
    /\ preDecision[p] \in {commit, abort}
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = preDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  preDecision, decision>>

Decide(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants: forward[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  preDecision, forward>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants: preDecision[q] = undecided
    /\ \A q \in participants: \A r \in participants: forward[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, participantAlive, participantFaulty,
                  preDecision, forward>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                  votes, voteSent, preDecision, decision, forward>>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcasted, votes, voteSent,
                  participantAlive, participantFaulty, preDecision, decision, forward>>

(* --------------------------------------------------------------------- *)
(*  Next-state relation                                                  *)
(* --------------------------------------------------------------------- *)

Next ==
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ CoordinatorMakeDecision
    \/ CoordinatorBroadcast
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p \in participants: PreDecFromForward(p)
    \/ \E p \in participants: \E q \in participants: Forward(p, q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordinatorDie

(* --------------------------------------------------------------------- *)
(*  Specification                                                       *)
(* --------------------------------------------------------------------- *)

vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcasted,
          votes, voteSent, participantAlive, participantFaulty,
          preDecision, decision, forward>>

SpecNB == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*  Type invariant                                                       *)
(* --------------------------------------------------------------------- *)

TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcasted \in [participants -> BOOLEAN]
    /\ votes \in [participants -> VoteVal]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ preDecision \in [participants -> {commit, abort, undecided}]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ forward \in [participants -> [participants -> {commit, abort, notsent}]]

====