---- MODULE ACP_NB ----
EXTENDS FiniteSets, TLC

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(***************************************************************************)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES
    coordAlive,            \* TRUE if the coordinator is up
    coordFaulty,           \* TRUE if the coordinator has crashed
    requestSent,           \* TRUE after the coordinator has sent the request
    decisionMade,          \* {commit, abort, notsent} – decision chosen by coord
    votes,                 \* [p \in participants |-> {yes,no,undecided}]
    decision,              \* [p \in participants |-> {undecided, commit, abort}]
    preDec,                \* [p \in participants |-> {commit, abort, notsent}]
    forward,               \* [p \in participants |-> [q \in participants |-> {notsent, commit, abort}]]
    participantAlive,      \* [p \in participants |-> BOOLEAN]
    participantFaulty      \* [p \in participants |-> BOOLEAN]

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
vars == <<coordAlive, coordFaulty, requestSent, decisionMade,
          votes, decision, preDec, forward,
          participantAlive, participantFaulty>>

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = FALSE
    /\ decisionMade = notsent
    /\ votes = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ preDec = [p \in participants |-> notsent]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]

(***************************************************************************)
(*  Coordinator actions                                                   *)
(***************************************************************************)
SendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<coordFaulty, decisionMade, votes, decision, preDec,
                   forward, participantAlive, participantFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ requestSent
    /\ p \in participants
    /\ votes[p] = undecided
    /\ \E v \in {yes, no}:
          /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   decision, preDec, forward, participantAlive, participantFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ requestSent
    /\ decisionMade = notsent
    /\ IF (\A p \in participants: votes[p] = yes)
          THEN decisionMade' = commit
          ELSE decisionMade' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, votes,
                   decision, preDec, forward, participantAlive, participantFaulty>>

Broadcast ==
    /\ coordAlive
    /\ decisionMade \in {commit, abort}
    /\ \E p \in participants: preDec[p] = notsent
    /\ preDec' = [preDec EXCEPT ![p] = decisionMade
                               FOR p \in participants]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, decision, forward, participantAlive, participantFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<requestSent, decisionMade, votes, decision,
                   preDec, forward, participantAlive, participantFaulty>>

(***************************************************************************)
(*  Participant actions                                                   *)
(***************************************************************************)
SendVote(p) ==
    /\ participantAlive[p]
    /\ votes[p] = undecided
    /\ \E v \in {yes, no}:
          /\ votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   decision, preDec, forward,
                   participantAlive, participantFaulty>>

PreDecFromCoord(p) ==
    /\ participantAlive[p]
    /\ preDec[p] = notsent
    /\ decisionMade \in {commit, abort}
    /\ preDec' = [preDec EXCEPT ![p] = decisionMade]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, decision, forward,
                   participantAlive, participantFaulty>>

PreDecFromForward(p,q) ==
    /\ participantAlive[p]
    /\ preDec[p] = notsent
    /\ forward[q][p] # notsent
    /\ preDec' = [preDec EXCEPT ![p] = forward[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, decision, forward,
                   participantAlive, participantFaulty>>

Forward(p,q) ==
    /\ participantAlive[p]
    /\ preDec[p] \in {commit, abort}
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, decision, preDec,
                   participantAlive, participantFaulty>>

Decide(p) ==
    /\ participantAlive[p]
    /\ preDec[p] \in {commit, abort}
    /\ \A q \in participants: forward[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, preDec, forward,
                   participantAlive, participantFaulty>>

AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A r \in participants: preDec[r] = notsent
    /\ \A d \in participants:
         /\ ~participantAlive[d]
         => \A r \in participants: forward[d][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, preDec, forward,
                   participantAlive, participantFaulty>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, decisionMade,
                   votes, decision, preDec, forward>>

(***************************************************************************)
(*  Next-state relation                                                   *)
(***************************************************************************)
Next ==
    \/ SendRequest
    \/ \E p \in participants: ReceiveVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p,q \in participants: PreDecFromForward(p,q)
    \/ \E p,q \in participants: Forward(p,q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
SpecNB ==
    Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant (safety)                                               *)
(***************************************************************************)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in BOOLEAN
    /\ decisionMade \in {commit, abort, notsent}
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ preDec \in [participants -> {commit, abort, notsent}]
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]

(***************************************************************************)
(*  Weak fairness assumptions (optional)                                  *)
(***************************************************************************)
\* We assume weak fairness for all progress actions except death.
\* The following definitions make the fairness assumptions explicit.
\* (The model checker can use them if desired.)

Fairness ==
    /\ WF_vars(SendRequest)
    /\ \A p \in participants: WF_vars(SendVote(p))
    /\ \A p \in participants: WF_vars(PreDecFromCoord(p))
    /\ \A p,q \in participants: WF_vars(PreDecFromForward(p,q))
    /\ \A p,q \in participants: WF_vars(Forward(p,q))
    /\ \A p \in participants: WF_vars(Decide(p))
    /\ \A p \in participants: WF_vars(AbortTimeout(p))

(***************************************************************************)
(*  The complete specification with fairness (if needed)                  *)
(***************************************************************************)
SpecNBWithFairness == SpecNB /\ Fairness

=============================================================================