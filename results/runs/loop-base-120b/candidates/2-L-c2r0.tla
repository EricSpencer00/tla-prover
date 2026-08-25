---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no, undecided,      \* vote values
    commit, abort,           \* final decision values
    waiting,                 \* auxiliary constant (not used directly)
    notsent                  \* forwarding status for “not sent”

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff the coordinator is alive
    coordFaulty,         \* TRUE iff the coordinator has crashed (faulty)
    coordDecision,       \* {commit, abort, undecided}
    coordSent,           \* SUBSET participants – those that have already been sent the decision by the coordinator
    partAlive,           \* [participants -> BOOLEAN] – participant aliveness
    partFaulty,          \* [participants -> BOOLEAN] – participant faulty flag
    vote,                \* [participants -> {yes,no,undecided}]
    voteSent,            \* [participants -> BOOLEAN] – has the participant sent its vote?
    preDecision,         \* [participants -> {commit, abort, undecided}] – decision stored in the forwarding table (own entry)
    forwardStatus,       \* [participants -> [participants -> {notsent, commit, abort}]]
    decision             \* [participants -> {commit, abort, undecided}] – final decision of a participant

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, coordSent,
           partAlive, partFaulty, vote, voteSent,
           preDecision, forwardStatus, decision >>

AllParticipants == participants

AliveParticipants == { p \\in participants : partAlive[p] }

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordSent \subseteq participants
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ preDecision \in [participants -> {commit, abort, undecided}]
    /\ forwardStatus \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decision \in [participants -> {commit, abort, undecided}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = {}
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ preDecision = [p \in participants |-> undecided]
    /\ forwardStatus = [i \in participants |-> [j \in participants |-> notsent]]
    /\ decision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent = {}
    /\ UNCHANGED <<coordFaulty, vote, voteSent, preDecision,
                    forwardStatus, decision, partAlive, partFaulty>>

CoordReceiveVote(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ voteSent[p]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordSent, vote, voteSent, preDecision,
                    forwardStatus, decision, partAlive, partFaulty>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants :
          (partAlive[p] => voteSent[p])
    /\ coordDecision' = 
          IF \A p \in participants : (partAlive[p] => vote[p] = yes)
          THEN commit
          ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, vote,
                    voteSent, preDecision, forwardStatus,
                    decision, partAlive, partFaulty>>

CoordBroadcastStep ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
         (p \notin coordSent)
    /\ LET p == Choose({ q \in participants : q \notin coordSent })
       IN /\ coordSent' = coordSent \cup {p}
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                        vote, voteSent, preDecision,
                        forwardStatus, decision, partAlive, partFaulty>>
    /\ UNCHANGED <<>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSent, vote, voteSent,
                  preDecision, forwardStatus, decision,
                  partAlive, partFaulty>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ ~voteSent[p]
    /\ vote[p]' \in {yes, no}
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  partAlive, partFaulty, preDecision,
                  forwardStatus, decision, vote>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, preDecision,
                  forwardStatus, decision>>

\* Pre‑decide from coordinator broadcast
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ preDecision[p] = undecided
    /\ p \in coordSent
    /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, forwardStatus, decision,
                  partAlive, partFaulty, vote>>

\* Pre‑decide from forwarding of another participant
PreDecideFromForward(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ preDecision[p] = undecided
    /\ \E q \in participants :
         forwardStatus[q][p] \in {commit, abort}
    /\ LET d == 
          IF \E q \in participants : forwardStatus[q][p] = commit
          THEN commit
          ELSE abort
       IN preDecision' = [preDecision EXCEPT ![p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, forwardStatus, decision,
                  partAlive, partFaulty, vote>>

\* Forwarding action
Forward(p, q) ==
    /\ p \in participants /\ q \in participants
    /\ partAlive[p] /\ partAlive[q]
    /\ preDecision[p] \in {commit, abort}
    /\ forwardStatus[p][q] = notsent
    /\ forwardStatus' = [forwardStatus EXCEPT ![p][q] = preDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, preDecision, decision,
                  partAlive, partFaulty, vote>>

\* Decide after having forwarded to everybody
Decide(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ decision[p] = undecided
    /\ preDecision[p] \in {commit, abort}
    /\ \A q \in participants :
         forwardStatus[p][q] = preDecision[p] \/ q = p
    /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, preDecision, forwardStatus,
                  partAlive, partFaulty, vote>>

\* Abort on timeout (when coordinator dead and no information circulating)
AbortOnTimeout(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : q \notin coordSent
    /\ \A r \in participants :
         \A s \in participants :
            forwardStatus[r][s] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                  vote, voteSent, preDecision, forwardStatus,
                  partAlive, partFaulty, vote>>

\* ----------------------------------------------------------------------
\* Combined Next action
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordSendRequest
    \/ CoordMakeDecision
    \/ CoordBroadcastStep
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant (type correctness)
\* ----------------------------------------------------------------------
THEOREM TypeInvNBIsInvariant == SpecNB => []TypeInvNB

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The .cfg file expects the following names:
\*   SPECIFICATION  == SpecNB
\*   INVARIANTS     == TypeInvNB
\*   CONSTANTS      == participants, yes, no, undecided, commit,
\*                     abort, waiting, notsent
\* These are already declared above.
=============================================================================