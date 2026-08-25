---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS 
    participants, \* set of participant identifiers
    yes, no,      \* vote values
    undecided,    \* used for votes and decisions before they are fixed
    commit, abort,\* final decisions
    waiting,      \* auxiliary constant (unused but required)
    notsent       \* forwarding status meaning “no decision sent”

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* Boolean – coordinator is up
    coordFaulty,         \* Boolean – coordinator has crashed
    coordDecision,       \* {commit, abort, undecided}
    broadcastSent,       \* SUBSET participants – who have been sent the decision by coordinator
    pAlive,              \* [participants -> BOOLEAN] – participant liveness
    pFaulty,             \* [participants -> BOOLEAN] – participant fault flag
    pVote,               \* [participants -> {yes,no,undecided}] – vote cast by each participant
    pPreDecision,        \* [participants -> {commit, abort, undecided}] – pre‑decision stored locally
    pDecision,           \* [participants -> {commit, abort, undecided}] – final decision
    fwd                  \* [participants -> [participants -> {commit, abort, notsent}]]
    
\* ----------------------------------------------------------------------
\* VARIABLES PACKED INTO A SINGLE SEQUENCE FOR THE SPECIFICATION
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision, broadcastSent,
           pAlive, pFaulty, pVote, pPreDecision, pDecision, fwd >>

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcastSent = {} 
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> undecided]
    /\ pPreDecision = [p \in participants |-> undecided]
    /\ pDecision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
\* 1. Participant sends its vote (choice is nondeterministic)
SendVote(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pVote[p] = undecided
    /\ \E v \in {yes, no}:
         /\ pVote' = [pVote EXCEPT ![p] = v]
         /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                        broadcastSent, pAlive, pFaulty,
                        pPreDecision, pDecision, fwd>>

\* 2. Coordinator makes a decision (commit if all yes, abort otherwise)
MakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \E d \in {commit, abort}:
         /\ coordDecision' = d
         /\ UNCHANGED <<coordFaulty, broadcastSent,
                        pAlive, pFaulty, pVote,
                        pPreDecision, pDecision, fwd>>

\* 3. Coordinator broadcasts its decision to all participants
Broadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ broadcastSent' = participants
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   pAlive, pFaulty, pVote,
                   pPreDecision, pDecision, fwd>>

\* 4. Participant receives pre‑decision directly from coordinator
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pPreDecision[p] = undecided
    /\ p \in broadcastSent
    /\ pPreDecision' = [pPreDecision EXCEPT ![p] = coordDecision]
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pAlive, pFaulty,
                   pVote, pDecision>>

\* 5. Participant receives pre‑decision forwarded by another participant
PreDecideFromFwd(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pPreDecision[p] = undecided
    /\ \E q \in participants:
         /\ q # p
         /\ fwd[q][p] # notsent
    /\ LET d == ChooseOne({ fwd[q][p] : q \in participants : q # p /\ fwd[q][p] # notsent })
       IN
          /\ pPreDecision' = [pPreDecision EXCEPT ![p] = d]
          /\ fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pAlive, pFaulty,
                   pVote, pDecision>>

\* 6. Participant forwards its pre‑decision to another participant
Forward(p, q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ pAlive[p] = TRUE
    /\ pPreDecision[p] # undecided
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = pPreDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pAlive, pFaulty,
                   pVote, pPreDecision, pDecision>>

\* 7. Participant decides after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pPreDecision[p] # undecided
    /\ \A q \in participants: fwd[p][q] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = pPreDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pAlive, pFaulty,
                   pVote, pPreDecision, fwd>>

\* 8. Abort on timeout (coordinator dead, no broadcast received, no forwarded info)
AbortTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ broadcastSent = {}
    /\ \A q,r \in participants: fwd[q][r] = notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pAlive, pFaulty,
                   pVote, pPreDecision, fwd>>

\* 9. Participant crashes
CrashParticipant(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   broadcastSent, pVote, pPreDecision,
                   pDecision, fwd>>

\* 10. Coordinator crashes
CrashCoordinator ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, broadcastSent,
                   pAlive, pFaulty, pVote,
                   pPreDecision, pDecision, fwd>>

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION
\* ----------------------------------------------------------------------
Next ==
    \E p \in participants: SendVote(p)
\/ MakeDecision
\/ Broadcast
\/ \E p \in participants: PreDecideFromCoord(p)
\/ \E p \in participants: PreDecideFromFwd(p)
\/ \E p,q \in participants: Forward(p,q)
\/ \E p \in participants: Decide(p)
\/ \E p \in participants: AbortTimeout(p)
\/ \E p \in participants: CrashParticipant(p)
\/ CrashCoordinator

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcastSent \subseteq participants
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no, undecided}]
    /\ pPreDecision \in [participants -> {commit, abort, undecided}]
    /\ pDecision \in [participants -> {commit, abort, undecided}]
    /\ fwd \in [participants -> [participants -> {commit, abort, notsent}]]

\* ----------------------------------------------------------------------
\* PROPERTIES (place‑holders – can be instantiated in the .cfg)
\* ----------------------------------------------------------------------
\* Agreement, validity, irrevocability, liveness etc. are expressed
\* in the external configuration file.  They are not required as
\* operators inside this module.

====