---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (as required by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES coordAlive,            \* TRUE iff the coordinator is alive
          coordDecision,        \* the decision made by the coordinator (commit or abort)
          coordBroadcasted,     \* mapping participant -> BOOLEAN, true if coordinator has sent the decision to that participant
          pAlive,               \* set of alive participants
          forward,              \* forwarding table: [p ∈ participants |-> [q ∈ participants |-> notsent, commit, abort]]
          pDecision             \* final decision of each participant (undecided, commit, abort)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all participants
Participants == participants

\* The set of possible decision values (including the special value none)
DecisionValues == {commit, abort}

\* The set of values that can appear in a forwarding entry
FwdValues == {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDecision \in DecisionValues
    /\ coordBroadcasted = [p \in participants |-> FALSE]
    /\ pAlive = participants
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ pDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordMakeDecision(d) ==
    /\ d \in DecisionValues
    /\ coordDecision' = d
    /\ UNCHANGED <<coordAlive, coordBroadcasted, pAlive, forward, pDecision>>

CoordBroadcast(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision \in DecisionValues
    /\ coordBroadcasted[p] = FALSE
    /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, pAlive, forward, pDecision>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDecision, coordBroadcasted, pAlive, forward, pDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* 1. Pre‑decide from coordinator
PreDecFromCoord(p) ==
    /\ p \in participants
    /\ p \in pAlive
    /\ forward[p][p] = notsent
    /\ coordBroadcasted[p] = TRUE
    /\ forward' = [forward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, pAlive, pDecision>>

\* 2. Pre‑decide from another participant's forwarding
PreDecFromFwd(p) ==
    /\ p \in participants
    /\ p \in pAlive
    /\ forward[p][p] = notsent
    /\ \E q \in participants :
           forward[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
               \E q \in participants : forward[q][p] = d
       IN forward' = [forward EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, pAlive, pDecision>>

\* 3. Forward to another participant
Forward(p, r) ==
    /\ p \in participants
    /\ r \in participants
    /\ p \in pAlive
    /\ forward[p][p] \in {commit, abort}
    /\ forward[p][r] = notsent
    /\ forward' = [forward EXCEPT ![p][r] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, pAlive, pDecision>>

\* 4. Decide after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ p \in pAlive
    /\ forward[p][p] \in {commit, abort}
    /\ \A r \in participants : forward[p][r] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, pAlive, forward>>

\* 5. Abort on timeout (no coordinator, no broadcast, no forwarding from dead)
AbortTimeout(p) ==
    /\ p \in participants
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : coordBroadcasted[q] = FALSE
    /\ \A d \in participants \\ pAlive :
         \A r \in pAlive : forward[d][r] = notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, pAlive, forward>>

\* 6. Participant crash
ParticipantDie(p) ==
    /\ p \in participants
    /\ p \in pAlive
    /\ pAlive' = pAlive \ {p}
    /\ UNCHANGED <<coordAlive, coordDecision, coordBroadcasted, forward, pDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E d \in DecisionValues : CoordMakeDecision(d)
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PreDecFromCoord(p)
    \/ \E p \in participants : PreDecFromFwd(p)
    \/ \E p, r \in participants : Forward(p, r)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordDecision, coordBroadcasted,
                         pAlive, forward, pDecision>>

\* ----------------------------------------------------------------------
\* Type invariant (as required)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in DecisionValues
    /\ coordBroadcasted \in [participants -> BOOLEAN]
    /\ pAlive \subseteq participants
    /\ forward \in [participants -> [participants -> FwdValues]]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

=============================================================================