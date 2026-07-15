---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    participants,    \* Set of participant identifiers
    yes, no,         \* Vote values
    undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Votes    == {yes, no}
Decisions == {commit, abort}
FwdVals  == {commit, abort, notsent}
Status   == {"alive", "faulty"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    vote,            \* [p \in participants -> Votes]   : each participant's vote
    status,          \* [p \in participants -> Status]  : alive or faulty
    decision,        \* [p \in participants -> {"undecided", "commit", "abort"}]
    forward,         \* [p \in participants -> [q \in participants -> FwdVals]]
    coordAlive,      \* Boolean indicating if coordinator is alive
    coordDecision,   \* {"none", "commit", "abort"}  (none = not yet decided)
    coordBroadcast   \* Subset of participants that have already been sent the decision
                 
\* A convenience to denote the set of alive participants
AliveParts == { p \in participants : status[p] = "alive" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote = [p \in participants |-> yes]               \* initially all vote yes; nondeterministic voting will be modeled by actions
    /\ status = [p \in participants |-> "alive"]
    /\ decision = [p \in participants |-> "undecided"]
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ coordBroadcast = {}

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from the simple broadcast protocol)
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ TRUE   \* (no state change; represents the event of sending request)

CoordReceiveVote(p) ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ p \in participants
    /\ status[p] = "alive"
    /\ vote[p] \in Votes
    /\ TRUE   \* (no state change; votes are already stored in variable vote)

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ \E v \in {commit, abort} : 
          /\ v = "commit" => \A p \in participants : vote[p] = yes
          /\ v = "abort"  => \E p \in participants : vote[p] = no
    /\ coordDecision' = 
          IF \A p \in participants : vote[p] = yes THEN "commit" ELSE "abort"
    /\ UNCHANGED <<vote, status, decision, forward, coordAlive, coordBroadcast>>

CoordBroadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision # "none"
    /\ \E p \in participants : p \notin coordBroadcast
    /\ LET newP == CHOOSE q \in participants : q \notin coordBroadcast IN
       /\ coordBroadcast' = coordBroadcast \cup {newP}
       /\ forward' = [forward EXCEPT ![newP][newP] = coordDecision]  \* store decision in its own entry (pre-decision)
    /\ UNCHANGED <<vote, status, decision, coordAlive, coordDecision>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<vote, status, decision, forward, coordDecision, coordBroadcast>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
VoteSend(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ TRUE   \* (vote already stored in variable vote, no state change)

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ forward[p][p] = notsent
    /\ p \in coordBroadcast
    /\ forward' = [forward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<vote, status, decision, coordAlive, coordDecision, coordBroadcast>>

PreDecideFromFwd(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ forward[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forward[q][p] # notsent
    /\ LET src == CHOOSE q \in participants :
                 q # p /\ forward[q][p] # notsent IN
       forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<vote, status, decision, coordAlive, coordDecision, coordBroadcast>>

Forward(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ forward[p][p] # notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forward[p][q] = notsent
    /\ LET tgt == CHOOSE q \in participants :
                 q # p /\ forward[p][q] = notsent IN
       forward' = [forward EXCEPT ![p][tgt] = forward[p][p]]
    /\ UNCHANGED <<vote, status, decision, coordAlive, coordDecision, coordBroadcast>>

Decide(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ forward[p][p] # notsent
    /\ \A q \in participants : q # p => forward[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = 
          IF forward[p][p] = commit THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<vote, status, forward, coordAlive, coordDecision, coordBroadcast>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ decision[p] = "undecided"
    /\ coordAlive = FALSE
    /\ \A q \in participants : forward[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<vote, status, forward, coordAlive, coordDecision, coordBroadcast>>

Die(p) ==
    /\ p \in participants
    /\ status[p] = "alive"
    /\ status' = [status EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<vote, decision, forward, coordAlive, coordDecision, coordBroadcast>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : VoteSend(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p \in participants : Forward(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordSendRequest
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<vote, status, decision, forward, coordAlive, coordDecision, coordBroadcast>>

\* ----------------------------------------------------------------------
\* Types for invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ vote \in [participants -> Votes]
    /\ status \in [participants -> Status]
    /\ decision \in [participants -> {"undecided", "commit", "abort"}]
    /\ forward \in [participants -> [participants -> FwdVals]]
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {"none", "commit", "abort"}
    /\ coordBroadcast \subseteq participants

\* ----------------------------------------------------------------------
\* Safety invariants (named as required)
\* ----------------------------------------------------------------------
AC1 == 
    \A p, q \in participants :
        (decision[p] = "commit") => (decision[q] = "commit" \/ decision[q] = "undecided")

AC2 ==
    \A p \in participants :
        (decision[p] = "commit") => \A q \in participants : vote[q] = yes

AC3 ==
    \A p \in participants :
        (decision[p] = "abort") => 
            ( \E q \in participants : vote[q] = no ) \/ 
            ( \E q \in participants : status[q] = "faulty" ) \/ 
            ( coordAlive = FALSE )

AC4 ==
    \A p \in participants :
        (decision[p] = "commit") => 
            [] (decision[p] = "commit")
        /\ (decision[p] = "abort") => 
            [] (decision[p] = "abort")

\* The reference .cfg expects a single invariant named TypeInvNB
TypeInvNB == 
    /\ TypeOK
    /\ AC1
    /\ AC2
    /\ AC3
    /\ AC4

\* ----------------------------------------------------------------------
\* Liveness property (for completeness, though not part of the required invariant)
\* ----------------------------------------------------------------------
ACP5 == 
    \A p \in participants :
        []<>( (status[p] = "faulty") \/ (decision[p] # "undecided") \/ (coordAlive = FALSE) )

=============================================================================