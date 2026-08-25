---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants,   \* set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,          \* TRUE if coordinator is alive
    coordFaulty,         \* TRUE if coordinator has crashed (faulty)
    coordDecision,       \* decision of the coordinator (commit/abort/undecided)
    alive,               \* subset of participants that are currently alive
    faulty,              \* subset of participants that have crashed
    vote,                \* [p \in participants |-> yes \/ no \/ undecided]
    decision,            \* [p \in participants |-> undecided \/ commit \/ abort]
    pre,                 \* forwarding table:
                         \*   [p \in participants |-> [q \in participants |-> notsent \/ commit \/ abort]]
    forwarded            \* [p \in participants |-> SUBSET participants]  (* participants to which p has already forwarded *)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB == 
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ alive \subseteq participants
    /\ faulty = participants \setminus alive
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ pre \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ forwarded \in [participants -> SUBSET participants]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ alive = participants
    /\ faulty = {}
    /\ vote = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ pre = [p \in participants |-> [q \in participants |-> notsent]]
    /\ forwarded = [p \in participants |-> {}]

\* ----------------------------------------------------------------------
\* Coordinator actions (simplified)
\* ----------------------------------------------------------------------
\* Coordinator may decide (based on collected votes) – details omitted.
DecideCoord == 
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \* for simplicity we allow nondeterministic decision
       \/ coordDecision' = commit
       \/ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, alive, faulty, vote, decision, pre, forwarded>>

\* Coordinator can crash
CrashCoord == 
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, alive, faulty, vote, decision, pre, forwarded>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* 1. Pre‑decide from coordinator broadcast
PreDecideFromCoord(p) == 
    /\ p \in alive
    /\ decision[p] = undecided
    /\ pre[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ pre' = [pre EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, vote, decision, forwarded>>

\* 2. Pre‑decide from forwarding by another participant
PreDecideFromForward(p) == 
    /\ p \in alive
    /\ decision[p] = undecided
    /\ pre[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ pre[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} : 
               \E q \in participants : q # p /\ pre[q][p] = d
       IN pre' = [pre EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, vote, decision, forwarded>>

\* 3. Forward decision to another participant
Forward(p,q) == 
    /\ p \in alive
    /\ q \in alive
    /\ q # p
    /\ pre[p][p] \in {commit, abort}
    /\ q \notin forwarded[p]
    /\ pre[p][q] = notsent
    /\ pre' = [pre EXCEPT ![p][q] = pre[p][p]]
    /\ forwarded' = [forwarded EXCEPT ![p] = forwarded[p] \cup {q}]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, vote, decision>>

\* 4. Decide locally after having forwarded to everyone
Decide(p) == 
    /\ p \in alive
    /\ decision[p] = undecided
    /\ pre[p][p] \in {commit, abort}
    /\ forwarded[p] = participants \ {p}
    /\ decision' = [decision EXCEPT ![p] = pre[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, vote, pre, forwarded>>

\* 5. Abort on timeout (coordinator dead and no information propagated)
AbortTimeout(p) == 
    /\ p \in alive
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in alive : pre[q][q] = notsent
    /\ \A q \in participants \ alive : 
          \A r \in alive : pre[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, vote, pre, forwarded>>

\* 6. Participant crashes
Crash(p) == 
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, vote, decision, pre, forwarded>>

\* ----------------------------------------------------------------------
\* Composite Next action
\* ----------------------------------------------------------------------
Next == 
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Crash(p)
    \/ CrashCoord
    \/ DecideCoord

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         alive, faulty, vote, decision, pre, forwarded>>

\* ----------------------------------------------------------------------
\* Invariant (type safety)
\* ----------------------------------------------------------------------
INVARIANT TypeInvNB

====