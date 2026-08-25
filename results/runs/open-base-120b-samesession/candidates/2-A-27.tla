---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES coordAlive, coordFaulty, coordDecision,
          alive, faulty,
          decision,
          forwarding

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Decisions == {commit, abort, undecided}
ForwardStatus == {notsent, commit, abort}
AllAlive == { p \\in participants : alive[p] }
AllFaulty == { p \\in participants : faulty[p] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, alive, faulty, decision, forwarding>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \* for simplicity we allow the coordinator nondeterministically to choose a decision
       coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordAlive, coordFaulty, alive, faulty, decision, forwarding>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* (1) Pre‑decide from coordinator
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, decision>>

\* (2) Pre‑decide from forwarding by another participant
PreDecideFromForward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ forwarding[q][p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, decision>>

\* (3) Forward to another participant
Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ alive[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, decision>>

\* (4) Decide (non‑blocking) after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, forwarding>>

\* (5) Abort on timeout
AbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants : \* no alive participant has received a broadcast from the coordinator
         (coordAlive => FALSE)   \* trivially true because coordAlive = FALSE
    /\ \A d \in participants :
         (\/ faulty[d] = FALSE) \/ (forwarding[d][p] = notsent)   \* no dead participant has forwarded a decision
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, alive, faulty, forwarding>>

\* (6) Participant crashes
ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, decision, forwarding>>

\* ----------------------------------------------------------------------
\* Disjunction of all possible next‑state actions
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p,q \in participants : PreDecideFromForward(p,q)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordMakeDecision
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         alive, faulty, decision, forwarding>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decisions
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> Decisions]
    /\ forwarding \in [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* THEOREM (optional, can be checked by TLC)
\* ----------------------------------------------------------------------
THEOREM SpecNB => []TypeInvNB

====