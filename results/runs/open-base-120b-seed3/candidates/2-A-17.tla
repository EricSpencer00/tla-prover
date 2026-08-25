---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
VoteVals == {yes, no}
DecisionVals == {commit, abort}
ParticipantState == {undecided, commit, abort}
ForwardStatus == {notsent} \cup DecisionVals

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* DecisionVals \cup {undecided}
    coordBroadcasted,    \* SUBSET participants that have received the coordinator's broadcast
    vote,                \* [participants -> VoteVals]
    alive,               \* [participants -> BOOLEAN]
    faulty,              \* [participants -> BOOLEAN]
    decision,            \* [participants -> ParticipantState]
    preDec,              \* [participants -> DecisionVals \cup {none}]
    fwd                  \* [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllAliveParticipants == { p \in participants : alive[p] }
AllDeadParticipants  == participants \\ AllAliveParticipants

\* The set of participants that have already received a pre‑decision
HasPreDec(p) == preDec[p] # none

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = {}
    /\ vote = [p \in participants |-> yes]           \* default vote
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ preDec = [p \in participants |-> none]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
\* 1. Collect votes (implicit – votes are already in the state)
\* 2. Make decision when all alive participants have voted
MakeDecision ==
    /\ coordAlive
    /\ \A p \in AllAliveParticipants : vote[p] \in VoteVals
    /\ coordDecision' = IF \A p \in AllAliveParticipants : vote[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordBroadcasted,
                    vote, alive, faulty, decision, preDec, fwd >>

\* 3. Broadcast decision to a single participant (reliable broadcast)
Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ p \notin coordBroadcasted
    /\ coordBroadcasted' = coordBroadcasted \cup {p}
    /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    vote, alive, faulty, decision >>

\* 4. Coordinator crash
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordFaulty, coordDecision, coordBroadcasted,
                    vote, alive, faulty, decision, preDec, fwd >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* Send vote to coordinator (implicit – vote is already stored)

\* 1. Pre‑decide from coordinator (handled by Broadcast action)

\* 2. Pre‑decide from forwarding by another participant
PreDecFromForward(p) ==
    /\ alive[p]
    /\ preDec[p] = none
    /\ \E q \in participants :
          fwd[q][p] # notsent
    /\ LET d == CHOOSE d \in DecisionVals :
               \E q \in participants : fwd[q][p] = d
       IN
       /\ preDec' = [preDec EXCEPT ![p] = d]
       /\ fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, alive, faulty, decision >>

\* 3. Forward a pre‑decision to another participant
Forward(p, q) ==
    /\ alive[p]
    /\ preDec[p] # none
    /\ q \in participants
    /\ q # p
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = preDec[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, alive, faulty,
                    decision, preDec >>

\* 4. Decide (non‑blocking) after forwarding to all others
Decide(p) ==
    /\ alive[p]
    /\ preDec[p] # none
    /\ \A q \in participants : q # p => fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, alive, faulty,
                    preDec, fwd >>

\* 5. Abort on timeout
AbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A r \in AllAliveParticipants : r \notin coordBroadcasted
    /\ \A d \in AllDeadParticipants :
          \A a \in AllAliveParticipants : fwd[d][a] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, alive, faulty,
                    preDec, fwd >>

\* 6. Participant crash
PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, vote, decision, preDec, fwd >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PreDecFromForward(p)
    \/ \E p,q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [] [][Next]_<< coordAlive, coordFaulty, coordDecision,
                              coordBroadcasted, vote, alive, faulty,
                              decision, preDec, fwd >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionVals \cup {undecided}
    /\ coordBroadcasted \subseteq participants
    /\ vote \in [participants -> VoteVals]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ decision \in [participants -> ParticipantState]
    /\ preDec \in [participants -> (DecisionVals \cup {none})]
    /\ fwd \in [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====