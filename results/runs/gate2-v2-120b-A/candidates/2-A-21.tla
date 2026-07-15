---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants (to be bound in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Participant == participants
Decision    == {commit, abort}
Vote        == {yes, no}
Status      == {undecided, commit, abort}
FwdStatus   == {notsent, commit, abort}
Bool        == {TRUE, FALSE}

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES
    coordAlive,      \* Coordinator aliveness flag (TRUE = alive)
    coordFaulty,     \* Coordinator fault flag (TRUE = faulty)
    coordDecision,   \* Decision made by the coordinator (or "Undecided")
    coordBroadcast,  \* Set of participants that have already been broadcast to
    votes,           \* [p \in Participant -> Vote \cup {"None"}]
    alive,           \* [p \in Participant -> Bool]
    faulty,          \* [p \in Participant -> Bool]
    predec,          \* [p \in Participant -> FwdStatus]  (pre-decision received)
    fwdTable,        \* [p \in Participant -> [q \in Participant -> FwdStatus]]
    decision         \* [p \in Participant -> Status]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
CoordUndecided == "Undecided"

--------------------------------------------------------------------
-- Initialization
--------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = CoordUndecided
    /\ coordBroadcast = {}
    /\ votes = [p \in Participant |-> "None"]
    /\ alive = [p \in Participant |-> TRUE]
    /\ faulty = [p \in Participant |-> FALSE]
    /\ predec = [p \in Participant |-> notsent]
    /\ fwdTable = [p \in Participant |-> [q \in Participant |-> notsent]]
    /\ decision = [p \in Participant |-> undecided]

--------------------------------------------------------------------
-- Coordinator actions (derived from ACP-SB, simplified)
--------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = CoordUndecided
    /\ UNCHANGED <<votes, alive, faulty, predec, fwdTable, decision, coordBroadcast>>

CoordCollectVotes ==
    /\ coordAlive = TRUE
    /\ /\ \E n \in participants :
          /\ votes[n] = "None"
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   alive, faulty, predec, fwdTable, decision>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = CoordUndecided
    /\ LET allYes == \A p \in participants : votes[p] = yes
       in coordDecision' =
           IF allYes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, alive, faulty,
                   predec, fwdTable, decision, coordBroadcast>>

CoordBroadcast ==
    /\ coordAlive = TRUE
    /\ coordDecision # CoordUndecided
    /\ \E p \in participants :
          /\ p \notin coordBroadcast
          /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                         votes, alive, faulty,
                         predec, fwdTable, decision>>
          /\ coordBroadcast' = coordBroadcast \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, alive, faulty,
                   predec, fwdTable, decision>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcast, votes,
                   alive, faulty, predec, fwdTable, decision>>

--------------------------------------------------------------------
-- Participant actions
--------------------------------------------------------------------
SendVote(p) ==
    /\ alive[p] = TRUE
    /\ votes[p] = "None"
    /\ votes' = [votes EXCEPT ![p] = IF \E q \in participants : q # p /\ fwdTable[q][p] # notsent
                                            THEN no
                                            ELSE yes]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   alive, faulty, predec, fwdTable, decision>>

PreDecFromCoord(p) ==
    /\ alive[p] = TRUE
    /\ predec[p] = notsent
    /\ p \in coordBroadcast
    /\ coordDecision # CoordUndecided
    /\ predec' = [predec EXCEPT ![p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, alive, faulty, fwdTable, decision>>

PreDecFromFwd(p) ==
    /\ alive[p] = TRUE
    /\ predec[p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ fwdTable[q][p] # notsent
    /\ LET src == CHOOSE q \in participants :
                     q # p /\ fwdTable[q][p] # notsent
        decisionFromSrc == IF fwdTable[src][p] = commit THEN commit ELSE abort
    IN
        predec' = [predec EXCEPT ![p] = decisionFromSrc]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, alive, faulty, fwdTable, decision>>

Forward(p) ==
    /\ alive[p] = TRUE
    /\ predec[p] # notsent
    /\ \E q \in participants :
          /\ q # p
          /\ fwdTable[p][q] = notsent
    /\ LET target == CHOOSE q \in participants :
                         q # p /\ fwdTable[p][q] = notsent
        fwdVal == predec[p]
    IN
        fwdTable' = [fwdTable EXCEPT ![p][target] = fwdVal]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, alive, faulty, predec, decision>>

Decide(p) ==
    /\ alive[p] = TRUE
    /\ predec[p] # notsent
    /\ \A q \in participants : fwdTable[p][q] # notsent
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = predec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, alive, faulty, predec, fwdTable>>

AbortTimeout(p) ==
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          (alive[q] => q \notin coordBroadcast)
    /\ \A q \in participants :
          (faulty[q] => \A r \in participants :
                           alive[r] => fwdTable[q][r] = notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, alive, faulty, predec, fwdTable>>

Die(p) ==
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   votes, predec, fwdTable, decision>>

--------------------------------------------------------------------
-- Combined participant step
--------------------------------------------------------------------
ParticipantStep(p) ==
    \/ SendVote(p)
    \/ PreDecFromCoord(p)
    \/ PreDecFromFwd(p)
    \/ Forward(p)
    \/ Decide(p)
    \/ AbortTimeout(p)
    \/ Die(p)

--------------------------------------------------------------------
-- Next-state relation
--------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : ParticipantStep(p)

--------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                               coordBroadcast, votes, alive, faulty,
                               predec, fwdTable, decision>>

--------------------------------------------------------------------
-- Type correctness invariant (ensures all variables stay within their domains)
--------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in Bool
    /\ coordFaulty \in Bool
    /\ coordDecision \in {CoordUndecided} \cup Decision
    /\ coordBroadcast \subseteq participants
    /\ votes \in [participants -> (Vote \cup {"None"})]
    /\ alive \in [participants -> Bool]
    /\ faulty \in [participants -> Bool]
    /\ predec \in [participants -> FwdStatus]
    /\ fwdTable \in [participants -> [participants -> FwdStatus]]
    /\ decision \in [participants -> Status]

======================================================================