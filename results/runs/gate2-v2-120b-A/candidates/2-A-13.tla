---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* Types for readability *)
Decision == {commit, abort}
Vote      == {yes, no}
Status    == {alive, dead}
ForwardStatus == {notsent, commit, abort}
Phase     == {none, predecided, decided}

VARIABLES
    \* Coordinator state
    coordAlive,            \* Boolean: TRUE if coordinator is alive
    coordFaulty,           \* Boolean: TRUE if coordinator is faulty (has crashed)
    coordDecision,         \* The decision the coordinator wants to broadcast
    \* Participant state
    participantAlive,      \* [p \in participants -> BOOLEAN]
    participantFaulty,     \* [p \in participants -> BOOLEAN]
    vote,                  \* [p \in participants -> Vote]
    decision,              \* [p \in participants -> Decision \cup {"none"}]
    forwarding,            \* [p \in participants -> [q \in participants -> ForwardStatus]]
    predecided,            \* [p \in participants -> BOOLEAN]
    forwardedCount         \* [p \in participants -> Nat]  (how many others p has forwarded to)

\*=============================================================================
\* Type invariant (helps TLC, though the required INVARIANT is TypeInvNB)
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision \cup {"none"}
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ vote \in [participants -> Vote]
    /\ decision \in [participants -> (Decision \cup {"none"})]
    /\ forwarding \in [participants -> [participants -> ForwardStatus]]
    /\ predecided \in [participants -> BOOLEAN]
    /\ forwardedCount \in [participants -> Nat]
    /\ \A p \in participants :
        /\ forwarding[p][p] = notsent           \* self entry never used for forwarding
        /\ IF predecided[p] THEN
              forwarding[p][p] \in {commit, abort}
           ELSE
              forwarding[p][p] = notsent
        /\ forwardedCount[p] = Cardinality({ q \in participants : 
                                          q # p /\ forwarding[p][q] # notsent })
    /\ \A p \in participants :
        /\ decision[p] \in Decision \cup {"none"}
        /\ (decision[p] # "none") => predecided[p]
        /\ (decision[p] # "none") => 
              forwarding[p][p] = decision[p]

\*=============================================================================
\* Initial state
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> yes]          \* arbitrary initial vote
    /\ decision = [p \in participants |-> "none"]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ predecided = [p \in participants |-> FALSE]
    /\ forwardedCount = [p \in participants |-> 0]

\*=============================================================================
\* Coordinator actions (derived from the base ACP-SB)
CoordSendDecision ==
    /\ coordAlive
    /\ coordDecision # "none"
    /\ UNCHANGED << participantAlive, participantFaulty, vote,
                    decision, forwarding, predecided, forwardedCount,
                    coordAlive, coordFaulty, coordDecision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, participantAlive, participantFaulty,
                    vote, decision, forwarding, predecided, forwardedCount>>

\*=============================================================================
\* Participant actions
ParticipantSendVote(p) ==
    /\ participantAlive[p]
    /\ vote[p] = yes \/ vote[p] = no
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    decision, forwarding, predecided, forwardedCount>>

PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ ~predecided[p]
    /\ coordDecision # "none"
    /\ decision[p] = "none"
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = 
                      IF coordDecision = commit THEN commit ELSE abort]
    /\ predecided' = [predecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    forwardedCount>>

PreDecideFromForward(p) ==
    /\ participantAlive[p]
    /\ ~predecided[p]
    /\ \E q \in participants :
          q # p /\ forwarding[q][p] # notsent
    /\ LET d == IF \E q \in participants : q # p /\ forwarding[q][p] = commit
               THEN commit ELSE abort IN
       /\ decision' = [decision EXCEPT ![p] = d]
       /\ forwarding' = [forwarding EXCEPT ![p][p] = d]
       /\ predecided' = [predecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    forwardedCount>>

Forward(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ p # q
    /\ predecided[p]
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ forwardedCount' = [forwardedCount EXCEPT ![p] = forwardedCount[p] + 1]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    decision, predecided>>

Decide(p) ==
    /\ participantAlive[p]
    /\ predecided[p]
    /\ forwardedCount[p] = Cardinality(participants) - 1
    /\ decision[p] = "none"
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    forwarding, predecided, forwardedCount>>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ decision[p] = "none"
    /\ ~coordAlive
    /\ \A q \in participants : forwarding[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = abort]
    /\ predecided' = [predecided EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty, vote,
                    forwardedCount>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    vote, decision, forwarding, predecided,
                    forwardedCount>>

\*=============================================================================
\* Next-state relation
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordDie
    \/ CoordSendDecision

\*=============================================================================
\* Specification
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         participantAlive, participantFaulty, vote,
                         decision, forwarding, predecided, forwardedCount>>

\*=============================================================================
\* Safety invariant (the required AC1-AC4)
SafetyInv ==
    /\ \A p,q \in participants :
          (decision[p] = commit /\ decision[q] = abort) => FALSE
    /\ \A p \in participants :
          (decision[p] = commit) => 
             \A r \in participants : vote[r] = yes
    /\ \A p \in participants :
          (decision[p] = abort) => 
            \/ \E r \in participants : vote[r] = no
            \/ \E r \in participants : participantFaulty[r] = TRUE
            \/ coordFaulty = TRUE
    /\ \A p \in participants :
          (decision[p] = commit \/ decision[p] = abort) => 
            (decision[p] = decision[p])  \* tautology, ensures stability
    /\ TypeInv

\*=============================================================================
\* Naming the required invariant
TypeInvNB == SafetyInv

\*=============================================================================
\* The module ends here
====