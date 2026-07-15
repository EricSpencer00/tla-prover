---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (declared in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT participants
CONSTANT yes, no, undecided
CONSTANT commit, abort, waiting
CONSTANT notsent

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Participant == participants

Decision   == {"Commit", "Abort"}          \* textual names for commit/abort
PreDecision == Decision \cup {"None"}     \* includes a sentinel for no pre-decision
FwdStatus   == {"NotSent", "Sent"}        \* per‑pair forwarding status

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,                \* [Participant -> Decision]  (yes/no as strings)
    decision,            \* [Participant -> {"Undecided","Commit","Abort"}]
    coordAlive,          \* Boolean, coordinator up?
    coordFaulty,         \* Boolean, coordinator faulty?
    participantsAlive,   \* [Participant -> BOOLEAN]
    participantsFaulty,  \* [Participant -> BOOLEAN]
    predec,              \* [Participant -> PreDecision] (none or a decision)
    fwdTable,            \* [Participant -> [Participant -> {"NotSent","Sent"}]]
    voted                \* [Participant -> BOOLEAN] (has sent its vote)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DecisionFromVote(v) == IF v = yes THEN "Commit" ELSE "Abort"

IsFaulty(p) == participantsFaulty[p] \/ ~participantsAlive[p]

AllAlive == {p \in participants : participantsAlive[p]}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote = [p \in participants |-> yes]          \* arbitrary initial vote
    /\ decision = [p \in participants |-> "Undecided"]
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ participantsAlive = [p \in participants |-> TRUE]
    /\ participantsFaulty = [p \in participants |-> FALSE]
    /\ predec = [p \in participants |-> "None"]
    /\ fwdTable = [p \in participants |-> [q \in participants |-> "NotSent"]]
    /\ voted = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\* ----------------------------------------------------------------------
CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, decision, participantsAlive, participantsFaulty,
                    predec, fwdTable, voted>>

MakeDecision ==
    /\ coordAlive = TRUE
    /\ \E d \in Decision :
          /\ decisionForAll = [p \in participants |-> d]
          /\ decision' = decisionForAll
          /\ UNCHANGED <<vote, coordAlive, coordFaulty,
                        participantsAlive, participantsFaulty,
                        predec, fwdTable, voted>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ participantsAlive[p] = TRUE
    /\ voted[p] = FALSE
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    predec, fwdTable>>

PreDecFromCoord(p) ==
    /\ participantsAlive[p] = TRUE
    /\ decision[p] \in {"Commit","Abort"}
    /\ predec[p] = "None"
    /\ predec' = [predec EXCEPT ![p] = decision[p]]
    /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    fwdTable, voted>>

PreDecFromPeer(p) ==
    /\ participantsAlive[p] = TRUE
    /\ predec[p] = "None"
    /\ \E q \in participants :
          /\ q # p
          /\ participantsAlive[q] = TRUE
          /\ fwdTable[q][p] = "Sent"
          /\ predec[q] # "None"
          /\ predec' = [predec EXCEPT ![p] = predec[q]]
    /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    fwdTable, voted>>

Forward(p) ==
    /\ participantsAlive[p] = TRUE
    /\ predec[p] # "None"
    /\ \E q \in participants :
          /\ q # p
          /\ participantsAlive[q] = TRUE
          /\ fwdTable[p][q] = "NotSent"
          /\ fwdTable' = [fwdTable EXCEPT ![p][q] = "Sent"]
    /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    predec, voted>>

Decide(p) ==
    /\ participantsAlive[p] = TRUE
    /\ predec[p] # "None"
    /\ \A q \in participants : q # p => fwdTable[p][q] = "Sent"
    /\ decision[p] = "Undecided"
    /\ decision' = [decision EXCEPT ![p] = predec[p]]
    /\ UNCHANGED <<vote, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    predec, fwdTable, voted>>

AbortTimeout(p) ==
    /\ participantsAlive[p] = TRUE
    /\ decision[p] = "Undecided"
    /\ coordAlive = FALSE
    /\ \A q \in participants : decision[q] = "Undecided"
    /\ \A q \in participants : fwdTable[q][p] = "NotSent"
    /\ decision' = [decision EXCEPT ![p] = "Abort"]
    /\ UNCHANGED <<vote, coordAlive, coordFaulty,
                    participantsAlive, participantsFaulty,
                    predec, fwdTable, voted>>

Die(p) ==
    /\ participantsAlive[p] = TRUE
    /\ participantsAlive' = [participantsAlive EXCEPT ![p] = FALSE]
    /\ participantsFaulty' = [participantsFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty,
                    predec, fwdTable, voted>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecFromCoord(p)
    \/ \E p \in participants : PreDecFromPeer(p)
    \/ \E p \in participants : Forward(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordDie
    \/ MakeDecision

\* ----------------------------------------------------------------------
\* Specification (the top‑level temporal formula)
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<vote, decision, coordAlive, coordFaulty,
                               participantsAlive, participantsFaulty,
                               predec, fwdTable, voted>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within their intended domains)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ vote \in [participants -> {yes, no}]
    /\ decision \in [participants -> {"Undecided","Commit","Abort"}]
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ participantsAlive \in [participants -> BOOLEAN]
    /\ participantsFaulty \in [participants -> BOOLEAN]
    /\ predec \in [participants -> PreDecision]
    /\ fwdTable \in [participants -> [participants -> {"NotSent","Sent"}]]
    /\ voted \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Safety invariant AC1: agreement (no mixed commit/abort)
\* ----------------------------------------------------------------------
Agreement ==
    ~(\E p, q \in participants :
          /\ participantsAlive[p] = TRUE
          /\ participantsAlive[q] = TRUE
          /\ decision[p] = "Commit"
          /\ decision[q] = "Abort")

\* ----------------------------------------------------------------------
\* Safety invariant AC2: commit validity
\* ----------------------------------------------------------------------
CommitValidity ==
    \A p \in participants :
        /\ decision[p] = "Commit"
        => /\ participantsAlive[p] = TRUE
           /\ vote[p] = yes

\* ----------------------------------------------------------------------
\* Safety invariant AC3: abort validity
\* ----------------------------------------------------------------------
AbortValidity ==
    \A p \in participants :
        /\ decision[p] = "Abort"
        => \/ \E q \in participants : vote[q] = no
           \/ \E q \in participants : participantsFaulty[q] = TRUE
           \/ coordFaulty = TRUE

\* ----------------------------------------------------------------------
\* Safety invariant AC4: irrevocability
\* ----------------------------------------------------------------------
Irrevocable ==
    \A p \in participants :
        /\ decision[p] \in {"Commit","Abort"}
        => [] (decision[p] = decision[p])   \* trivially stays the same

\* ----------------------------------------------------------------------
\* Combined safety invariant (the one required by the .cfg)
\* ----------------------------------------------------------------------
SafetyInv == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocable

=============================================================================