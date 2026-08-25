---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ------------------------------------------------------------
\* State variables
VARIABLES 
    coordAlive,          \* TRUE if coordinator is up
    coordFaulty,         \* TRUE if coordinator has crashed
    coordDecision,       \* coordinator's decision (commit/abort/waiting)
    votes,               \* participants' votes
    voteSent,            \* whether a participant has sent its vote
    participantAlive,    \* liveness of each participant
    participantFaulty,   \* crash flag of each participant
    participantDecision, \* final decision of each participant
    forwarding           \* forwarding table: [p \in participants |-> [q \in participants |-> {notsent, commit, abort}]]

\* ------------------------------------------------------------
\* Initialisation
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ votes = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ------------------------------------------------------------
\* Coordinator actions
CoordMakeDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision' = IF \A p \in participants: votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding>>

CoordDie ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding>>

\* ------------------------------------------------------------
\* Participant actions
SendVote(p) ==
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ \/ votes' = [votes EXCEPT ![p] = yes]
          /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
       \/ votes' = [votes EXCEPT ![p] = no]
          /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding>>

PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ forwarding[p][p] = notsent
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p] = [forwarding[p] EXCEPT ![p] = coordDecision]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision>>

PreDecideFromForward(p) ==
    /\ participantAlive[p]
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants: q # p /\ forwarding[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} :
                 \E q \in participants: q # p /\ forwarding[q][p] = d
        IN forwarding' = [forwarding EXCEPT ![p] = [forwarding[p] EXCEPT ![p] = d]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision>>

Forward(p, r) ==
    /\ participantAlive[p]
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][r] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p] = [forwarding[p] EXCEPT ![r] = forwarding[p][p]]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision>>

Decide(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] \in {commit, abort}
    /\ \A r \in participants: forwarding[p][r] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    forwarding>>

AbortTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants: participantAlive[q] => forwarding[q][q] = notsent
    /\ \A q \in participants:
          ~participantAlive[q] =>
            \A r \in participants:
                participantAlive[r] => forwarding[q][r] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantAlive, participantFaulty,
                    forwarding>>

Die(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, voteSent,
                    participantDecision, forwarding>>

\* ------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ CoordMakeDecision
    \/ CoordDie
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p \in participants: PreDecideFromForward(p)
    \/ \E p \in participants: \E r \in participants: Forward(p, r)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: Die(p)

\* ------------------------------------------------------------
\* Fairness (weak fairness on all progress actions except crashes)
Fairness ==
    /\ \A p \in participants: WF_vars(SendVote(p))
    /\ \A p \in participants: WF_vars(PreDecideFromCoord(p))
    /\ \A p \in participants: WF_vars(PreDecideFromForward(p))
    /\ \A p \in participants: \A r \in participants: WF_vars(Forward(p, r))
    /\ \A p \in participants: WF_vars(Decide(p))
    /\ \A p \in participants: WF_vars(AbortTimeout(p))
    /\ WF_vars(CoordMakeDecision)

\* ------------------------------------------------------------
\* Specification
SpecNB ==
    Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                votes, voteSent,
                participantAlive, participantFaulty,
                participantDecision, forwarding>> /\ Fairness

\* ------------------------------------------------------------
\* Type invariant
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, waiting}
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\* ------------------------------------------------------------
\* The required identifiers for the .cfg file
SPECIFICATION == SpecNB
INVARIANTS == TypeInvNB

====