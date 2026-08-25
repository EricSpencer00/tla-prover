---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ForwardStatus == {notsent, commit, abort}
VoteVal       == {yes, no, undecided}
DecisionVal   == {commit, abort, undecided}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* DecisionVal: decision made by coordinator (undecided initially)
    coordVotes,          \* [participants -> VoteVal]: votes collected by coordinator
    participantAlive,    \* SUBSET participants: set of alive participants
    participantVote,     \* [participants -> VoteVal]: own vote of each participant
    participantDecision, \* [participants -> DecisionVal]: final decision of each participant
    forwarding           \* [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision, coordVotes,
          participantAlive, participantVote, participantDecision,
          forwarding >>

\* The set of all participants
AllParts == participants

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordVotes = [p \in participants |-> undecided]
    /\ participantAlive = participants
    /\ participantVote = [p \in participants |-> undecided]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordCrash ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    participantDecision, forwarding >>

SendVote(p) ==
    /\ p \in participantAlive
    /\ participantVote[p] = undecided
    /\ participantVote' = [participantVote EXCEPT ![p] = 
            IF RandomElement({yes, no}) = yes THEN yes ELSE no ]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantDecision, forwarding >>

CollectVotes ==
    /\ \A p \in participants: participantVote[p] # undecided
    /\ coordVotes' = participantVote
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantVote,
                    participantDecision, forwarding >>

MakeDecision ==
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ \/ (\E p \in participants : coordVotes[p] = no)   \* at least one NO vote
          /\ coordDecision' = abort
       \/ (\A p \in participants : coordVotes[p] = yes)   \* all YES votes
          /\ coordDecision' = commit
    /\ UNCHANGED << coordAlive, coordFaulty, coordVotes,
                    participantAlive, participantVote,
                    participantDecision, forwarding >>

BroadcastDecision ==
    /\ coordDecision # undecided
    /\ coordAlive = TRUE
    /\ forwarding' = 
        [p \in participants |-> 
            [q \in participants |-> 
                IF q = p THEN 
                    (IF coordDecision = commit THEN commit ELSE abort)
                ELSE forwarding[p][q]]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    participantDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PreDecideFromCoord(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ coordDecision # undecided
    /\ forwarding' = [forwarding EXCEPT ![p][p] = 
            (IF coordDecision = commit THEN commit ELSE abort)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    participantDecision >>

PreDecideFromForward(p, q) ==
    /\ p \in participantAlive
    /\ q \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ forwarding[q][p] # notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    participantDecision >>

Forward(p, q) ==
    /\ p \in participantAlive
    /\ q \in participantAlive
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    participantDecision >>

Decide(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] # notsent
    /\ \A q \in participants: forwarding[p][q] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = 
            (IF forwarding[p][p] = commit THEN commit ELSE abort)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    forwarding >>

AbortOnTimeout(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantAlive, participantVote,
                    forwarding >>

ParticipantCrash(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordVotes,
                    participantVote, participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ CollectVotes
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordCrash
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : \E q \in participants : PreDecideFromForward(p,q)
    \/ \E p \in participants : \E q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantCrash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionVal
    /\ coordVotes \in [participants -> VoteVal]
    /\ participantAlive \subseteq participants
    /\ participantVote \in [participants -> VoteVal]
    /\ participantDecision \in [participants -> DecisionVal]
    /\ forwarding \in [participants -> [participants -> ForwardStatus]]

\* ----------------------------------------------------------------------
\* THEOREMS (optional)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeInv == SpecNB => []TypeInvNB

====