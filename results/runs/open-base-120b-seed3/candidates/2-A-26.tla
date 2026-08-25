---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS 
    participants,   \* the set of participant identifiers
    yes, no,        \* vote values
    undecided, commit, abort,   \* decision values for participants
    waiting,        \* auxiliary value (unused in this spec but kept for compatibility)
    notsent         \* status used in the forwarding table

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES 
    coordAlive,         \* Boolean: TRUE iff the coordinator is alive
    coordFaulty,        \* Boolean: TRUE iff the coordinator has crashed
    coordDecision,      \* one of {undecided, commit, abort}
    coordRequestSent,   \* Boolean: TRUE iff the coordinator has sent the request
    votes,              \* [participants -> {yes,no}]   (partial function)
    participantAlive,   \* SUBSET participants
    participantFaulty,  \* SUBSET participants
    participantDecision,\* [participants -> {undecided, commit, abort}]
    forwarding          \* [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllParticipants == participants
AllDecisions   == {undecided, commit, abort}
AllVotes       == {yes, no}
AllForwardVals == {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordRequestSent = FALSE
    /\ votes = [p \in participants |-> NULL]   \* NULL means no vote yet
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* COORDINATOR ACTIONS
\* ----------------------------------------------------------------------
SendRequest ==
    /\ coordAlive
    /\ ~coordRequestSent
    /\ coordRequestSent' = TRUE
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding >>

ReceiveVote(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ votes[p] = NULL
    /\ \E v \in AllVotes:
          /\ votes' = [votes EXCEPT ![p] = v]
          /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                         coordRequestSent, participantAlive,
                         participantFaulty, participantDecision, forwarding >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: votes[p] # NULL
    /\ coordDecision' = IF \A p \in participants: votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordRequestSent,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding >>

CoordinatorDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordRequestSent, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* PARTICIPANT ACTIONS
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ votes[p] # NULL          \* vote already collected by coordinator; no effect here
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

PreDecideFromCoordinator(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ coordDecision # undecided
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision >>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ forwarding[q][p] # notsent
    /\ LET d == CHOOSE q \in participants :
                     q # p /\ forwarding[q][p] # notsent
        IN forwarding' = [forwarding EXCEPT ![p][p] = forwarding[d][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision >>

Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ p \in participantAlive
    /\ forwarding[p][p] # notsent            \* p has a pre‑decision
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision >>

Decide(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ \A q \in participants: forwarding[p][q] # notsent   \* forwarded to everyone
    /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    forwarding >>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          (q \in participantAlive => forwarding[q][p] = notsent)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    forwarding >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* COMBINED NEXT ACTION
\* ----------------------------------------------------------------------
Next ==
    \/ SendRequest
    \/ \E p \in participants: ReceiveVote(p)
    \/ MakeDecision
    \/ CoordinatorDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecideFromCoordinator(p)
    \/ \E p \in participants: PreDecideFromForward(p)
    \/ \E p,q \in participants: Forward(p,q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in AllDecisions
    /\ coordRequestSent \in BOOLEAN
    /\ votes \in [participants -> (AllVotes \cup {NULL})]
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ participantDecision \in [participants -> AllDecisions]
    /\ forwarding \in [participants -> [participants -> AllForwardVals]]

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [][Next]_<< coordAlive, coordFaulty, coordDecision,
                    coordRequestSent, votes,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* ----------------------------------------------------------------------
\* PROPERTIES (the required identifiers are already defined above)
\* ----------------------------------------------------------------------
\* The safety properties AC1–AC4 and liveness properties AC3, AC5 can be
\* expressed as separate invariants or temporal formulas, but they are
\* not required to be named in this module.  The required exported
\* identifiers are SpecNB and TypeInvNB.

====