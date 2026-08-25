---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* the (finite) set of participant identifiers
    yes, no,          \* vote values
    undecided, commit, abort, \* decision values
    waiting,         \* coordinator decision before it is made
    notsent          \* status used in forwarding table

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES 
    coordAlive,          \* TRUE iff the coordinator has not crashed
    coordFaulty,         \* TRUE iff the coordinator is faulty (crashed)
    coordDecision,       \* waiting, commit or abort
    coordBroadcasted,    \* subset of participants that have already received the decision from the coordinator
    votes,               \* [p \in participants |-> yes/no] – the vote each participant cast
    voteSent,            \* [p \in participants |-> BOOLEAN] – has p already sent its vote?
    participantAlive,    \* subset of participants that are still alive
    participantFaulty,   \* subset of participants that have crashed
    participantDecision, \* [p \in participants |-> undecided/commit/abort] – final decision
    forwarding           \* [p \in participants |-> [q \in participants |-> notsent/commit/abort]]

\*=====================================================================
\* Helper definitions
\*=====================================================================
\* The set of all variables – needed for the stuttering equivalence
vars == << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
           votes, voteSent,
           participantAlive, participantFaulty,
           participantDecision, forwarding >>

\* All participants are either alive or faulty (crashed)
AliveOrFaulty == participantAlive = participants \ participantFaulty

\* A participant has already received a pre‑decision (stored at its own index)
PreDecided(p) == forwarding[p][p] # notsent

\* The pre‑decision stored at participant p (commit or abort)
PreDecision(p) == forwarding[p][p]

\* All other participants to which p has already forwarded its pre‑decision
AllForwarded(p) == \A q \in participants \ {p} : forwarding[p][q] # notsent

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = waiting
    /\ coordBroadcasted = {}
    /\ votes = [p \in participants |-> yes]      \* default vote; can be overwritten by participants
    /\ voteSent = [p \in participants |-> FALSE]
    /\ participantAlive = participants
    /\ participantFaulty = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\*=====================================================================
\* Coordinator actions (derived from the base ACP‑SB)
\*=====================================================================
\* Collect all votes and decide (commit iff every vote is yes)
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \A p \in participants : voteSent[p] = TRUE
    /\ LET allYes == \A p \in participants : votes[p] = yes
       IN coordDecision' = IF allYes THEN commit ELSE abort
    /\ coordBroadcasted' = {}
    /\ UNCHANGED << coordAlive, coordFaulty, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* Broadcast the decision to a single participant (one step per participant)
CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # waiting
    /\ \E p \in participants : p \notin coordBroadcasted
    /\ LET p == CHOOSE q \in participants : q \notin coordBroadcasted
       IN coordBroadcasted' = coordBroadcasted \cup {p}
    /\ UNCHANGED << coordFaulty, coordDecision, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* Coordinator crashes (becomes faulty)
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcasted, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\*=====================================================================
\* Participant actions (base actions + new reliable‑broadcast actions)
\*=====================================================================
\* A participant sends its vote to the coordinator
SendVote(p) ==
    /\ p \in participantAlive
    /\ voteSent[p] = FALSE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding >>

\* If a participant has voted no, it aborts immediately
AbortOnNo(p) ==
    /\ p \in participantAlive
    /\ voteSent[p] = TRUE
    /\ votes[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    forwarding >>

\* (1) Pre‑decide from coordinator: the coordinator has already broadcast the decision to p
PreDecideFromCoord(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ p \in coordBroadcasted
    /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    participantDecision >>

\* (2) Pre‑decide from forwarding by another participant
PreDecideFromFwd(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants \ {p} :
          forwarding[p][q] # notsent
          /\ forwarding[p][q] \in {commit, abort}
    /\ LET q == CHOOSE r \in participants \ {p} :
                forwarding[p][r] # notsent
                /\ forwarding[p][r] \in {commit, abort}
       IN forwarding' = [forwarding EXCEPT ![p][p] = forwarding[p][q]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    participantDecision >>

\* (3) Forward the pre‑decision to another participant
Forward(p,q) ==
    /\ p \in participantAlive
    /\ q \in participants \ {p}
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ LET dec == forwarding[p][p]
       IN forwarding' = [forwarding EXCEPT
                         ![p][q] = dec,
                         ![q][p] = dec]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    participantDecision >>

\* (4) Decide (non‑blocking) after having forwarded to everybody
Decide(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] \in {commit, abort}
    /\ AllForwarded(p)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = PreDecision(p)]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    forwarding >>

\* (5) Abort on timeout when coordinator is dead and no information can be obtained
AbortTimeout(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A a \in participantAlive : forwarding[a][a] = notsent
    /\ \A d \in participants \ participantAlive :
          \A a \in participantAlive : forwarding[d][a] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantAlive, participantFaulty,
                    forwarding >>

\* (6) Participant crashes
ParticipantDie(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, voteSent, participantDecision, forwarding >>

\*=====================================================================
\* The overall Next relation
\*=====================================================================
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnNo(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\*=====================================================================
\* Specification
\*=====================================================================
SpecNB == Init /\ [][Next]_vars

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {waiting, commit, abort}
    /\ coordBroadcasted \subseteq participants
    /\ votes \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

\*=====================================================================
\* Liveness properties (optional – can be referenced from the .cfg)
\*=====================================================================
\* AC5 – every non‑faulty participant eventually decides
AC5 ==  \A p \in participants :
           []<>(p \in participantFaulty \/ participantDecision[p] # undecided)

\*=====================================================================
\* End of module
\*=====================================================================
====