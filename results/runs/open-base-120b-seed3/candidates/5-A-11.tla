---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    vote,               \* [p \in participants |-> yes/no]
    voteSent,           \* SUBSET participants
    participantDecision,\* [p \in participants |-> undecided/commit/abort]
    participantAlive,  \* SUBSET participants
    requestSent,        \* SUBSET participants (coordinator has sent request)
    recvVote,           \* [p \in participants |-> yes/no/waiting]
    broadcastSent,      \* [p \in participants |-> commit/abort/notsent]
    coordDecision,      \* undecided/commit/abort
    coordAlive          \* BOOLEAN (TRUE = alive, FALSE = crashed)

vars == << vote, voteSent, participantDecision, participantAlive,
           requestSent, recvVote, broadcastSent, coordDecision, coordAlive >>

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent = {}
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantAlive = participants
    /\ requestSent = {}
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

\* ----------------------------------------------------------------------
\*  Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin requestSent
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    recvVote, broadcastSent, coordDecision >>
    /\ requestSent' = requestSent \cup {p}
    /\ coordAlive' = coordAlive

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ recvVote[p] = waiting
    /\ p \in voteSent
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    requestSent, broadcastSent, coordDecision, coordAlive >>
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in participants
    /\ p \in requestSent
    /\ recvVote[p] = waiting
    /\ p \notin participantAlive
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    requestSent, recvVote, broadcastSent, coordAlive >>
    /\ coordDecision' = abort

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent = participants
    /\ \A p \in participants : recvVote[p] # waiting
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    requestSent, recvVote, broadcastSent, coordAlive >>
    /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes
                         THEN commit
                         ELSE abort

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ broadcastSent[p] = notsent
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    requestSent, recvVote, coordDecision, coordAlive >>
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]

CoordDie ==
    /\ coordAlive
    /\ UNCHANGED << vote, voteSent, participantDecision, participantAlive,
                    requestSent, recvVote, broadcastSent, coordDecision >>
    /\ coordAlive' = FALSE

\* ----------------------------------------------------------------------
\*  Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ p \in participantAlive
    /\ p \in requestSent
    /\ p \notin voteSent
    /\ UNCHANGED << vote, participantDecision, participantAlive,
                    requestSent, recvVote, broadcastSent, coordDecision, coordAlive >>
    /\ voteSent' = voteSent \cup {p}

AbortOnVote(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ p \in voteSent
    /\ vote[p] = no
    /\ UNCHANGED << vote, voteSent, participantAlive,
                    requestSent, recvVote, broadcastSent, coordDecision, coordAlive >>
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]

AbortOnTimeout(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin requestSent
    /\ UNCHANGED << vote, voteSent, participantAlive,
                    requestSent, recvVote, broadcastSent, coordDecision, coordAlive >>
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]

DecideFromBroadcast(p) ==
    /\ p \in participantAlive
    /\ participantDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ UNCHANGED << vote, voteSent, participantAlive,
                    requestSent, recvVote, coordDecision, coordAlive >>
    /\ participantDecision' = [participantDecision EXCEPT ![p] = broadcastSent[p]]

ParticipantDie(p) ==
    /\ p \in participantAlive
    /\ UNCHANGED << vote, voteSent, participantDecision,
                    requestSent, recvVote, broadcastSent, coordDecision, coordAlive >>
    /\ participantAlive' = participantAlive \ {p}

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \subseteq participants
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantAlive \subseteq participants
    /\ requestSent \subseteq participants
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

\* ----------------------------------------------------------------------
\*  Safety properties (optional, can be used in the .cfg)
\* ----------------------------------------------------------------------
AC1 == \A p, q \in participants :
          (participantDecision[p] = commit) => (participantDecision[q] # abort)

AC2 == \A p \in participants :
          (participantDecision[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 == \A p \in participants :
          (participantDecision[p] = abort) =>
          ( \E q \in participants : vote[q] = no
            \/ \E q \in participants : q \notin participantAlive
            \/ coordAlive = FALSE )

AC4 == \A p \in participants :
          /\ participantDecision[p] = commit => [] (participantDecision[p] = commit)
          /\ participantDecision[p] = abort  => [] (participantDecision[p] = abort)

\* ----------------------------------------------------------------------
\*  Liveness property (non‑blocking termination is NOT required)
\* ----------------------------------------------------------------------
Liveness ==
    <> ( \A p \in participants : participantDecision[p] # undecided
         \/ \E p \in participants : p \notin participantAlive
         \/ coordAlive = FALSE )

====