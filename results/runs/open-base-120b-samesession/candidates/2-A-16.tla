---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  participants, \* set of participant identifiers
  yes, no, undecided, \* vote values
  commit, abort, \* decision values
  waiting, \* placeholder for coordinator request state (unused here)
  notsent \* forwarding table entry meaning “not yet forwarded”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
  coordAlive,          \* TRUE if the coordinator is up
  coordFaulty,         \* TRUE if the coordinator has been detected faulty
  coordDecision,       \* {commit, abort, undecided}
  votes,               \* [participants -> {yes,no,undecided}]
  pAlive,              \* set of participants that are still alive
  pDecision,           \* [participants -> {commit,abort,undecided}]
  forward               \* [participants -> [participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {commit, abort, undecided}
  /\ votes \in [participants -> {yes, no, undecided}]
  /\ pAlive \subseteq participants
  /\ pDecision \in [participants -> {commit, abort, undecided}]
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ votes = [p \in participants |-> undecided]
  /\ pAlive = participants
  /\ pDecision = [p \in participants |-> undecided]
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordDecision' \in {commit, abort}
  /\ UNCHANGED <<coordAlive, coordFaulty, votes, pAlive, pDecision, forward>>

CoordinatorDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, votes, pAlive, pDecision, forward>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
Vote(p, v) ==
  /\ p \in pAlive
  /\ votes[p] = undecided
  /\ v \in {yes, no}
  /\ votes' = [votes EXCEPT ![p] = v]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, pAlive, pDecision, forward>>

PreDecideFromCoord(p) ==
  /\ p \in pAlive
  /\ forward[p][p] = notsent
  /\ coordDecision \in {commit, abort}
  /\ forward' = [forward EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pAlive, pDecision>>

PreDecideFromForward(p) ==
  /\ p \in pAlive
  /\ forward[p][p] = notsent
  /\ \E q \in participants: q # p /\ forward[q][p] # notsent
  /\ LET d == (CHOOSE q \in participants: q # p /\ forward[q][p] # notsent) IN
       forward' = [forward EXCEPT ![p][p] = forward[d][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pAlive, pDecision>>

Forward(p, q) ==
  /\ p \in pAlive
  /\ q \in participants
  /\ p # q
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pAlive, pDecision>>

Decide(p) ==
  /\ p \in pAlive
  /\ forward[p][p] # notsent
  /\ \A q \in participants: forward[p][q] # notsent
  /\ pDecision[p] = undecided
  /\ pDecision' = [pDecision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pAlive, forward>>

AbortTimeout(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ coordAlive = FALSE
  /\ \A r \in participants: forward[r][r] = notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pAlive, forward>>

Die(p) ==
  /\ p \in pAlive
  /\ pAlive' = pAlive \ {p}
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes, pDecision, forward>>

\* ----------------------------------------------------------------------
\* Disjunctive next-state relation
\* ----------------------------------------------------------------------
ParticipantVote ==
  \E p \in participants: Vote(p, yes) \/ Vote(p, no)

ParticipantPreDecideCoord ==
  \E p \in participants: PreDecideFromCoord(p)

ParticipantPreDecideForward ==
  \E p \in participants: PreDecideFromForward(p)

ParticipantForward ==
  \E p, q \in participants: p # q /\ Forward(p, q)

ParticipantDecide ==
  \E p \in participants: Decide(p)

ParticipantAbortTimeout ==
  \E p \in participants: AbortTimeout(p)

ParticipantDie ==
  \E p \in participants: Die(p)

Next ==
  \/ MakeDecision
  \/ CoordinatorDie
  \/ ParticipantVote
  \/ ParticipantPreDecideCoord
  \/ ParticipantPreDecideForward
  \/ ParticipantForward
  \/ ParticipantDecide
  \/ ParticipantAbortTimeout
  \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [] [Next]_<<coordAlive, coordFaulty, coordDecision,
                          votes, pAlive, pDecision, forward>>

\* ----------------------------------------------------------------------
\* The only invariant required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT TypeInvNB

====