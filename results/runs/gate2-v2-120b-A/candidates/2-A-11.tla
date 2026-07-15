---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    \* Coordinator state
    coord_alive,            \* TRUE iff coordinator is alive
    coord_faulty,           \* TRUE iff coordinator is faulty (has crashed)
    coord_request,         \* TRUE iff a request is pending
    coord_vote,            \* Mapping from participant -> vote (yes/no)
    coord_decision,        \* The decision made by coordinator (commit/abort/Undecided)
    coord_sent,            \* Mapping from participant -> BOOL, TRUE if decision broadcast to that participant

    \* Participant state
    part_alive,            \* Mapping participant -> BOOL
    part_faulty,           \* Mapping participant -> BOOL
    part_forward,          \* Mapping participant -> [participants -> {notsent, commit, abort}]
    part_decision          \* Mapping participant -> {commit, abort, undecided}

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Participants == participants
DecisionVal  == {commit, abort, undecided}
ForwardVal   == {notsent, commit, abort}
VoteVal      == {yes, no}
CoordState   == {waiting, notsent} \* simple placeholder for request handling

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
AllSent(p) == \A q \in Participants : part_forward[p][q] # notsent

AllDecided == \A p \in Participants : part_decision[p] # undecided

NoAliveHasBroadcast == \A p \in Participants :
    coord_alive => coord_sent[p] = FALSE

NoDeadForwardedToAlive == \A p \in Participants :
    part_faulty[p] => \A q \in Participants :
        part_alive[q] => \A r \in Participants : part_forward[p][r] = notsent

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ coord_alive = TRUE
    /\ coord_faulty = FALSE
    /\ coord_request = FALSE
    /\ coord_vote = [p \in Participants |-> no] \* irrelevant until set
    /\ coord_decision = undecided
    /\ coord_sent = [p \in Participants |-> FALSE]
    /\ part_alive = [p \in Participants |-> TRUE]
    /\ part_faulty = [p \in Participants |-> FALSE]
    /\ part_forward = [p \in Participants |-> [q \in Participants |-> notsent]]
    /\ part_decision = [p \in Participants |-> undecided]

(*--------------------------------------------------------------------
  Coordinator actions (inherited from ACP-SB)
--------------------------------------------------------------------*)
CoordSendRequest ==
    /\ coord_alive
    /\ ~coord_request
    /\ coord_request' = TRUE
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_vote,
                    coord_decision, coord_sent,
                    part_alive, part_faulty, part_forward, part_decision>>

CoordCollectVote(p) ==
    /\ coord_alive
    /\ coord_request
    /\ p \in Participants
    /\ part_alive[p]
    /\ coord_vote' = [coord_vote EXCEPT ![p] = part_forward[p][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_decision, coord_sent,
                    part_alive, part_faulty, part_forward, part_decision>>

CoordMakeDecision ==
    /\ coord_alive
    /\ coord_request
    /\ \A p \in Participants : part_alive[p] => part_forward[p][p] # notsent
    /\ coord_decision' =
        IF \A p \in Participants : part_forward[p][p] = commit THEN commit
        ELSE abort
    /\ coord_request' = FALSE
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_vote,
                    coord_sent, part_alive, part_faulty,
                    part_forward, part_decision>>

CoordBroadcast ==
    /\ coord_alive
    /\ coord_decision # undecided
    /\ coord_sent' = [p \in Participants |-> TRUE]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision,
                    part_alive, part_faulty, part_forward, part_decision>>

CoordDie ==
    /\ coord_alive
    /\ coord_alive' = FALSE
    /\ coord_faulty' = TRUE
    /\ UNCHANGED <<coord_request, coord_vote, coord_decision,
                    coord_sent, part_alive, part_faulty,
                    part_forward, part_decision>>

(*--------------------------------------------------------------------
  Participant actions (extended with reliable broadcast)
--------------------------------------------------------------------*)
ParticipantVote(p) ==
    /\ part_alive[p]
    /\ ~part_faulty[p]
    /\ part_decision[p] = undecided
    /\ part_forward[p][p] = notsent
    /\ \E v \in VoteVal : 
        /\ part_forward' = [part_forward EXCEPT ![p][p] = 
                               IF v = yes THEN commit ELSE abort]
        /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                        coord_vote, coord_decision, coord_sent,
                        part_alive, part_faulty, part_decision>>

PreDecideFromCoord(p) ==
    /\ part_alive[p]
    /\ part_forward[p][p] = notsent
    /\ coord_sent[p]
    /\ part_forward' = [part_forward EXCEPT ![p][p] = 
                         IF coord_decision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_alive, part_faulty, part_decision>>

PreDecideFromForward(p, q) ==
    /\ part_alive[p]
    /\ part_forward[p][p] = notsent
    /\ part_forward[q][p] # notsent
    /\ part_forward' = [part_forward EXCEPT ![p][p] = part_forward[q][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_alive, part_faulty, part_decision>>

Forward(p, q) ==
    /\ part_alive[p]
    /\ part_forward[p][p] # notsent
    /\ part_forward[p][q] = notsent
    /\ part_forward' = [part_forward EXCEPT ![p][q] = part_forward[p][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_alive, part_faulty, part_decision>>

Decide(p) ==
    /\ part_alive[p]
    /\ part_forward[p][p] # notsent
    /\ AllSent(p)
    /\ part_decision' = [part_decision EXCEPT ![p] = part_forward[p][p]]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_alive, part_faulty, part_forward>>

AbortOnTimeout(p) ==
    /\ part_alive[p]
    /\ part_decision[p] = undecided
    /\ ~coord_alive
    /\ NoAliveHasBroadcast
    /\ NoDeadForwardedToAlive
    /\ part_decision' = [part_decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_alive, part_faulty, part_forward>>

ParticipantDie(p) ==
    /\ part_alive[p]
    /\ part_alive' = [part_alive EXCEPT ![p] = FALSE]
    /\ part_faulty' = [part_faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coord_alive, coord_faulty, coord_request,
                    coord_vote, coord_decision, coord_sent,
                    part_forward, part_decision>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ CoordSendRequest
    \/ \E p \in Participants : CoordCollectVote(p)
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in Participants : ParticipantVote(p)
    \/ \E p \in Participants : PreDecideFromCoord(p)
    \/ \E p,q \in Participants : PreDecideFromForward(p, q)
    \/ \E p,q \in Participants : Forward(p, q)
    \/ \E p \in Participants : Decide(p)
    \/ \E p \in Participants : AbortOnTimeout(p)
    \/ \E p \in Participants : ParticipantDie(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coord_alive, coord_faulty, coord_request,
                               coord_vote, coord_decision, coord_sent,
                               part_alive, part_faulty, part_forward,
                               part_decision>>

(*--------------------------------------------------------------------
  Safety invariants (as listed in the description)
--------------------------------------------------------------------*)
AC1 == \A p, q \in Participants :
          (part_decision[p] = commit) => (part_decision[q] # abort)

AC2 == \A p \in Participants :
          (part_decision[p] = commit) => 
            (\A r \in Participants : part_forward[r][r] = commit)

AC3 == \A p \in Participants :
          (part_decision[p] = abort) => 
            \/ \E r \in Participants : part_forward[r][r] = abort
            \/ \E r \in Participants : part_faulty[r]
            \/ coord_faulty

AC4 == \A p \in Participants :
          (part_decision[p] \in {commit, abort}) =>
            (part_decision[p]' = part_decision[p])

TypeInvNB == 
    /\ coord_alive \in BOOLEAN
    /\ coord_faulty \in BOOLEAN
    /\ coord_request \in BOOLEAN
    /\ coord_vote \in [Participants -> VoteVal]
    /\ coord_decision \in DecisionVal
    /\ coord_sent \in [Participants -> BOOLEAN]
    /\ part_alive \in [Participants -> BOOLEAN]
    /\ part_faulty \in [Participants -> BOOLEAN]
    /\ part_forward \in [Participants -> [Participants -> ForwardVal]]
    /\ part_decision \in [Participants -> DecisionVal]

(*--------------------------------------------------------------------
  Safety properties exposed as the required invariant
--------------------------------------------------------------------*)
Inv == AC1 /\ AC2 /\ AC3 /\ AC4 /\ TypeInvNB

=============================================================================