---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
VoteSet == {yes, no}
DecisionSet == {commit, abort, undecided}
FwdState == {notsent, commit, abort}
AliveStatus == {"alive", "dead"}

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    coordAlive,                \* "alive" or "dead"
    coordFaulty,               \* BOOLEAN
    coordDecision,             \* commit, abort, or undef (undecided)
    coordVotes,                \* [p \in participants -> VoteSet]
    coordBroadcasted,          \* [p \in participants -> BOOLEAN]

    pAlive,                    \* [p \in participants -> AliveStatus]
    pFaulty,                   \* [p \in participants -> BOOLEAN]
    pDecision,                 \* [p \in participants -> DecisionSet]
    pVoteSent,                 \* [p \in participants -> BOOLEAN]
    pFwd,                      \* [p \in participants -> [q \in participants -> FwdState]]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AllForwarded(p) == \A q \in participants : pFwd[p][q] # notsent

PreDecided(p) == pFwd[p][p] # notsent

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ coordAlive = "alive"
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordVotes = [p \in participants |-> no] \* arbitrary initialization
    /\ coordBroadcasted = [p \in participants |-> FALSE]

    /\ pAlive = [p \in participants |-> "alive"]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pVoteSent = [p \in participants |-> FALSE]
    /\ pFwd = [p \in participants |-> [q \in participants |-> notsent]]

(*-----------------------------------------------------------------
  Coordinator actions (inherited from ACP-SB)
-----------------------------------------------------------------*)
CoordSendReq ==
    /\ coordAlive = "alive"
    /\ coordDecision = undecided
    /\ coordBroadcasted = [p \in participants |-> FALSE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVotes,
                    pAlive, pFaulty, pDecision, pVoteSent, pFwd>>

CoordCollectVotes ==
    /\ coordAlive = "alive"
    /\ \A p \in participants : pVoteSent[p]
    /\ coordVotes' = [p \in participants |-> IF pFaulty[p] THEN no ELSE
                       IF pDecision[p] = commit THEN yes ELSE no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, pAlive, pFaulty,
                    pDecision, pVoteSent, pFwd>>

CoordMakeDecision ==
    /\ coordAlive = "alive"
    /\ coordDecision = undecided
    /\ coordDecision' = IF \A p \in participants : coordVotes[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordVotes,
                    coordBroadcasted, pAlive, pFaulty,
                    pDecision, pVoteSent, pFwd>>

CoordBroadcast ==
    /\ coordAlive = "alive"
    /\ coordDecision # undecided
    /\ \E p \in participants : ~coordBroadcasted[p]
    /\ coordBroadcasted' = [q \in participants |-> TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, pAlive, pFaulty,
                    pDecision, pVoteSent, pFwd>>

CoordDie ==
    /\ coordAlive = "alive"
    /\ coordAlive' = "dead"
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pDecision, pVoteSent, pFwd>>

(*-----------------------------------------------------------------
  Participant actions
-----------------------------------------------------------------*)
ParticipantVote(p) ==
    /\ pAlive[p] = "alive"
    /\ pVoteSent[p] = FALSE
    /\ pDecision[p] = undecided
    /\ pFwd[p][p] = notsent
    /\ pDecision' = [q \in participants |-> IF q = p THEN undecided ELSE pDecision[q]]
    /\ pVoteSent' = [q \in participants |-> IF q = p THEN TRUE ELSE pVoteSent[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pFwd>>

PreDecideFromCoord(p) ==
    /\ pAlive[p] = "alive"
    /\ pFwd[p][p] = notsent
    /\ coordBroadcasted[p] = TRUE
    /\ coordDecision # undecided
    /\ pFwd' = [q \in participants |-> 
                IF q = p 
                THEN [r \in participants |-> IF r = p THEN 
                        (IF coordDecision = commit THEN commit ELSE abort) 
                      ELSE pFwd[p][r]]
                ELSE pFwd[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pDecision, pVoteSent>>

PreDecideFromFwd(p) ==
    /\ pAlive[p] = "alive"
    /\ pFwd[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ pFwd[q][p] # notsent
    /\ pFwd' = [q \in participants |-> 
                IF q = p 
                THEN [r \in participants |-> IF r = p THEN pFwd[CHOOSE q \in participants: q # p /\ pFwd[q][p] # notsent][p]
                                                 ELSE pFwd[p][r]]
                ELSE pFwd[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pDecision, pVoteSent>>

Forward(p, q) ==
    /\ pAlive[p] = "alive"
    /\ pAlive[q] = "alive"
    /\ pFwd[p][p] # notsent
    /\ pFwd[p][q] = notsent
    /\ pFwd' = [i \in participants |-> 
                IF i = p 
                THEN [j \in participants |-> IF j = q THEN pFwd[p][p] ELSE pFwd[p][j]]
                ELSE pFwd[i]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pDecision, pVoteSent>>

Decide(p) ==
    /\ pAlive[p] = "alive"
    /\ pFwd[p][p] # notsent
    /\ AllForwarded(p)
    /\ pDecision' = [q \in participants |-> IF q = p THEN 
                        (IF pFwd[p][p] = commit THEN commit ELSE abort) 
                     ELSE pDecision[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pVoteSent, pFwd>>

AbortTimeout(p) ==
    /\ pAlive[p] = "alive"
    /\ pDecision[p] = undecided
    /\ coordAlive = "dead"
    /\ \A q \in participants : pAlive[q] = "dead" => 
          ~(\E r \in participants : pFwd[r][q] # notsent)
    /\ pDecision' = [q \in participants |-> IF q = p THEN abort ELSE pDecision[q]]
    /\ pFwd' = [i \in participants |-> 
                IF i = p 
                THEN [j \in participants |-> notsent]
                ELSE pFwd[i]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pAlive, pFaulty, pVoteSent>>

ParticipantDie(p) ==
    /\ pAlive[p] = "alive"
    /\ pAlive' = [q \in participants |-> IF q = p THEN "dead" ELSE pAlive[q]]
    /\ pFaulty' = [q \in participants |-> IF q = p THEN TRUE ELSE pFaulty[q]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcasted,
                    pDecision, pVoteSent, pFwd>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ CoordSendReq
    \/ CoordCollectVotes
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in participants : ParticipantVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         coordVotes, coordBroadcasted,
                         pAlive, pFaulty, pDecision,
                         pVoteSent, pFwd>>

(*-----------------------------------------------------------------
  Type invariant (kept simple for model checking)
-----------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in {"alive", "dead"}
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordVotes \in [participants -> VoteSet]
    /\ coordBroadcasted \in [participants -> BOOLEAN]

    /\ pAlive \in [participants -> AliveStatus]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> DecisionSet]
    /\ pVoteSent \in [participants -> BOOLEAN]
    /\ pFwd \in [participants -> [participants -> FwdState]]

(*-----------------------------------------------------------------
  Safety properties (as invariants)
-----------------------------------------------------------------*)
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        pDecision[p] = commit => \A q \in participants : pDecision[q] = commit

AbortValidity ==
    \A p \in participants :
        pDecision[p] = abort =>
        (\E q \in participants : pDecision[q] = abort /\ pDecision[q] # commit) \/
        (\E q \in participants : pFaulty[q]) \/
        coordFaulty

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit \/ pDecision[p] = abort) =>
        (pDecision[p]' = pDecision[p])

(*-----------------------------------------------------------------
  Liveness properties (as temporal formulas)
-----------------------------------------------------------------*)
AC3Liveness == <> ( \A p \in participants : pDecision[p] # undecided
                    \/ \E p \in participants : pFaulty[p]
                    \/ coordFaulty)

NonBlockingTermination == [] ( \A p \in participants :
                               (pAlive[p] = "alive" /\ ~pFaulty[p]) => <> (pDecision[p] # undecided) )

=============================================================================