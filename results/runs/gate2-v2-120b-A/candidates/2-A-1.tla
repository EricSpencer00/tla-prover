---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (set in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Enumerated state values
\* ----------------------------------------------------------------------
Values == {yes, no, undecided, commit, abort}
Decisions == {commit, abort}
FwdStatus == {notsent, commit, abort}
Alive == {"alive", "dead"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* participant vote: [participants -> Values]
    pDecision,      \* final decision:   [participants -> {"undecided", "commit", "abort"}]
    pForward,       \* forwarding table: [participants -> [participants -> FwdStatus]]
    coordState,     \* coordinator alive/faulty flag: "alive" or "dead"
    requestSent,    \* whether coordinator has sent request: BOOLEAN
    decisionMade    \* coordinator's decision: "undecided", "commit", "abort"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pVote \in [participants -> Values]
    /\ pDecision \in [participants -> {"undecided", "commit", "abort"}]
    /\ pForward \in [participants -> [participants -> FwdStatus]]
    /\ coordState \in {"alive", "dead"}
    /\ requestSent \in BOOLEAN
    /\ decisionMade \in {"undecided", "commit", "abort"}

AllDecided ==
    \A i \in participants : pDecision[i] # "undecided"

AnyCommit ==
    \E i \in participants : pDecision[i] = "commit"

AnyAbort ==
    \E i \in participants : pDecision[i] = "abort"

IsFaulty(i) ==
    pVote[i] = no \/ coordState = "dead"

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ pVote = [i \in participants |-> undecided]
    /\ pDecision = [i \in participants |-> "undecided"]
    /\ pForward = [i \in participants |-> [j \in participants |-> notsent]]
    /\ coordState = "alive"
    /\ requestSent = FALSE
    /\ decisionMade = "undecided"

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordState = "alive"
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<pVote, pDecision, pForward, coordState, decisionMade>>

CoordCollectVotes ==
    /\ requestSent = TRUE
    /\ decisionMade = "undecided"
    /\ \A i \in participants : pVote[i] # undecided
    /\ decisionMade' = IF \A i \in participants : pVote[i] = yes THEN "commit" ELSE "abort"
    /\ UNCHANGED <<pVote, pDecision, pForward, coordState, requestSent>>

CoordBroadcast ==
    /\ decisionMade \in {"commit", "abort"}
    /\ coordState = "alive"
    /\ \A i \in participants :
          pForward[i][i] = notsent
    /\ pForward' = [i \in participants |-> 
          [j \in participants |-> 
            IF i = j THEN 
               IF decisionMade = "commit" THEN commit ELSE abort
            ELSE pForward[i][j]]]
    /\ UNCHANGED <<pVote, pDecision, coordState, requestSent, decisionMade>>

CoordDie ==
    /\ coordState = "alive"
    /\ coordState' = "dead"
    /\ UNCHANGED <<pVote, pDecision, pForward, requestSent, decisionMade>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(i) ==
    /\ i \in participants
    /\ coordState = "alive"
    /\ pVote[i] = undecided
    /\ pVote' = [pVote EXCEPT ![i] = yes] \* for simplicity, always vote yes; nondeterminism not needed for safety
    /\ UNCHANGED <<pDecision, pForward, coordState, requestSent, decisionMade>>

PartPreDecideFromCoord(i) ==
    /\ i \in participants
    /\ pDecision[i] = "undecided"
    /\ pForward[i][i] \in {commit, abort}
    /\ pDecision' = [pDecision EXCEPT ![i] = 
            IF pForward[i][i] = commit THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<pVote, pForward, coordState, requestSent, decisionMade>>

PartPreDecideFromForward(i) ==
    /\ i \in participants
    /\ pDecision[i] = "undecided"
    /\ \E j \in participants :
          j # i /\ pForward[j][i] \in {commit, abort}
    /\ pDecision' = [pDecision EXCEPT ![i] = 
            IF \E j \in participants : j # i /\ pForward[j][i] = commit
               THEN "commit"
               ELSE "abort"]
    /\ UNCHANGED <<pVote, pForward, coordState, requestSent, decisionMade>>

PartForward(i, j) ==
    /\ i \in participants
    /\ j \in participants
    /\ i # j
    /\ pDecision[i] # "undecided"
    /\ pForward[i][j] = notsent
    /\ pForward' = [pForward EXCEPT ![i][j] = 
            IF pDecision[i] = "commit" THEN commit ELSE abort]
    /\ UNCHANGED <<pVote, pDecision, coordState, requestSent, decisionMade>>

PartDecide(i) ==
    /\ i \in participants
    /\ pDecision[i] # "undecided"
    /\ \A j \in participants : pForward[i][j] # notsent
    /\ UNCHANGED <<pVote, pDecision, pForward, coordState, requestSent, decisionMade>>

PartAbortOnTimeout(i) ==
    /\ i \in participants
    /\ pDecision[i] = "undecided"
    /\ coordState = "dead"
    /\ \A j \in participants :
          pForward[j][i] = notsent
    /\ pDecision' = [pDecision EXCEPT ![i] = "abort"]
    /\ UNCHANGED <<pVote, pForward, coordState, requestSent, decisionMade>>

PartDie(i) ==
    /\ i \in participants
    /\ pDecision[i] = "undecided"
    /\ pDecision' = [pDecision EXCEPT ![i] = "abort"]
    /\ UNCHANGED <<pVote, pForward, coordState, requestSent, decisionMade>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in participants : PartSendVote(i)
    \/ \E i \in participants : PartPreDecideFromCoord(i)
    \/ \E i \in participants : PartPreDecideFromForward(i)
    \/ \E i, j \in participants : i # j /\ PartForward(i, j)
    \/ \E i \in participants : PartDecide(i)
    \/ \E i \in participants : PartAbortOnTimeout(i)
    \/ \E i \in participants : PartDie(i)
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordBroadcast
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<pVote, pDecision, pForward, coordState, requestSent, decisionMade>>

\* ----------------------------------------------------------------------
\* Safety invariant (type-correctness + agreement)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ pVote \in [participants -> Values]
    /\ pDecision \in [participants -> {"undecided", "commit", "abort"}]
    /\ pForward \in [participants -> [participants -> FwdStatus]]
    /\ coordState \in {"alive", "dead"}
    /\ requestSent \in BOOLEAN
    /\ decisionMade \in {"undecided", "commit", "abort"}
    /\ \A i, j \in participants : 
         (pForward[i][j] = commit => pDecision[i] = "commit")
    /\ \A i, j \in participants :
         (pForward[i][j] = abort => pDecision[i] = "abort")
    /\ \A i, j \in participants :
         (pDecision[i] = "commit" => pDecision[j] # "abort")
    /\ \A i \in participants :
         (pDecision[i] = "abort" => 
            ( \E k \in participants : pVote[k] = no ) \/ coordState = "dead")
    /\ \A i \in participants :
         (pDecision[i] = "commit" => \A k \in participants : pVote[k] = yes)

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep module self‑contained)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeInvNB == SpecNB => []TypeInvNB

====