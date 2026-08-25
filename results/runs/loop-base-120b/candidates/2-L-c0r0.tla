---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE if coordinator is up
    coordFaulty,         \* TRUE if coordinator has crashed (faulty)
    coordDecision,       \* {commit, abort, undecided}
    coordBroadcasted,    \* TRUE after coordinator has broadcasted its decision
    votes,               \* [participants -> {yes,no,undecided}]
    pAlive,              \* [participants -> BOOLEAN]  (TRUE = up)
    pFaulty,             \* [participants -> BOOLEAN]  (TRUE = crashed)
    pDecision,           \* [participants -> {commit,abort,undecided}]
    voteSent,            \* [participants -> BOOLEAN]  (TRUE = vote already sent)
    forwardTable         \* [participants -> [participants -> {notsent,commit,abort}]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
           votes, pAlive, pFaulty, pDecision, voteSent, forwardTable >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = FALSE
    /\ votes = [p \in participants |-> undecided]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (simplified)
\* ----------------------------------------------------------------------
\* Collect votes (no explicit action – votes are set by participants)
\* Make decision when all votes are known
MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votes[p] # undecided
    /\ IF \A p \in participants : votes[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordBroadcasted,
                    votes, pAlive, pFaulty, pDecision, voteSent, forwardTable >>

\* Broadcast the decision (reliable broadcast is realized by participants)
Broadcast ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ ~coordBroadcasted
    /\ coordBroadcasted' = TRUE
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    votes, pAlive, pFaulty, pDecision, voteSent, forwardTable >>

\* Coordinator may crash
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, pDecision, voteSent, forwardTable >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* Send vote (yes or no) to coordinator
SendVote(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ ~voteSent[p]
    /\ votes' = [votes EXCEPT ![p] = IF RandomChoice({yes,no}) = yes THEN yes ELSE no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    pAlive, pFaulty, pDecision, forwardTable >>

\* Pre‑decide from coordinator's broadcast
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ coordBroadcasted
    /\ coordDecision \in {commit, abort}
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, pDecision, voteSent >>

\* Pre‑decide from another participant's forwarding
PreDecideFromForward(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ forwardTable[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit,abort} :
                \E q \in participants : q # p /\ forwardTable[q][p] = d
       IN forwardTable' = [forwardTable EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, pDecision, voteSent >>

\* Forward pre‑decision to a specific participant
Forward(p,q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ pAlive[p]
    /\ forwardTable[p][p] \in {commit, abort}
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, pDecision, voteSent >>

\* Decide after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ forwardTable[p][p] \in {commit, abort}
    /\ \A q \in participants : forwardTable[p][q] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, voteSent, forwardTable >>

\* Abort on timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants :
          forwardTable[q][p] = notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pAlive, pFaulty, voteSent, forwardTable >>

\* Participant crashes
ParticipantDie(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    votes, pDecision, voteSent, forwardTable >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordBroadcasted \in BOOLEAN
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {commit, abort, undecided}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====