---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

\* ------------------------------------------------------------------------
\* CONSTANTS (to be supplied by the configuration)
\* ------------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ------------------------------------------------------------------------
\* Derived sets
\* ------------------------------------------------------------------------
VoteVal == {yes, no, "undef"}
DecisionVal == {commit, abort, "none"}

\* ------------------------------------------------------------------------
\* VARIABLES
\* ------------------------------------------------------------------------
VARIABLES 
    coordAlive,      \* TRUE if coordinator is up
    coordFaulty,     \* TRUE if coordinator has crashed
    coordDecision,   \* coordinator's final decision (or "none")
    vote,            \* [p \in participants |-> VoteVal]  (participants' votes)
    voteSent,        \* [p \in participants |-> BOOLEAN]  (has participant sent its vote?)
    pAlive,          \* [p \in participants |-> BOOLEAN]  (alive status)
    pFaulty,         \* [p \in participants |-> BOOLEAN]  (faulty flag)
    pDecision,       \* [p \in participants |-> {undecided, commit, abort}]
    forwardTable     \* [p \in participants |-> [q \in participants |-> {notsent, commit, abort}]]

\* ------------------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------------------
\* Set of all variables for the stuttering relation
vars == << coordAlive, coordFaulty, coordDecision,
           vote, voteSent,
           pAlive, pFaulty,
           pDecision,
           forwardTable >>

\* A participant has already stored a pre‑decision
PreDecided(p) == forwardTable[p][p] # notsent

\* All participants to which p has already forwarded its pre‑decision
AllForwarded(p) == \A q \in participants : forwardTable[p][q] # notsent

\* ------------------------------------------------------------------------
\* INITIAL STATE
\* ------------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ vote = [p \in participants |-> "undef"]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

\* ------------------------------------------------------------------------
\* COORDINATOR ACTIONS
\* ------------------------------------------------------------------------
\* Participant sends its vote (yes or no) to the coordinator
SendVote(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ vote[p]' \in {yes, no}
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, pAlive, pFaulty,
                   pDecision, forwardTable >>

\* Coordinator decides after all votes are in
DecideCoord ==
    /\ coordAlive = TRUE
    /\ \A p \in participants : voteSent[p] = TRUE
    /\ IF \A p \in participants : vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty,
                   vote, voteSent,
                   pAlive, pFaulty,
                   pDecision, forwardTable >>

\* Coordinator crashes
CrashCoord ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, vote, voteSent,
                   pAlive, pFaulty,
                   pDecision, forwardTable >>

\* ------------------------------------------------------------------------
\* PARTICIPANT ACTIONS
\* ------------------------------------------------------------------------
\* Pre‑decide from coordinator's broadcast
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ coordDecision \in {commit, abort}
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pAlive, pFaulty,
                   pDecision >>

\* Pre‑decide from forwarding by another participant
PreDecideFromForward(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forwardTable[q][p] \in {commit, abort}
    /\ LET d == 
          CHOOSE d \in {commit, abort} : 
            \E q \in participants : q # p /\ forwardTable[q][p] = d
       IN forwardTable' = [forwardTable EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pAlive, pFaulty,
                   pDecision >>

\* Forward pre‑decision to another participant q
Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ pAlive[p] = TRUE
    /\ forwardTable[p][p] \in {commit, abort}
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pAlive, pFaulty,
                   pDecision >>

\* Decide locally after having forwarded to everyone
Decide(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ forwardTable[p][p] \in {commit, abort}
    /\ AllForwarded(p)
    /\ pDecision' = [pDecision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pAlive, pFaulty,
                   forwardTable >>

\* Abort on timeout (coordinator dead and no decision reachable)
AbortTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          forwardTable[q][p] = notsent
    /\ \A r \in participants :
          ~ (pAlive[r] = FALSE /\ \E s \in participants : forwardTable[r][s] \in {commit, abort})
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pAlive, pFaulty,
                   forwardTable >>

\* Participant crashes
Crash(p) ==
    /\ p \in participants
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                   vote, voteSent,
                   pDecision,
                   forwardTable >>

\* ------------------------------------------------------------------------
\* COMBINED NEXT RELATION
\* ------------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ DecideCoord
    \/ CrashCoord
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Crash(p)

\* ------------------------------------------------------------------------
\* SPECIFICATION
\* ------------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ------------------------------------------------------------------------
\* TYPE INVARIANT
\* ------------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in DecisionVal
    /\ vote \in [participants -> VoteVal]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

\* ------------------------------------------------------------------------
\* SAFETY PROPERTIES
\* ------------------------------------------------------------------------
\* Agreement: no two participants decide differently
Agreement ==
    \A p, q \in participants :
        (pDecision[p] # undecided /\ qDecision[q] # undecided) => 
        pDecision[p] = qDecision[q]

\* Commit validity
CommitValid ==
    \A p \in participants :
        (pDecision[p] = commit) => 
        \A r \in participants : vote[r] = yes

\* Abort validity
AbortValid ==
    \A p \in participants :
        (pDecision[p] = abort) => 
        (\E r \in participants : vote[r] = no) \/ ( \E r \in participants : pFaulty[r] ) \/ coordFaulty

\* Irrevocability
Irrevocable ==
    \A p \in participants :
        (pDecision[p] = commit \/ pDecision[p] = abort) => 
        [] (pDecision[p]' = pDecision[p])

\* ------------------------------------------------------------------------
\* LIVENESS PROPERTIES (expressed as temporal formulas)
\* ------------------------------------------------------------------------
\* AC3 liveness (eventual decision or fault)
LivenessAC3 ==
    <> ( \A p \in participants : pDecision[p] # undecided \/ \E p \in participants : pFaulty[p] \/ coordFaulty )

\* AC5 non‑blocking termination
NonBlockingTermination ==
    \A p \in participants :
        pAlive[p] => <> (pDecision[p] # undecided)

\* ------------------------------------------------------------------------
\* THEOREMS (to be checked by TLC)
\* ------------------------------------------------------------------------
THEOREM SpecNB => []TypeInvNB
THEOREM SpecNB => []Agreement
THEOREM SpecNB => []CommitValid
THEOREM SpecNB => []AbortValid
THEOREM SpecNB => []Irrevocable
THEOREM SpecNB => LivenessAC3
THEOREM SpecNB => NonBlockingTermination

====