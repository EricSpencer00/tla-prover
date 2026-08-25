---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

(********************************************************************
  Constants (to be supplied by the .cfg file)
 ********************************************************************)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(********************************************************************
  State variables
 ********************************************************************)
VARIABLES coordFaulty,          \* TRUE iff the coordinator has crashed
          coordDecision,        \* one of {commit, abort, "none"}
          votes,                \* [p \in participants -> {yes,no,undecided}]
          forwarding,           \* [p \in participants -> [q \in participants -> {notsent, commit, abort}]]
          decision,             \* [p \in participants -> {undecided, commit, abort}]
          participantFaulty    \* SUBSET participants, the set of crashed participants

(********************************************************************
  Helper definitions
 ********************************************************************)
Alive(p) == p \\in participants \\ participantFaulty
AllAlive == participants \\ participantFaulty

CoordAlive == ~coordFaulty

CoordHasBroadcast == coordDecision \\in {commit, abort}

PreDecided(p) == forwarding[p][p] # notsent

AllForwarded(p) == \A q \in participants : q # p => forwarding[p][q] # notsent

AnyDecisionReceived(p) ==
    \E q \in participants :
        q # p /\ forwarding[q][p] # notsent

(********************************************************************
  Type invariants
 ********************************************************************)
TypeInvNB ==
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, "none"}
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \subseteq participants

(********************************************************************
  Initial state
 ********************************************************************)
Init ==
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ votes = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decision = [p \in participants |-> undecided]
    /\ participantFaulty = {}

(********************************************************************
  Coordinator actions
 ********************************************************************)

\* Coordinator may crash
CoordCrash ==
    /\ ~coordFaulty
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, forwarding, decision, participantFaulty>>

\* Coordinator decides (after all votes are in) and broadcasts
CoordDecide ==
    /\ CoordAlive
    /\ coordDecision = "none"
    /\ \A p \in participants : votes[p] # undecided
    /\ \* decision rule: abort if any no vote, otherwise commit
       IF \E p \in participants : votes[p] = no
          THEN coordDecision' = abort
          ELSE coordDecision' = commit
    /\ forwarding' = [p \in participants |-> 
                         [q \in participants |-> 
                             IF q = p
                                THEN coordDecision'
                                ELSE forwarding[p][q]]]
    /\ UNCHANGED <<coordFaulty, votes, decision, participantFaulty>>

(********************************************************************
  Participant actions (base actions)
 ********************************************************************)

\* A participant sends a vote (yes or no)
ParticipantSendVote(p) ==
    /\ Alive(p)
    /\ votes[p] = undecided
    /\ votes' = [votes EXCEPT ![p] = IF Random() % 2 = 0 THEN yes ELSE no]
    /\ UNCHANGED <<coordFaulty, coordDecision, forwarding, decision, participantFaulty>>

\* Participant crashes
ParticipantDie(p) ==
    /\ Alive(p)
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ UNCHANGED <<coordFaulty, coordDecision, votes, forwarding, decision>>

(********************************************************************
  Reliable broadcast actions (new/modified)
 ********************************************************************)

\* Pre‑decide from coordinator's broadcast (already reflected in forwarding)
\* (No separate action needed; handled by CoordDecide)

\* Pre‑decide from a forwarding participant
PreDecideFromFwd(p) ==
    /\ Alive(p)
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants : q # p /\ forwarding[q][p] # notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
    /\ UNCHANGED <<coordFaulty, coordDecision, votes, decision, participantFaulty>>

\* Forward the pre‑decision to another participant
Forward(p,q) ==
    /\ Alive(p) /\ Alive(q) /\ p # q
    /\ forwarding[p][p] \in {commit, abort}
    /\ forwarding[p][q] = notsent
    /\ LET d == forwarding[p][p] IN
       forwarding' = [forwarding EXCEPT 
                       ![p][q] = d,
                       ![q][q] = IF forwarding[q][q] = notsent THEN d ELSE forwarding[q][q]]
    /\ UNCHANGED <<coordFaulty, coordDecision, votes, decision, participantFaulty>>

\* Decide locally after having forwarded to everybody
Decide(p) ==
    /\ Alive(p)
    /\ decision[p] = undecided
    /\ forwarding[p][p] \in {commit, abort}
    /\ AllForwarded(p)
    /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordFaulty, coordDecision, votes, forwarding, participantFaulty>>

\* Abort on timeout (non‑blocking abort)
AbortTimeout(p) ==
    /\ Alive(p)
    /\ decision[p] = undecided
    /\ ~CoordAlive
    /\ \A r \in AllAlive : forwarding[r][r] = notsent
    /\ \A r \in participants : \A s \in participants : 
          (r # s /\ r \\in participantFaulty) => forwarding[r][s] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordFaulty, coordDecision, votes, forwarding, participantFaulty>>

(********************************************************************
  Next-state relation
 ********************************************************************)
Next ==
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordCrash
    \/ CoordDecide
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)

(********************************************************************
  Specification
 ********************************************************************)
SpecNB == Init /\ [][Next]_<<coordFaulty, coordDecision, votes, forwarding, decision, participantFaulty>>

(********************************************************************
  Theorem (type invariant holds)
 ********************************************************************)
THEOREM TypeInvariant == SpecNB => []TypeInvNB

====