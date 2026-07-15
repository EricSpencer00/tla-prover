---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    participants,      \* Set of participant identifiers
    yes, no,           \* Vote values
    undecided, commit, abort, waiting, notsent \* Decision and forwarding status values

\*----------------------------------------------------------------------
\* State variables
\*----------------------------------------------------------------------
VARIABLES
    alive,             \* [proc -> BOOLEAN] alive status of each process (coordinator and participants)
    faulty,            \* [proc -> BOOLEAN] faulty flag of each process
    coordinator_state,\* "request", "broadcast", "decision", "dead"
    votes,             \* [participants -> {yes,no,undecided}]
    coord_votes,       \* Set of votes received by coordinator
    decision,          \* [participants -> {undecided, commit, abort}]
    forwarding,        \* [p \in participants |-> [q \in participants |-> notsent]]
    forward_sent,      \* [p \in participants |-> SUBSET participants]  \* set of q to which p has already forwarded
    voted,             \* [participants -> BOOLEAN]  \* true when vote already sent
    committed, aborted \* subsets of participants for convenience

\*----------------------------------------------------------------------
\* Helper definitions
\*----------------------------------------------------------------------
procSet == {"coord"} \cup participants

CoordinatorAlive == alive["coord"]
CoordinatorFaulty == faulty["coord"]
CoordinatorState == coordinator_state

\*----------------------------------------------------------------------
\* Initial state
\*----------------------------------------------------------------------
Init ==
    /\ alive = [proc \in procSet |-> IF proc = "coord" THEN TRUE ELSE TRUE]
    /\ faulty = [proc \in procSet |-> FALSE]
    /\ coordinator_state = "request"
    /\ votes = [p \in participants |-> undecided]
    /\ coord_votes = {}
    /\ decision = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ forward_sent = [p \in participants |-> {}]
    /\ voted = [p \in participants |-> FALSE]
    /\ committed = {}
    /\ aborted = {}

\*----------------------------------------------------------------------
\* Participant actions
\*----------------------------------------------------------------------
\* Base vote action (from ACP-SB)
Vote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ ~voted[p]
    /\ /\ votes[p] \in {yes, no}
       /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED << alive, faulty, coordinator_state, coord_votes,
                    decision, forwarding, forward_sent, committed, aborted >>

\* Pre‑decide from coordinator broadcast
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] = notsent
    /\ coordinator_state = "broadcast"
    /\ decision[p] \in {commit, abort}
    /\ forwarding' = [forwarding EXCEPT ![p][p] = decision[p]]
    /\ UNCHANGED << alive, faulty, coordinator_state, votes, coord_votes,
                    decision, forward_sent, voted, committed, aborted >>

\* Pre‑decide from another participant's forwarding
PreDecideFromFwd(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ forwarding[q][p] # notsent
          /\ forwarding[p][p] = forwarding[q][p]
    /\ UNCHANGED << alive, faulty, coordinator_state, votes, coord_votes,
                    decision, forward_sent, voted, committed, aborted >>

\* Forward to another participant
Forward(p, q) ==
    /\ p \in participants
    /\ q \in participants
    /\ p # q
    /\ alive[p]
    /\ forwarding[p][p] # notsent          \* p has a pre‑decision
    /\ q \notin forward_sent[p]           \* not yet forwarded to q
    /\ forwarding' = [forwarding EXCEPT ![q][p] = forwarding[p][p]]
    /\ forward_sent' = [forward_sent EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED << alive, faulty, coordinator_state, votes, coord_votes,
                    decision, voted, committed, aborted >>

\* Decide after having forwarded to all others
Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ forwarding[p][p] # notsent
    /\ forward_sent[p] = participants \ {p}
    /\ decision[p] = forwarding[p][p]
    /\ decision' = [decision EXCEPT ![p] = decision[p]]
    /\ IF decision[p] = commit THEN committed' = committed \cup {p}
       ELSE aborted' = aborted \cup {p}
    /\ UNCHANGED << alive, faulty, coordinator_state, votes, coord_votes,
                    forwarding, forward_sent, voted >>

\* Abort on timeout (coordinator dead, no broadcast, no forward)
AbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~CoordinatorAlive
    /\ coordinator_state # "broadcast"
    /\ \A q \in participants : forwarding[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ aborted' = aborted \cup {p}
    /\ UNCHANGED << alive, faulty, coordinator_state, votes, coord_votes,
                    forwarding, forward_sent, voted, committed >>

\* Crash (die)
Die(p) ==
    /\ p \in procSet
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ IF p = "coord" THEN coordinator_state' = "dead" ELSE UNCHANGED coordinator_state
    /\ UNCHANGED << votes, coord_votes, decision, forwarding,
                    forward_sent, voted, committed, aborted >>

\*----------------------------------------------------------------------
\* Coordinator actions (borrowed from the base protocol)
\*----------------------------------------------------------------------
\* Send request (nothing changes in this NB variant)
SendRequest ==
    /\ CoordinatorAlive
    /\ coordinator_state = "request"
    /\ coordinator_state' = "waiting"
    /\ UNCHANGED << alive, faulty, votes, coord_votes, decision,
                    forwarding, forward_sent, voted, committed, aborted >>

\* Receive vote
ReceiveVote ==
    /\ CoordinatorAlive
    /\ coordinator_state = "waiting"
    /\ \E p \in participants :
          /\ alive[p]
          /\ voted[p]
          /\ voting = votes[p]
          /\ coord_votes' = coord_votes \cup {voting}
    /\ IF Cardinality(coord_votes') = Cardinality(participants)
          THEN coordinator_state' = "decision"
          ELSE coordinator_state' = coordinator_state
    /\ UNCHANGED << alive, faulty, votes, decision,
                    forwarding, forward_sent, voted, committed, aborted >>

\* Make decision
MakeDecision ==
    /\ CoordinatorAlive
    /\ coordinator_state = "decision"
    /\ decisionToMake = IF no \in coord_votes THEN abort ELSE commit
    /\ decision' = [p \in participants |-> decisionToMake]
    /\ coordinator_state' = "broadcast"
    /\ UNCHANGED << alive, faulty, votes, coord_votes,
                    forwarding, forward_sent, voted, committed, aborted >>

\* Broadcast (coordinator simply marks that broadcast is in progress)
Broadcast ==
    /\ CoordinatorAlive
    /\ coordinator_state = "broadcast"
    /\ UNCHANGED << alive, faulty, votes, coord_votes, decision,
                    forwarding, forward_sent, voted, committed, aborted >>
    /\ coordinator_state' = "broadcast" \* stays until participants take pre‑decide

\*----------------------------------------------------------------------
\* Next-state relation
\*----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : Vote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromFwd(p)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in procSet : Die(p)
    \/ SendRequest
    \/ ReceiveVote
    \/ MakeDecision
    \/ Broadcast

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<alive, faulty, coordinator_state, votes,
                     coord_votes, decision, forwarding,
                     forward_sent, voted, committed, aborted>>

\*----------------------------------------------------------------------
\* Type invariant (ensures variables stay within their domains)
\*----------------------------------------------------------------------
TypeInvNB ==
    /\ alive \in [procSet -> BOOLEAN]
    /\ faulty \in [procSet -> BOOLEAN]
    /\ coordinator_state \in {"request", "waiting", "decision", "broadcast", "dead"}
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ coord_votes \subseteq {yes, no}
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ forward_sent \in [participants -> SUBSET participants]
    /\ voted \in [participants -> BOOLEAN]
    /\ committed \subseteq participants
    /\ aborted \subseteq participants
    /\ committed \cap aborted = {}

\*----------------------------------------------------------------------
\* Safety invariant AC1 (Agreement)
\*----------------------------------------------------------------------
AC1_Agreement ==
    \A p, q \in participants :
        (decision[p] = commit) => (decision[q] = commit)

\*----------------------------------------------------------------------
\* Safety invariant AC2 (Commit validity)
\*----------------------------------------------------------------------
AC2_CommitValidity ==
    \A p \in participants :
        (decision[p] = commit) => \A q \in participants : votes[q] = yes

\*----------------------------------------------------------------------
\* Safety invariant AC3 (Abort validity)
\*----------------------------------------------------------------------
AC3_AbortValidity ==
    \A p \in participants :
        (decision[p] = abort) =>
            \/ \E q \in participants : votes[q] = no
            \/ \E q \in participants : faulty[q]
            \/ faulty["coord"]

\*----------------------------------------------------------------------
\* Safety invariant AC4 (Irrevocability)
\*----------------------------------------------------------------------
AC4_Irrevocable ==
    /\ committed = committed \cup { p \in participants : decision[p] = commit }
    /\ aborted   = aborted   \cup { p \in participants : decision[p] = abort }

\*----------------------------------------------------------------------
\* Combined safety invariant (the .cfg expects the name TypeInvNB, but we also
\* expose the AC* invariants for readability; they are not required by the cfg)
\*----------------------------------------------------------------------
\* The cfg will check TypeInvNB; the AC* properties are provided for completeness.
\*----------------------------------------------------------------------
\* The module ends here.
\*----------------------------------------------------------------------
====