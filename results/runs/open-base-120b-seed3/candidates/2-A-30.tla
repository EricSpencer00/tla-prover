---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (declared in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES 
    \* coordinator state
    coordAlive,          \* BOOLEAN – TRUE when coordinator is up
    coordFaulty,         \* BOOLEAN – TRUE when coordinator has crashed (faulty)
    coordDecision,       \* one of {undecided, commit, abort}
    coordBroadcasted,    \* Set of participants that have already received the broadcast from the coordinator

    \* participant state
    alive,               \* Set of participants that are currently up
    faulty,              \* Set of participants that have crashed (faulty)
    vote,                \* [participants -> {yes,no,undecided}]
    decision,            \* [participants -> {undecided,commit,abort}]
    fwd                  \* [participants -> [participants -> {notsent,commit,abort}]]
    
\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcasted \subseteq participants

    /\ alive \subseteq participants
    /\ faulty = participants \ alive
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcasted = {}

    /\ alive = participants
    /\ faulty = {}
    /\ vote = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* COORDINATOR ACTIONS (inherited from ACP‑SB – only the ones needed here)
\* ----------------------------------------------------------------------
\* Coordinator decides (commit or abort) after collecting votes – simplified
CoordDecide ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ \* For simplicity we allow an arbitrary decision
       coordDecision' \in {commit, abort}
    /\ UNCHANGED << coordAlive, coordFaulty, coordBroadcasted,
                    alive, faulty, vote, decision, fwd >>

\* Coordinator broadcasts its decision to a single participant
CoordBroadcast ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
         /\ p \notin coordBroadcasted
         /\ coordBroadcasted' = coordBroadcasted \cup {p}
         /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                        alive, faulty, vote, decision, fwd >>
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    alive, faulty, vote, decision, fwd >>

\* Coordinator crashes
CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordBroadcasted,
                    alive, faulty, vote, decision, fwd >>

\* ----------------------------------------------------------------------
\* PARTICIPANT ACTIONS
\* ----------------------------------------------------------------------
\* A participant sends its vote to the coordinator – simplified
SendVote(p) ==
    /\ p \in alive
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes] \* (the actual vote value is irrelevant for the safety properties)
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, decision, fwd >>

\* Pre‑decide from coordinator broadcast
PreDecFromCoord(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ p \in coordBroadcasted
    /\ fwd' = [fwd EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, vote, decision >>

\* Pre‑decide from a forward sent by another participant
PreDecFromFwd(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ \E q \in participants :
         /\ q # p
         /\ fwd[q][p] # notsent
    /\ LET d == 
           IF \E q \in participants : q # p /\ fwd[q][p] = commit
              THEN commit
           ELSE abort
       IN fwd' = [fwd EXCEPT ![p][p] = d]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, vote, decision >>

\* Forward the pre‑decision to another participant
Forward(p, r) ==
    /\ p \in alive
    /\ fwd[p][p] # notsent                \* pre‑decision already stored
    /\ r \in participants
    /\ r # p
    /\ fwd[p][r] = notsent                \* not yet forwarded to r
    /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, vote, decision >>

\* Decide locally after having forwarded to everyone
Decide(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A r \in participants : r # p => fwd[p][r] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, vote, fwd >>

\* Abort on timeout when coordinator is dead and no information is reachable
AbortTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ \/ coordAlive = FALSE
       \/ coordFaulty = TRUE
    /\ \A q \in alive : fwd[q][q] = notsent
    /\ \A q \in participants \ alive :
         \A r \in alive : fwd[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    alive, faulty, vote, fwd >>

\* Participant crashes (becomes faulty)
ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision, coordBroadcasted,
                    vote, decision, fwd >>

\* ----------------------------------------------------------------------
\* COMBINED ACTION
\* ----------------------------------------------------------------------
ParticipantActions ==
    \E p \in participants :
        \/ SendVote(p)
        \/ PreDecFromCoord(p)
        \/ PreDecFromFwd(p)
        \/ \E r \in participants : r # p /\ Forward(p, r)
        \/ Decide(p)
        \/ AbortTimeout(p)
        \/ ParticipantDie(p)

Next ==
    \/ CoordDecide
    \/ CoordBroadcast
    \/ CoordDie
    \/ ParticipantActions

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<< coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, alive, faulty,
                         vote, decision, fwd >>

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
\* Type invariant (already defined)
\* Additional safety invariants could be added here if desired.
\* For the purpose of the .cfg file we expose only TypeInvNB.
\* ----------------------------------------------------------------------
\* THE END
\* ----------------------------------------------------------------------
====