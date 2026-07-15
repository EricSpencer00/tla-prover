---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (must be supplied in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Participant == participants
ParticipantSet == participants

Decision == {commit, abort}
Vote == {yes, no}
DecisionOrUndecided == Decision \cup {undecided}
ForwardStatus == {notsent, commit, abort}

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* TRUE if coordinator is alive
    coordFaulty,         \* TRUE if coordinator is faulty
    coordDecision,      \* coordinator's decision (commit/abort) or FALSE if none yet
    partAlive,          \* [p \in participants -> BOOLEAN]
    partFaulty,         \* [p \in participants -> BOOLEAN]
    partVote,           \* [p \in participants -> {yes, no}]
    partDecision,       \* [p \in participants -> {undecided, commit, abort}]
    partForward,        \* [p \in participants -> [q \in participants -> ForwardStatus]]
    partPreDecided,     \* [p \in participants -> BOOLEAN]  \* has participant stored a pre‑decision?
    partPreDecision,    \* [p \in participants -> {commit, abort}]
    partVotesSent       \* [p \in participants -> BOOLEAN]  \* has p sent its vote to coord?

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AliveSet == { p \in participants : partAlive[p] }

AllForwarded(p) == \A q \in participants : q /= p => partForward[p][q] # notsent

(*-----------------------------------------------------------------
  Type invariant (used as the only invariant required by the cfg)
-----------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {FALSE} \cup Decision
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> Vote]
    /\ partDecision \in [participants -> DecisionOrUndecided]
    /\ partForward \in [participants -> [participants -> ForwardStatus]]
    /\ partPreDecided \in [participants -> BOOLEAN]
    /\ partPreDecision \in [participants -> Decision]
    /\ partVotesSent \in [participants -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = FALSE
    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> yes]        \* voters may be chosen nondeterministically later
    /\ partDecision = [p \in participants |-> undecided]
    /\ partForward = [p \in participants |-> [q \in participants |-> notsent]]
    /\ partPreDecided = [p \in participants |-> FALSE]
    /\ partPreDecision = [p \in participants |-> commit]   \* placeholder, never used until pre‑decided
    /\ partVotesSent = [p \in participants |-> FALSE]

(*-----------------------------------------------------------------
  Coordinator actions (inherited from ACP‑SB)
-----------------------------------------------------------------*)
CoordSendDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision = FALSE
    /\ coordDecision' \in Decision
    /\ UNCHANGED <<coordAlive, coordFaulty, partAlive, partFaulty,
                  partVote, partDecision, partForward,
                  partPreDecided, partPreDecision, partVotesSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, partAlive, partFaulty,
                  partVote, partDecision, partForward,
                  partPreDecided, partPreDecision, partVotesSent>>

(*-----------------------------------------------------------------
  Participant actions (base + new)
-----------------------------------------------------------------*)
SendVote(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ ~partVotesSent[p]
    /\ partVotesSent' = [partVotesSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote, partDecision,
                  partForward, partPreDecided, partPreDecision>>

PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ ~partPreDecided[p]
    /\ coordDecision \in Decision
    /\ partPreDecided' = [partPreDecided EXCEPT ![p] = TRUE]
    /\ partPreDecision' = [partPreDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote,
                  partDecision, partForward, partVotesSent>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ ~partPreDecided[p]
    /\ \E q \in participants :
          q # p /\ partForward[q][p] # notsent
    /\ LET d == IF \E q \in participants :
                     q # p /\ partForward[q][p] = commit
                 THEN commit
                 ELSE abort IN
       /\ partPreDecided' = [partPreDecided EXCEPT ![p] = TRUE]
       /\ partPreDecision' = [partPreDecision EXCEPT ![p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote,
                  partDecision, partForward, partVotesSent>>

Forward(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ partPreDecided[p]
    /\ \E q \in participants :
          q # p /\ partForward[p][q] = notsent
    /\ LET q == CHOOSE r \in participants :
                    r # p /\ partForward[p][r] = notsent IN
       /\ partForward' = [partForward EXCEPT ![p][q] = partPreDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote,
                  partDecision, partPreDecided, partPreDecision,
                  partVotesSent>>

Decide(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ partPreDecided[p]
    /\ AllForwarded(p)
    /\ partDecision[p] = undecided
    /\ partDecision' = [partDecision EXCEPT ![p] = partPreDecision[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote,
                  partForward, partPreDecided, partPreDecision,
                  partVotesSent>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ partDecision[p] = undecided
    /\ ~coordAlive
    /\ ~\E i \in participants :
           (coordAlive /\ coordDecision \in Decision /\ partForward[i][p] # notsent)
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partAlive, partFaulty, partVote,
                  partForward, partPreDecided, partPreDecision,
                  partVotesSent>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  partVote, partDecision, partForward,
                  partPreDecided, partPreDecision, partVotesSent>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : PreDecideFromForward(p)
    \/ \E p \in participants : Forward(p)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordSendDecision
    \/ CoordDie

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                            partAlive, partFaulty, partVote,
                            partDecision, partForward,
                            partPreDecided, partPreDecision,
                            partVotesSent>>

====