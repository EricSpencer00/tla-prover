---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    CoordAlive,          \* TRUE if coordinator is up
    CoordFaulty,         \* TRUE if coordinator has crashed
    CoordDecision,       \* {commit, abort, undecided}
    Vote,                \* mapping participants -> {yes,no,undecided}
    SentVote,            \* mapping participants -> BOOLEAN
    Decision,            \* mapping participants -> {commit,abort,undecided}
    Alive,               \* mapping participants -> BOOLEAN
    Faulty,              \* mapping participants -> BOOLEAN
    Fwd                  \* forwarding table: [p][q] in {notsent,commit,abort}

/\* --------------------------------------------------------------------- *\
\*   Initial state                                                       *\
\* --------------------------------------------------------------------- */
Init ==
    /\ CoordAlive = TRUE
    /\ CoordFaulty = FALSE
    /\ CoordDecision = undecided
    /\ Vote = [p \in participants |-> undecided]
    /\ SentVote = [p \in participants |-> FALSE]
    /\ Decision = [p \in participants |-> undecided]
    /\ Alive = [p \in participants |-> TRUE]
    /\ Faulty = [p \in participants |-> FALSE]
    /\ Fwd = [p \in participants |-> [q \in participants |-> notsent]]

/\* --------------------------------------------------------------------- *\
\*   Coordinator actions                                                *\
\* --------------------------------------------------------------------- */
MakeDecision ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ \A p \in participants: SentVote[p] = TRUE
    /\ CoordDecision' = IF \A p \in participants: Vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << CoordFaulty, Vote, SentVote, Decision, Alive, Faulty, Fwd >>

Broadcast ==
    /\ CoordAlive
    /\ CoordDecision \in {commit, abort}
    /\ \E p \in participants:
          /\ Alive[p] /\ ~Faulty[p]
          /\ Fwd[p][p] = notsent
          /\ Fwd' = [Fwd EXCEPT ![p][p] = CoordDecision]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision, Vote,
                         SentVote, Decision, Alive, Faulty >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ CoordFaulty' = TRUE
    /\ UNCHANGED << CoordDecision, Vote, SentVote, Decision,
                   Alive, Faulty, Fwd >>

/\* --------------------------------------------------------------------- *\
\*   Participant actions                                                *\
\* --------------------------------------------------------------------- */
SendVote ==
    \/ (\E p \in participants:
            /\ Alive[p] /\ ~Faulty[p]
            /\ Vote[p] = undecided
            /\ Vote' = [Vote EXCEPT ![p] = yes]
            /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
            /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                           Decision, Alive, Faulty, Fwd >>)
    \/ (\E p \in participants:
            /\ Alive[p] /\ ~Faulty[p]
            /\ Vote[p] = undecided
            /\ Vote' = [Vote EXCEPT ![p] = no]
            /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
            /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                           Decision, Alive, Faulty, Fwd >>)

PreDecideFromFwd ==
    /\ \E p, q \in participants:
          /\ p # q
          /\ Alive[p] /\ ~Faulty[p]
          /\ Fwd[q][p] \in {commit, abort}
          /\ Fwd[p][p] = notsent
          /\ Fwd' = [Fwd EXCEPT ![p][p] = Fwd[q][p]]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                         Vote, SentVote, Decision, Alive, Faulty >>

Forward ==
    /\ \E p, r \in participants:
          /\ p # r
          /\ Alive[p] /\ ~Faulty[p]
          /\ Fwd[p][p] \in {commit, abort}
          /\ Fwd[p][r] = notsent
          /\ Fwd' = [Fwd EXCEPT ![p][r] = Fwd[p][p]]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                         Vote, SentVote, Decision, Alive, Faulty >>

Decide ==
    /\ \E p \in participants:
          /\ Alive[p] /\ ~Faulty[p]
          /\ Decision[p] = undecided
          /\ Fwd[p][p] \in {commit, abort}
          /\ \A r \in participants: Fwd[p][r] # notsent
          /\ Decision' = [Decision EXCEPT ![p] = Fwd[p][p]]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                         Vote, SentVote, Alive, Faulty, Fwd >>

AbortTimeout ==
    /\ \E p \in participants:
          /\ Alive[p] /\ ~Faulty[p]
          /\ Decision[p] = undecided
          /\ CoordAlive = FALSE
          /\ \A q \in participants: (Alive[q] => Fwd[q][q] = notsent)
          /\ \A q \in participants:
                ( ~Alive[q] => \A r \in participants:
                                   (Alive[r] => Fwd[q][r] = notsent) )
          /\ Decision' = [Decision EXCEPT ![p] = abort]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                         Vote, SentVote, Alive, Faulty, Fwd >>

ParticipantDie ==
    /\ \E p \in participants:
          /\ Alive[p]
          /\ Alive' = [Alive EXCEPT ![p] = FALSE]
          /\ Faulty' = [Faulty EXCEPT ![p] = TRUE]
          /\ UNCHANGED << CoordAlive, CoordFaulty, CoordDecision,
                         Vote, SentVote, Decision, Fwd >>

/\* --------------------------------------------------------------------- *\
\*   Next-state relation                                                *\
\* --------------------------------------------------------------------- */
Next ==
    \/ MakeDecision
    \/ Broadcast
    \/ PreDecideFromFwd
    \/ Forward
    \/ Decide
    \/ AbortTimeout
    \/ SendVote
    \/ ParticipantDie
    \/ CoordDie

VARIABLES vars == << CoordAlive, CoordFaulty, CoordDecision, Vote,
                    SentVote, Decision, Alive, Faulty, Fwd >>

SpecNB == Init /\ [][Next]_vars

/\* --------------------------------------------------------------------- *\
\*   Type invariant                                                     *\
\* --------------------------------------------------------------------- */
TypeInvNB ==
    /\ participants # {}
    /\ CoordAlive \in BOOLEAN
    /\ CoordFaulty \in BOOLEAN
    /\ CoordDecision \in {commit, abort, undecided}
    /\ Vote \in [participants -> {yes, no, undecided}]
    /\ SentVote \in [participants -> BOOLEAN]
    /\ Decision \in [participants -> {commit, abort, undecided}]
    /\ Alive \in [participants -> BOOLEAN]
    /\ Faulty \in [participants -> BOOLEAN]
    /\ Fwd \in [participants -> [participants -> {notsent, commit, abort}]]

====