---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\*=============================================================================
\* State variables
\*=============================================================================
VARIABLES 
    coordAlive,          \* Boolean: coordinator is up
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* {commit, abort, undecided}
    broadcastFromCoord,  \* [p \in participants -> BOOLEAN]  ; has p received broadcast from coordinator ?
    participantVote,     \* [p \in participants -> {yes,no}]
    voteSent,            \* [p \in participants -> BOOLEAN] ; has p sent its vote ?
    alive,               \* [p \in participants -> BOOLEAN] ; participant is up ?
    faulty,              \* [p \in participants -> BOOLEAN] ; participant has crashed ?
    fwd,                 \* [p \in participants -> [q \in participants -> {notsent, commit, abort}]]
    decision             \* [p \in participants -> {commit, abort, undecided}]

vars == << coordAlive, coordFaulty, coordDecision, broadcastFromCoord,
           participantVote, voteSent, alive, faulty, fwd, decision >>

\*=============================================================================
\* Helper definitions
\*=============================================================================
AllVotesSent == \A p \in participants : voteSent[p]

AllYes == \A p \in participants : participantVote[p] = yes

AllForwarded(p) == \A q \in participants : fwd[p][q] # notsent

PreDec(p) == fwd[p][p] \in {commit, abort}

\*=============================================================================
\* Initialization
\*=============================================================================
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcastFromCoord = [p \in participants |-> FALSE]
    /\ participantVote = [p \in participants |-> IF RandomElement({yes,no}) = yes THEN yes ELSE no]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decision = [p \in participants |-> undecided]

\*=============================================================================
\* Coordinator actions
\*=============================================================================
SendVote(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote,
                    alive, faulty, fwd, decision >>

MakeDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision = undecided
    /\ AllVotesSent
    /\ coordDecision' = IF AllYes THEN commit ELSE abort
    /\ UNCHANGED << broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, fwd, decision >>

BroadcastDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants : ~broadcastFromCoord[p]
    /\ LET p == Choose({q \in participants : ~broadcastFromCoord[q]})
       IN broadcastFromCoord' = [broadcastFromCoord EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    participantVote, voteSent,
                    alive, faulty, fwd, decision >>

CoordDie ==
    /\ coordAlive
    /\ coordFaulty = FALSE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, broadcastFromCoord,
                    participantVote, voteSent,
                    alive, faulty, fwd, decision >>

\*=============================================================================
\* Participant actions
\*=============================================================================
PreDecFromCoord(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ broadcastFromCoord[p]
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, decision >>

PreDecFromForward(p, q) ==
    /\ p,q \in participants
    /\ p # q
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ fwd[q][p] \in {commit, abort}
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, decision >>

Forward(p, q) ==
    /\ p,q \in participants
    /\ p # q
    /\ alive[p]
    /\ PreDec(p)
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, decision >>

Decide(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ PreDec(p)
    /\ AllForwarded(p)
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, fwd >>

AbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A r \in participants : ~broadcastFromCoord[r]
    /\ \A d \in participants :
          faulty[d] => \A a \in participants : alive[a] => fwd[d][a] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    alive, faulty, fwd >>

ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p]
    /\ faulty[p] = FALSE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    broadcastFromCoord, participantVote, voteSent,
                    fwd, decision >>

\*=============================================================================
\* Next-state relation
\*=============================================================================
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordDie
    \/ \E p \in participants : PreDecFromCoord(p)
    \/ \E p,q \in participants : PreDecFromForward(p,q)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\*=============================================================================
\* Specification
\*=============================================================================
SpecNB == Init /\ [][Next]_vars

\*=============================================================================
\* Type invariant
\*=============================================================================
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ broadcastFromCoord \in [participants -> BOOLEAN]
    /\ participantVote \in [participants -> {yes,no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decision \in [participants -> {commit, abort, undecided}]

=============================================================================