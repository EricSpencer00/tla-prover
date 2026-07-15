---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

\*---------------------------------------------------------------------- 
\* Constants (values provided by the .cfg file)
\*---------------------------------------------------------------------- 
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\*---------------------------------------------------------------------- 
\* Derived sets
\*---------------------------------------------------------------------- 
Values == {yes, no}
Decisions == {commit, abort}
ParticipantStates == {waiting, undecided, commit, abort}
ForwardStatus == {notsent, commit, abort}

\*---------------------------------------------------------------------- 
\* Type invariant helper
\*---------------------------------------------------------------------- 
ParticipantState == [ 
    vote      : participants -> Values,
    alive     : participants -> BOOLEAN,
    decision  : participants -> ParticipantStates,
    faulty    : participants -> BOOLEAN,
    voteSent  : participants -> BOOLEAN,
    fwd       : participants -> [participants -> ForwardStatus]
]

CoordState == [
    alive        : BOOLEAN,
    faulty       : BOOLEAN,
    requestSent  : BOOLEAN,
    votesRecv    : participants -> BOOLEAN,
    decisionMade : BOOLEAN,
    broadcast    : BOOLEAN,
    decision     : Decideset
]

Decideset == {commit, abort, ""}   \* empty string denotes "no decision yet"

\*---------------------------------------------------------------------- 
\* Variables
\*---------------------------------------------------------------------- 
VARIABLES coord, part

\*---------------------------------------------------------------------- 
\* Initial state
\*---------------------------------------------------------------------- 
InitCoord == [
    alive        |-> TRUE,
    faulty       |-> FALSE,
    requestSent  |-> FALSE,
    votesRecv    |-> [p \in participants |-> FALSE],
    decisionMade |-> FALSE,
    broadcast    |-> FALSE,
    decision     |-> ""
]

InitPart == [p \in participants |-> [
    vote      |-> no,               \* arbitrary, will be set by vote actions
    alive     |-> TRUE,
    decision  |-> undecided,
    faulty    |-> FALSE,
    voteSent  |-> FALSE,
    fwd       |-> [q \in participants |-> notsent]
]]

Init == /\ coord = InitCoord
        /\ part  = InitPart

\*---------------------------------------------------------------------- 
\* Coordinator actions (inherited from ACP-SB)
\*---------------------------------------------------------------------- 
SendRequest ==
    /\ coord.alive
    /\ ~coord.requestSent
    /\ coord' = [coord EXCEPT !.requestSent = TRUE]

RecvVote(p) ==
    /\ coord.alive
    /\ coord.requestSent
    /\ p \in participants
    /\ part[p].alive
    /\ ~coord.votesRecv[p]
    /\ coord' = [coord EXCEPT !.votesRecv[p] = TRUE]

MakeDecision ==
    /\ coord.alive
    /\ coord.requestSent
    /\ \A p \in participants: coord.votesRecv[p]
    /\ ~coord.decisionMade
    /\ coord' = [coord EXCEPT 
                  !.decisionMade = TRUE,
                  !.decision = IF \A p \in participants: part[p].vote = yes
                                 THEN commit ELSE abort]

Broadcast ==
    /\ coord.alive
    /\ coord.decisionMade
    /\ ~coord.broadcast
    /\ coord' = [coord EXCEPT !.broadcast = TRUE]

CoordDie ==
    /\ coord.alive
    /\ coord' = [coord EXCEPT 
                  !.alive = FALSE,
                  !.faulty = TRUE]

\*---------------------------------------------------------------------- 
\* Participant actions (base + reliable broadcast)
\*---------------------------------------------------------------------- 
SendVote(p) ==
    /\ part[p].alive
    /\ part[p].vote = no \/ part[p].vote = yes
    /\ ~part[p].voteSent
    /\ part' = [part EXCEPT ![p].voteSent = TRUE]

PreDecideFromCoord(p) ==
    /\ part[p].alive
    /\ part[p].decision = undecided
    /\ coord.broadcast
    /\ coord.decision \in {commit, abort}
    /\ part[p].fwd[p] = notsent
    /\ part' = [part EXCEPT 
                 ![p].fwd = [part[p].fwd EXCEPT ![p] = coord.decision]]

PreDecideFromFwd(p) ==
    LET src == { q \in participants : 
                  part[p].alive /\ 
                  part[p].decision = undecided /\
                  part[p].fwd[p] = notsent /\ 
                  part[q].alive /\ part[q].fwd[p] \in {commit, abort} }
    IN 
    /\ src # {}
    /\ \E q \in src: 
        part' = [part EXCEPT 
                 ![p].fwd = [part[p].fwd EXCEPT ![p] = part[q].fwd[p]]]

Forward(p) ==
    /\ part[p].alive
    /\ part[p].fwd[p] \in {commit, abort}
    /\ \E q \in participants :
         /\ part[q].alive
         /\ part[p].fwd[q] = notsent
         /\ part' = [part EXCEPT 
                      ![p].fwd = [part[p].fwd EXCEPT ![q] = part[p].fwd[p]]]

Decide(p) ==
    /\ part[p].alive
    /\ part[p].decision = undecided
    /\ \A q \in participants : part[p].fwd[q] \in {commit, abort}
    /\ part[p].fwd[p] \in {commit, abort}
    /\ part' = [part EXCEPT 
                 ![p].decision = part[p].fwd[p]]

AbortOnTimeout(p) ==
    /\ part[p].alive
    /\ part[p].decision = undecided
    /\ ~coord.alive
    /\ \A q \in participants : 
        ~(coord.broadcast /\ q \in participants)  \* no broadcast to anyone
    /\ \A dead \in participants :
        ~part[dead].faulty \/ 
        \A r \in participants :
            ~part[dead].fwd[r] \in {commit, abort}
    /\ part' = [part EXCEPT ![p].decision = abort]

PartDie(p) ==
    /\ part[p].alive
    /\ part' = [part EXCEPT 
                 ![p].alive = FALSE,
                 ![p].faulty = TRUE]

\*---------------------------------------------------------------------- 
\* Next-state relation
\*---------------------------------------------------------------------- 
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: PreDecideFromCoord(p)
    \/ \E p \in participants: PreDecideFromFwd(p)
    \/ \E p \in participants: Forward(p)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: PartDie(p)
    \/ SendRequest
    \/ \E p \in participants: RecvVote(p)
    \/ MakeDecision
    \/ Broadcast
    \/ CoordDie

\*---------------------------------------------------------------------- 
\* Specification
\*---------------------------------------------------------------------- 
SpecNB == Init /\ [][Next]_<<coord, part>>

\*---------------------------------------------------------------------- 
\* Type invariant (ensures all variables stay within their domains)
\*---------------------------------------------------------------------- 
TypeInvNB ==
    /\ coord \in CoordState
    /\ part \in [participants -> ParticipantState]
    /\ \A p \in participants :
        part[p].vote \in Values /\
        part[p].alive \in BOOLEAN /\
        part[p].decision \in ParticipantStates /\
        part[p].faulty \in BOOLEAN /\
        part[p].voteSent \in BOOLEAN /\
        part[p].fwd \in [participants -> ForwardStatus]

=============================================================================