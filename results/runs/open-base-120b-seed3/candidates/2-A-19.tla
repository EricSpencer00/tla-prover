---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    coordAlive,        \* Is the coordinator alive?
    coordFaulty,       \* Has the coordinator crashed?
    coordDecision,    \* Decision made by the coordinator (undecided, commit, abort)
    broadcastSent,    \* [p \in participants -> BOOLEAN] : whether the coordinator has sent the decision to p
    vote,             \* [p \in participants -> {yes,no}] : the vote cast by each participant
    voteSent,         \* [p \in participants -> BOOLEAN] : whether p has sent its vote to the coordinator
    forwarding,       \* [p \in participants -> [q \in participants -> {notsent, commit, abort}]]
    decided,          \* [p \in participants -> {undecided, commit, abort}]
    alive,            \* Set of participants that are still alive
    faulty            \* Set of participants that have crashed

vars == <<coordAlive, coordFaulty, coordDecision, broadcastSent,
          vote, voteSent, forwarding, decided, alive, faulty>>

Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> no]          \* initial dummy value
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decided = [p \in participants |-> undecided]
    /\ alive = participants
    /\ faulty = {}

\* ---------- Coordinator actions ----------
SendRequest ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ UNCHANGED vars

SendVoteYes(p) ==
    /\ p \in alive
    /\ ~voteSent[p]
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  forwarding, decided, alive, faulty>>

SendVoteNo(p) ==
    /\ p \in alive
    /\ ~voteSent[p]
    /\ vote' = [vote EXCEPT ![p] = no]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  forwarding, decided, alive, faulty>>

DetectFault(p) ==
    /\ p \in participants
    /\ p \notin alive
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, broadcastSent,
                  vote, voteSent, forwarding, decided, alive, faulty>>

MakeDecision ==
    /\ coordAlive
    /\ \A p \in participants : voteSent[p]
    /\ \/ (\A p \in participants : vote[p] = yes) /\ coordDecision' = commit
       \/ (\E p \in participants : vote[p] = no)    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, broadcastSent,
                  vote, voteSent, forwarding, decided, alive, faulty>>

BroadcastDecision ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ broadcastSent' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                  vote, voteSent, forwarding, decided, alive, faulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, broadcastSent,
                  vote, voteSent, forwarding, decided, alive, faulty>>

\* ---------- Participant actions ----------
PreDecFromCoord(p) ==
    /\ p \in alive
    /\ broadcastSent[p]
    /\ forwarding[p][p] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, decided, alive, faulty>>

PreDecFromForward(p) ==
    /\ p \in alive
    /\ forwarding[p][p] = notsent
    /\ \E q \in participants :
          q # p /\ forwarding[q][p] # notsent
    /\ LET d == IF \E q \in participants : q # p /\ forwarding[q][p] = commit
                THEN commit ELSE abort
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, decided, alive, faulty>>

Forward(p,q) ==
    /\ p \in alive
    /\ q \in participants
    /\ q # p
    /\ forwarding[p][p] # notsent
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, decided, alive, faulty>>

Decide(p) ==
    /\ p \in alive
    /\ decided[p] = undecided
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ decided' = [decided EXCEPT ![p] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, forwarding, alive, faulty>>

AbortOnTimeout(p) ==
    /\ p \in alive
    /\ decided[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : ~broadcastSent[q]
    /\ \A d \in participants :
          d \in faulty => \A r \in participants :
                         r \in alive => forwarding[d][r] = notsent
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, forwarding, alive, faulty>>

ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, broadcastSent,
                  vote, voteSent, forwarding, decided>>

\* ---------- Next state ----------
Next ==
    \/ \E p \in participants : SendVoteYes(p)
    \/ \E p \in participants : SendVoteNo(p)
    \/ \E p \in participants : PreDecFromCoord(p)
    \/ \E p \in participants : PreDecFromForward(p)
    \/ \E p,q \in participants : Forward(p,q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ SendRequest
    \/ MakeDecision
    \/ BroadcastDecision
    \/ \E p \in participants : DetectFault(p)
    \/ CoordDie

SpecNB == Init /\ [][Next]_vars

\* ---------- Type invariants ----------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ decided \in [participants -> {undecided, commit, abort}]
    /\ alive \subseteq participants
    /\ faulty \subseteq participants
    /\ Disjoint[alive, faulty]

====