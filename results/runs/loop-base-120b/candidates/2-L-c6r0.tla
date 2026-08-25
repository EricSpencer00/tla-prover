---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants,   \* set of all participant identifiers
    yes, no,        \* vote values
    undecided,      \* participant decision before finalisation
    commit, abort,  \* final decision values
    waiting,        \* placeholder for request‑waiting state
    notsent         \* forwarding table entry meaning “no decision forwarded yet”

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,        \* TRUE iff the coordinator is alive
    coordFaulty,       \* TRUE iff the coordinator has crashed (faulty)
    coordDecision,    \* decision made by the coordinator (undecided/commit/abort)

    alive,            \* [participants -> BOOLEAN]  alive status of each participant
    faulty,           \* [participants -> BOOLEAN]  faulty flag of each participant
    voteSent,         \* [participants -> BOOLEAN]  whether a participant has already sent its vote
    vote,             \* [participants -> {yes,no}] the vote cast by each participant

    preDec,           \* [participants -> {commit,abort,undecided}]
                       \* decision that a participant has received (but not yet finalised)

    decision,         \* [participants -> {commit,abort,undecided}]
                       \* final decision of each participant

    fwd               \* [participants -> [participants -> {commit,abort,notsent}]]
                       \* forwarding table: for each sender p and receiver q
                       \* the entry is the decision that p has already forwarded to q
                       
\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << coordAlive, coordFaulty, coordDecision,
          alive, faulty, voteSent, vote,
          preDec, decision, fwd >>

AllParticipants == participants

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided

    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]

    /\ voteSent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> yes]   \* the concrete vote will be chosen by SendVote

    /\ preDec = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]

    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherit from ACP‑SB)
\* ----------------------------------------------------------------------
SendRequest == TRUE   \* placeholder – request is implicit in this model

SendVote(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ voteSent[p] = FALSE
    /\ vote[p] \in {yes, no}
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, vote, preDec, decision, fwd>>

MakeDecision ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ \A p \in participants : voteSent[p]    \* all votes have arrived
    /\ IF \E p \in participants : vote[p] = no
          THEN coordDecision' = abort
          ELSE coordDecision' = commit
    /\ UNCHANGED <<coordAlive, coordFaulty,
                   alive, faulty, voteSent, vote, preDec, decision, fwd>>

BroadcastDecision ==
    /\ coordDecision \in {commit, abort}
    /\ \E p \in participants :
          /\ alive[p] = TRUE
          /\ preDec[p] = undecided
          /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, decision, fwd>>

CoordinatorDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, alive, faulty, voteSent, vote,
                   preDec, decision, fwd>>

\* ----------------------------------------------------------------------
\* Participant actions (extended for reliable broadcast)
\* ----------------------------------------------------------------------
PreDecideFromCoord(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDec[p] = undecided
    /\ coordDecision \in {commit, abort}
    /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, decision, fwd>>

PreDecideFromForward(p, q) ==
    /\ p \in participants /\ q \in participants
    /\ alive[p] = TRUE
    /\ preDec[p] = undecided
    /\ fwd[q][p] \in {commit, abort}
    /\ preDec' = [preDec EXCEPT ![p] = fwd[q][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, decision, fwd>>

Forward(p, q) ==
    /\ p \in participants /\ q \in participants
    /\ alive[p] = TRUE
    /\ preDec[p] \in {commit, abort}
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, preDec, decision>>

Decide(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDec[p] \in {commit, abort}
    /\ \A q \in participants : fwd[p][q] # notsent   \* forwarded to everyone (including self)
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, preDec, fwd>>

AbortTimeout(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ (coordAlive = FALSE \/ coordFaulty = TRUE)
    /\ \A r \in participants : preDec[r] = undecided   \* no pre‑decision from coordinator has been received
    /\ \A r \in participants : \A s \in participants :
          ~(alive[r] = FALSE /\ fwd[r][s] # notsent)   \* no dead participant has already forwarded a decision
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   alive, faulty, voteSent, vote, preDec, fwd>>

Die(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   voteSent, vote, preDec, decision, fwd>>

\* ----------------------------------------------------------------------
\* The overall next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVote(p)
    \/ MakeDecision
    \/ BroadcastDecision
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants : \E q \in participants : PreDecideFromForward(p, q)
    \/ \E p \in participants : \E q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : Die(p)
    \/ CoordinatorDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant (required)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ preDec \in [participants -> {commit, abort, undecided}]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ fwd \in [participants -> [participants -> {commit, abort, notsent}]]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====