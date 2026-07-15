---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no, undecided, \* vote values
    commit, abort, \* decision values
    waiting, \* coordinator request state
    notsent      \* forwarding status meaning no decision yet

\* ---------- State variables ----------
VARIABLES
    coordAlive,        \* coordinator alive flag
    coordFaulty,       \* coordinator faulty flag
    coordReq,          \* current request (waiting or decided)
    coordDecision,    \* decision made by coordinator (commit or abort)
    votes,            \* [p \in participants -> {yes,no,undecided}]
    decisions,         \* [p \in participants -> {undecided,commit,abort}]
    forwarding,        \* [p \in participants -> [q \in participants -> {notsent,commit,abort}]]
    forwarded,        \* [p \in participants -> SUBSET participants]  \* set of participants p has already forwarded to
    participantAlive, \* set of participants currently alive
    participantFaulty \* set of participants currently faulty

\* ---------- Derived definitions ----------
PreDecide(p) == 
    /\ p \in participantAlive
    /\ decisions[p] = undecided
    /\ \/ /\ coordAlive
          /\ coordDecision \in {commit,abort}
          /\ forwarding[p][p] = notsent
          /\ forwarding[p][p]' = coordDecision
       \/ \E q \in participants :
            /\ q \in participantAlive
            /\ forwarding[q][p] \in {commit,abort}
            /\ forwarding[p][p]' = forwarding[q][p]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, decisions, forwarding, forwarded,
                    participantAlive, participantFaulty>>

Forward(p,q) ==
    /\ p \in participantAlive
    /\ q \in participantAlive
    /\ p # q
    /\ forwarding[p][p] \in {commit,abort}      \* p has a pre‑decision
    /\ q \notin forwarded[p]                    \* not yet forwarded to q
    /\ forwarding[p][q]' = forwarding[p][p]     \* send the same decision
    /\ forwarded[p]' = forwarded[p] \cup {q}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, decisions, forwarding, participantAlive,
                    participantFaulty>>

Decide(p) ==
    /\ p \in participantAlive
    /\ forwarding[p][p] \in {commit,abort}
    /\ \A q \in participants : q \in forwarded[p] \/ q = p   \* has forwarded to all others
    /\ decisions[p]' = forwarding[p][p]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, forwarding, forwarded,
                    participantAlive, participantFaulty>>

AbortTimeout(p) ==
    /\ p \in participantAlive
    /\ decisions[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participantAlive :
          forwarding[coordAlive][q] = notsent
    /\ \A q \in participants :
          \A r \in participants :
            ~(q \in participantFaulty /\ forwarding[q][r] \in {commit,abort})
    /\ decisions[p]' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, forwarding, forwarded,
                    participantAlive, participantFaulty>>

SendVote(p) ==
    /\ p \in participantAlive
    /\ coordReq = waiting
    /\ votes[p]' = IF p \in participantAlive THEN yes ELSE no
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    decisions, forwarding, forwarded,
                    participantAlive, participantFaulty>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ \A p \in participants : votes[p] # undecided
    /\ coordDecision' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
    /\ coordReq' = coordDecision'
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, decisions,
                    forwarding, forwarded, participantAlive, participantFaulty>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordReq = coordDecision
    /\ \E p \in participants :
          /\ p \in participantAlive
          /\ forwarding[p][p] = notsent
          /\ forwarding[p][p]' = coordDecision
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, decisions, forwarded,
                    participantAlive, participantFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordReq, coordDecision, votes, decisions,
                    forwarding, forwarded, participantAlive, participantFaulty>>

PartDie(p) ==
    /\ p \in participantAlive
    /\ participantAlive' = participantAlive \ {p}
    /\ participantFaulty' = participantFaulty \cup {p}
    /\ decisions' = [decisions EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, forwarding, forwarded>>

\* ---------- Initialization ----------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordReq = waiting
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> undecided]
    /\ decisions = [p \in participants |-> undecided]
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ forwarded = [p \in participants |-> {}]
    /\ participantAlive = participants
    /\ participantFaulty = {}

\* ---------- Next-state relation ----------
Next ==
    \/ SendVote(p)               \* any participant may send its vote
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ PreDecide(p)              \* receive decision directly from coordinator
    \/ Forward(p,q)              \* forward to another participant
    \/ Decide(p)                 \* finalize after forwarding to all
    \/ AbortTimeout(p)
    \/ PartDie(p)                \* a participant crashes
    \/ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordDecision,
                    votes, decisions, forwarding, forwarded,
                    participantAlive, participantFaulty>>

SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordReq, coordDecision,
                         votes, decisions, forwarding, forwarded,
                         participantAlive, participantFaulty>>

\* ---------- Type invariant ----------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordReq \in {waiting, commit, abort}
    /\ coordDecision \in {undecided, commit, abort}
    /\ votes \in [participants -> {yes,no,undecided}]
    /\ decisions \in [participants -> {undecided, commit, abort}]
    /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ forwarded \in [participants -> SUBSET participants]
    /\ participantAlive \subseteq participants
    /\ participantFaulty \subseteq participants
    /\ participantAlive \cap participantFaulty = {}

\* ---------- Safety properties ----------
\* AC1: Agreement – no two participants decide differently
Agreement ==
    \A p,q \in participants :
        /\ p \in participantAlive => decisions[p] # undecided
        /\ q \in participantAlive => decisions[q] # undecided
        => decisions[p] = decisions[q]

\* AC2: Commit validity – if any participant commits, all voted yes
CommitValidity ==
    \A p \in participants :
        decisions[p] = commit => \A q \in participants : votes[q] = yes

\* AC3: Abort validity – if any participant aborts, then some vote was no or some fault occurred
AbortValidity ==
    \A p \in participants :
        decisions[p] = abort =>
            \/ \E q \in participants : votes[q] = no
            \/ \E q \in participants : q \in participantFaulty
            \/ coordFaulty

\* AC4: Irrevocability – once decided, the decision never changes
Irrevocability ==
    \A p \in participants :
        \A d \in {commit, abort} :
            (decisions[p] = d) => [] (decisions[p] = d)

\* ---------- Liveness properties ----------
\* AC5 (non‑blocking termination) – every non‑faulty participant eventually decides
Termination ==
    \A p \in participants :
        p \in participantAlive => <> (decisions[p] # undecided)

\* (AC3 liveness is not required as an invariant but may be added if desired)
\* AC3_Liveness == <> ( \E p \in participants : decisions[p] # undecided
\*                     \/ \E p \in participants : p \in participantFaulty
\*                     \/ coordFaulty )

\* ---------- Theorems (optional, expose properties) ----------
THEOREM SpecNB => []Agreement
THEOREM SpecNB => []CommitValidity
THEOREM SpecNB => []AbortValidity
THEOREM SpecNB => []Irrevocability
THEOREM SpecNB => []Termination

====