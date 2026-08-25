---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants,   \* set of participant identifiers
    yes, no, 
    undecided, commit, abort, 
    waiting, notsent

VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* subset of participants that are alive
    pDecision,      \* [participants -> {undecided,commit,abort}]
    pSentVote,      \* [participants -> BOOLEAN]
    cAlive,         \* BOOLEAN (coordinator is alive)
    cDecision,      \* {undecided,commit,abort}
    cRequested,     \* subset of participants to which a vote request has been sent
    cReceived,      \* [participants -> {yes,no,waiting}]
    cBroadcast      \* [participants -> {commit,abort,notsent}]

\*=====================================================================
\* Helper definitions
\*=====================================================================

\* The set of all state variables
vars == << pVote, pAlive, pDecision, pSentVote,
           cAlive, cDecision, cRequested, cReceived, cBroadcast >>

\*=====================================================================
\* Initial state
\*=====================================================================

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = participants
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cRequested = {}
    /\ cReceived = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]

\*=====================================================================
\* Coordinator actions
\*=====================================================================

SendVoteRequest(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \notin cRequested
    /\ cRequested' = cRequested \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cReceived, cBroadcast >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequested
    /\ cReceived[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ cReceived' = [cReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cBroadcast >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequested
    /\ cReceived[p] = waiting
    /\ p \notin pAlive          \* participant has crashed
    /\ pSentVote[p] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cRequested, cReceived, cBroadcast >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cReceived[p] # waiting
    /\ IF \A p \in participants : cReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cRequested, cReceived, cBroadcast >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ p \in participants
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cReceived >>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSentVote,
                    cDecision, cRequested, cReceived, cBroadcast >>

\*=====================================================================
\* Participant actions
\*=====================================================================

SendVote(p) ==
    /\ p \in pAlive
    /\ pSentVote[p] = FALSE
    /\ p \in cRequested            \* participant has received request
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision,
                    cAlive, cDecision, cRequested, cReceived, cBroadcast >>

AbortOnVote(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceived, cBroadcast >>

AbortOnTimeout(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ ~cAlive                     \* coordinator has crashed
    /\ p \notin cRequested         \* no request was ever sent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceived, cBroadcast >>

DecideOnBroadcast(p) ==
    /\ p \in pAlive
    /\ pDecision[p] = undecided
    /\ cBroadcast[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED << pVote, pAlive, pSentVote,
                    cAlive, cDecision, cRequested, cReceived, cBroadcast >>

ParticipantDie(p) ==
    /\ p \in pAlive
    /\ pAlive' = pAlive \ {p}
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cAlive, cDecision, cRequested, cReceived, cBroadcast >>

\*=====================================================================
\* Next-state relation
\*=====================================================================

SendVoteRequestAction == \E p \in participants : SendVoteRequest(p)
ReceiveVoteAction      == \E p \in participants : ReceiveVote(p)
DetectFaultAction      == \E p \in participants : DetectFault(p)
BroadcastAction        == \E p \in participants : Broadcast(p)
SendVoteAction         == \E p \in participants : SendVote(p)
AbortOnVoteAction      == \E p \in participants : AbortOnVote(p)
AbortOnTimeoutAction   == \E p \in participants : AbortOnTimeout(p)
DecideOnBroadcastAction== \E p \in participants : DecideOnBroadcast(p)
ParticipantDieAction   == \E p \in participants : ParticipantDie(p)

Next ==
    \/ SendVoteRequestAction
    \/ ReceiveVoteAction
    \/ DetectFaultAction
    \/ MakeDecision
    \/ BroadcastAction
    \/ CoordinatorDie
    \/ SendVoteAction
    \/ AbortOnVoteAction
    \/ AbortOnTimeoutAction
    \/ DecideOnBroadcastAction
    \/ ParticipantDieAction

\*=====================================================================
\* Fairness assumptions (weak fairness on progress actions, not on dies)
\*=====================================================================

CoordinatorProgress ==
    \/ SendVoteRequestAction
    \/ ReceiveVoteAction
    \/ DetectFaultAction
    \/ MakeDecision
    \/ BroadcastAction

ParticipantProgress ==
    \/ SendVoteAction
    \/ AbortOnVoteAction
    \/ AbortOnTimeoutAction
    \/ DecideOnBroadcastAction

\*=====================================================================
\* Specification
\*=====================================================================

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(CoordinatorProgress) /\ WF_vars(ParticipantProgress)

\*=====================================================================
\* Type invariant (required)
\*=====================================================================

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \subseteq participants
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cRequested \subseteq participants
    /\ cReceived \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {commit, abort, notsent}]

====