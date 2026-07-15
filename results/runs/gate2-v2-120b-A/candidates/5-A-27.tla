---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    participants,   \* set of participants
    yes, no,        \* vote values
    undecided, commit, abort, \* participant decisions
    waiting, notsent            \* special markers for coordinator state

\* ----------------------------------------------------------------------
\* Types (for readability and the TypeInv invariant)
\* ----------------------------------------------------------------------
Vote      == {yes, no}
Decision  == {undecided, commit, abort}
VoteVal   == Vote \cup {waiting}
DecSent   == {commit, abort, notsent}
Alive     == BOOLEAN

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    CAlive,          \* coordinator alive?
    CFaulty,         \* coordinator faulty?
    CDecision,       \* coordinator decision (undecided/commit/abort)
    CReqSent,        \* set of participants to which vote request has been sent
    CVoted,          \* map participants -> vote value or waiting
    CDecSent,        \* map participants -> decision sent or notsent

    PAlive,          \* map participants -> BOOLEAN (alive?)
    PFaulty,         \* map participants -> BOOLEAN (faulty?)
    PVote,           \* map participants -> Vote (chosen at start)
    PSent,           \* map participants -> BOOLEAN (has sent vote)
    PDecision        \* map participants -> Decision

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PIds == participants

CReqAll   == CReqSent = participants
CVotedAll == \A p \in participants: CVoted[p] # waiting
AllDecSent== \A p \in participants: CDecSent[p] # notsent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ CAlive   = TRUE
    /\ CFaulty  = FALSE
    /\ CDecision= undecided
    /\ CReqSent = {}
    /\ CVoted   = [p \in participants |-> waiting]
    /\ CDecSent = [p \in participants |-> notsent]

    /\ PAlive   = [p \in participants |-> TRUE]
    /\ PFaulty  = [p \in participants |-> FALSE]
    /\ PVote    = [p \in participants |-> IF RandomChoice({yes, no}) = 0 THEN yes ELSE no]  \* nondet vote
    /\ PSent    = [p \in participants |-> FALSE]
    /\ PDecision= [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ CAlive
    /\ ~ (p \in CReqSent)
    /\ CReqSent' = CReqSent \cup {p}
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

CoordRecvVote(p) ==
    /\ CAlive
    /\ CDecision = undecided
    /\ CReqAll
    /\ waiting = CVoted[p]
    /\ PSent[p] = TRUE
    /\ CVoted' = [CVoted EXCEPT ![p] = PVote[p]]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CDecSent,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

CoordDetectFault(p) ==
    /\ CAlive
    /\ CDecision = undecided
    /\ CReqAll
    /\ waiting = CVoted[p]
    /\ ~PAlive[p]            \* participant died before voting
    /\ CDecision' = abort
    /\ CFaulty' = TRUE       \* coordinator becomes faulty due to detection
    /\ UNCHANGED << CAlive, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

CoordMakeDecision ==
    /\ CAlive
    /\ CDecision = undecided
    /\ CReqAll
    /\ CVotedAll
    /\ CDecision' = IF \A p \in participants: CVoted[p] = yes
                     THEN commit
                     ELSE abort
    /\ UNCHANGED << CAlive, CFaulty, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

CoordBroadcast(p) ==
    /\ CAlive
    /\ CDecision # undecided
    /\ CDecSent[p] = notsent
    /\ CDecSent' = [CDecSent EXCEPT ![p] = CDecision]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

CoordDie ==
    /\ CAlive
    /\ CAlive' = FALSE
    /\ CFaulty' = TRUE
    /\ UNCHANGED << CDecision, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent, PDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ PAlive[p]
    /\ p \in CReqSent          \* vote request received
    /\ ~ PSent[p]
    /\ PSent' = [PSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PDecision >>

PartAbortOnNo(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ PSent[p] = TRUE
    /\ PVote[p] = no
    /\ PDecision' = [PDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent >>

PartAbortOnTimeout(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ ~ CAlive                \* coordinator died before sending request
    /\ PDecision' = [PDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent >>

PartDecideFromBroadcast(p) ==
    /\ PAlive[p]
    /\ PDecision[p] = undecided
    /\ CDecSent[p] # notsent
    /\ CDecision \in {commit, abort}
    /\ PDecision' = [PDecision EXCEPT ![p] = CDecision]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                    PAlive, PFaulty, PVote, PSent >>

PartDie(p) ==
    /\ PAlive[p]
    /\ PAlive' = [PAlive EXCEPT ![p] = FALSE]
    /\ PFaulty' = [PFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                    PVote, PSent, PDecision >>

\* ----------------------------------------------------------------------
\* Stuttering (to avoid deadlock when no enabled action)
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED << CAlive, CFaulty, CDecision, CReqSent, CVoted, CDecSent,
                PAlive, PFaulty, PVote, PSent, PDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<CAlive, CFaulty, CDecision, CReqSent, CVoted,
                         CDecSent, PAlive, PFaulty, PVote, PSent, PDecision>>

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC, not part of safety spec)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ CAlive \in BOOLEAN
    /\ CFaulty \in BOOLEAN
    /\ CDecision \in {undecided, commit, abort}
    /\ CReqSent \subseteq participants
    /\ CVoted \in [participants -> VoteVal]
    /\ CDecSent \in [participants -> DecSent]

    /\ PAlive \in [participants -> BOOLEAN]
    /\ PFaulty \in [participants -> BOOLEAN]
    /\ PVote \in [participants -> Vote]
    /\ PSent \in [participants -> BOOLEAN]
    /\ PDecision \in [participants -> Decision]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* AC1: No two participants decide differently
Agree ==
    \A p,q \in participants :
        (PDecision[p] = commit => PDecision[q] # abort) /\
        (PDecision[p] = abort  => PDecision[q] # commit)

\* AC2: If any participant commits, all participants voted yes
CommitValidity ==
    \A p \in participants :
        (PDecision[p] = commit) => \A q \in participants : PVote[q] = yes

\* AC3: If any participant aborts, then either some vote was no or some fault exists
AbortValidity ==
    \A p \in participants :
        (PDecision[p] = abort) =>
            ( \E q \in participants : PVote[q] = no )
            \/ ( \E q \in participants : PFaulty[q] )
            \/ CFaulty

\* AC4: Irrevocability (once decided, never changes)
Irrevocability ==
    \A p \in participants :
        (PDecision[p] = commit => PDecision[p]' = commit) /\
        (PDecision[p] = abort  => PDecision[p]' = abort)

\* The module exports TypeInv as the required invariant
\* (additional safety invariants can be checked separately)
=============================================================================