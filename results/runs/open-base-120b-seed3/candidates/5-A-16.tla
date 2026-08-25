---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    pVote,          \* vote of each participant (yes/no)
    pAlive,         \* whether each participant is alive
    pDecision,      \* final decision of each participant (undecided/commit/abort)
    pFaulty,        \* whether each participant has crashed
    pSentVote,      \* whether each participant has sent its vote
    cAlive,         \* coordinator alive flag
    cFaulty,        \* coordinator faulty flag
    cDecision,      \* coordinator decision (undecided/commit/abort)
    cRequests,      \* set of participants to which a vote request has been sent
    cVotes,         \* votes received by coordinator (yes/no/waiting)
    cSent           \* for each participant, whether coordinator has sent decision (commit/abort/notsent)

vars == << pVote, pAlive, pDecision, pFaulty, pSentVote,
           cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cRequests = {}
    /\ cVotes = [p \in participants |-> waiting]
    /\ cSent = [p \in participants |-> notsent]

(* ---------- Coordinator actions ---------- *)

SendReq(p) ==
    /\ cAlive
    /\ p \in participants
    /\ p \notin cRequests
    /\ cRequests' = cRequests \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cVotes, cSent >>

RecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequests
    /\ cVotes[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cSent >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequests
    /\ cVotes[p] = waiting
    /\ pAlive[p] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cRequests, cVotes, cSent >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVotes[p] # waiting
    /\ IF \A p \in participants: cVotes[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cRequests, cVotes, cSent >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ p \in participants
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cVotes >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty, pSentVote,
                    cDecision, cRequests, cVotes, cSent >>

(* ---------- Participant actions ---------- *)

SendVote(p) ==
    /\ pAlive[p]
    /\ p \in participants
    /\ p \in cRequests
    /\ pSentVote[p] = FALSE
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty,
                    cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cAlive = FALSE
    /\ pSentVote[p] = FALSE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cAlive, cFaulty, cDecision, cRequests, cVotes, cSent >>

(* ---------- Next-state relation ---------- *)

Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

Spec == Init /\ [][Next]_vars

(* ---------- Type invariant ---------- *)

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cRequests \subseteq participants
    /\ cVotes \in [participants -> {yes, no, waiting}]
    /\ cSent \in [participants -> {commit, abort, notsent}]

====