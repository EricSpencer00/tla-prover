---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Vote collection: participants send yes/no, coordinator decides commit iff all voted yes.
\* Simple broadcast: the coordinator sends its decision to participants one at a time; a crash
\* mid-broadcast can strand a participant (the blocking case the spec tracks but does not forbid).
TypeOK ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \subseteq participants
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \subseteq participants
  /\ pSent \subseteq participants
  /\ coordRequests \subseteq participants
  /\ coordRecv \in [participants -> {waiting} \cup {yes, no}]
  /\ coordSent \in [participants -> {notsent} \cup {commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \subseteq participants
  /\ coordFaulty \subseteq participants

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = participants
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = {}
  /\ pSent = {}
  /\ coordRequests = {}
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = participants
  /\ coordFaulty = {}

CoordSendRequest(p) ==
  /\ coordAlive = participants
  /\ p \in coordAlive
  /\ p \notin coordRequests
  /\ coordRequests' = coordRequests \cup {p}
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
  /\ coordAlive = participants
  /\ coordDecision = undecided
  /\ coordRequests = participants
  /\ coordRecv[p] = waiting
  /\ p \in pSent
  /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordSent, coordDecision, coordAlive, coordFaulty>>

CoordDetectParticipantFault(p) ==
  /\ coordAlive = participants
  /\ coordDecision = undecided
  /\ coordRequests = participants
  /\ coordRecv[p] = waiting
  /\ p \notin pAlive
  /\ coordDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordAlive, coordFaulty>>

CoordDecide ==
  /\ coordAlive = participants
  /\ coordDecision = undecided
  /\ coordRequests = participants
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = IF (\A p \in participants : coordRecv[p] = yes) THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
  /\ coordAlive = participants
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive = participants
  /\ coordAlive' = {}
  /\ coordFaulty' = {coordFaulty \cup participants}
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision>>

PsendVote(p) ==
  /\ p \in pAlive
  /\ p \in coordRequests
  /\ p \notin pSent
  /\ pSent' = pSent \cup {p}
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PabortOnVote(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ p \in pSent
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PabortNoVoteRequest(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ coordAlive = {}
  /\ p \notin coordRequests
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

PdecideOnBroadcast(p) ==
  /\ p \in pAlive
  /\ pDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Pdie(p) ==
  /\ p \in pAlive
  /\ pAlive' = pAlive \ {p}
  /\ pFaulty' = pFaulty \cup {p}
  /\ UNCHANGED <<pVote, pDecision, pSent, coordRequests, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : CoordSendRequest(p) \/ CoordReceiveVote(p) \/ CoordDetectParticipantFault(p) \/ CoordBroadcast(p) \/ PsendVote(p) \/ PabortOnVote(p) \/ PabortNoVoteRequest(p) \/ PdecideOnBroadcast(p) \/ Pdie(p)
  \/ CoordDecide
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants :
       /\ TRUE
       /\ SF_vars(CoordBroadcast(p))
       /\ SF_vars(PdecideOnBroadcast(p))
  /\ \A p \in participants : WF_vars(PsendVote(p))
  /\ \A p \in participants : WF_vars(PabortOnVote(p))
  /\ WF_vars(CoordDecide)

\* Safety: no two participants ever hold conflicting final decisions.
AgreementConsistent == \A p, q \in participants : (pDecision[p] = commit) => (pDecision[q] # abort)

CommitValid == (\E p \in participants : pDecision[p] = commit) => (\A p \in participants : pVote[p] = yes)

AbortValid ==
  (\E p \in participants : pDecision[p] = abort) =>
    \/ (\E p \in participants : pVote[p] = no)
    \/ (\E p \in participants : p \in pFaulty)
    \/ (coordFaulty # {})

Irreversible == (\A p \in participants : pDecision[p] = commit) ~> (\A p \in participants : pDecision[p] = commit)

\* Liveness: either everyone decides, or the failure of someone is what blocks it.
DecideOrFail == <>(\E p \in participants : pDecision[p] # undecided) \/ (coordFaulty # {}) \/ (pFaulty # {})

TypeInv == TypeOK

====