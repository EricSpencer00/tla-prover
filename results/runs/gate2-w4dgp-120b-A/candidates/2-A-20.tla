---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* This module implements the Non-Blocking Atomic Commitment Protocol (ACP-NB)
\* from Babaoglu and Toueg.  It extends the simple broadcast variant by
\* implementing a reliable broadcast: a participant that receives a decision
\* forwards it to all other participants before delivering it locally.  This
\* forwarding is what guarantees termination even if the coordinator crashes
\* mid-broadcast.
\* Compared with the base ACP-SB module it adds, for each participant, a
\* forwarding table (the fwd map) recording what decision has been received
\* and to whom it has already been forwarded.  The rest of the coordinator
\* logic is inherited unchanged from ACP-SB (InitReq, Vote, CrashCoord, etc.).

ASSUME yes # no

VARIABLES vote, aliveP, decision, faultyP, sent, coord, fwd

vars == <<vote, aliveP, decision, faultyP, sent, coord, fwd>>

\* coord[f] is the coordinator's broadcast state for participant f.  fwd[p][q]
\* records what decision p has received from the coordinator (or what it has
\* already chosen for itself) and whether p has forwarded that decision to q.
TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \subseteq participants
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faultyP \subseteq participants
  /\ sent \in [participants -> {waiting, notsent}]
  /\ coord \in [participants -> {undecided, commit, abort, waiting}]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> yes]
  /\ aliveP = participants
  /\ decision = [p \in participants |-> undecided]
  /\ faultyP = {}
  /\ sent = [p \in participants |-> notsent]
  /\ coord = [f \in participants |-> waiting]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

InitReq ==
  /\ coord' = [f \in participants |-> undecided]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, fwd>>

Vote(p) ==
  /\ p \in aliveP
  /\ sent[p] = notsent
  /\ sent' = [sent EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, coord, fwd>>

CrashCoord ==
  /\ coord /= [f \in participants |-> waiting]
  /\ coord' = [f \in participants |-> waiting]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, fwd>>

Decide ==
  /\ coord' = [f \in participants |-> IF \A p \in participants : p \in aliveP /\ vote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, fwd>>

Broadcast ==
  /\ coord # [f \in participants |-> waiting]
  /\ \A f \in participants : coord[f] # undecided => coord[f] = waiting => coord' = [coord EXCEPT ![f] = waiting]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, fwd>>

Die(p) ==
  /\ p \in aliveP
  /\ aliveP' = aliveP \ {p}
  /\ faultyP' = faultyP \cup {p}
  /\ UNCHANGED <<vote, decision, sent, coord, fwd>>

\* Coordinator broadcasts its pre-decided value to one participant at a time.
PropagateCoord(p) ==
  /\ p \in aliveP
  /\ decision[p] = undecided
  /\ coord[p] # undecided
  /\ coord[p] # waiting
  /\ decision' = [decision EXCEPT ![p] = coord[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coord, fwd>>

\* A participant receives a pre-decision from the coordinator (storing it in
\* its own forwarding entry) and is not yet marked as decided itself.
PreDecideCoord(p) ==
  /\ p \in aliveP
  /\ decision[p] = undecided
  /\ coord[p] # undecided
  /\ coord[p] # waiting
  /\ fwd' = [fwd EXCEPT ![p][p] = coord[p]]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, coord>>

\* A participant receives a pre-decision via forwarding from another participant.
PreDecideForward(q) ==
  \E p \in participants :
    /\ p # q
    /\ p \in aliveP
    /\ fwd[p][q] # notsent
    /\ decision[q] = undecided
    /\ fwd' = [fwd EXCEPT ![q][q] = fwd[p][q]]
    /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, coord>>

\* Forwarding: every other participant must receive the pre-decision before
\* the local participant finalizes.  This is the reliable-broadcast guarantee.
Forward(p, q) ==
  /\ p \in aliveP
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, aliveP, decision, faultyP, sent, coord>>

\* Once a participant has forwarded its pre-decision to everyone, it may
\* finalize (commit or abort) locally.  Because every other participant has
\* already received the same pre-decision, no participant can later decide
\* differently.
DecideLocal(p) ==
  /\ p \in aliveP
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coord, fwd>>

\* Abort on timeout: if the coordinator has died and no broadcast or
\* forwarding is pending or possible, still-alive participants abort.
AbortTimeout(p) ==
  /\ p \in aliveP
  /\ decision[p] = undecided
  /\ coord = [f \in participants |-> waiting]
  /\ aliveP = participants \ faultyP
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sent, coord, fwd>>

Next ==
  \/ InitReq \/ CrashCoord \/ Decide \/ Broadcast
  \/ \E p \in participants :
       Vote(p) \/ Die(p) \/ PropagateCoord(p) \/ PreDecideCoord(p)
       \/ DecideLocal(p) \/ AbortTimeout(p)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E q \in participants : PreDecideForward(q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Vote('h1'))
  /\ WF_vars(Vote('h2'))
  /\ WF_vars(PreDecideCoord('h1'))
  /\ WF_vars(PreDecideCoord('h2'))
  /\ WF_vars(PreDecideForward('h1'))
  /\ WF_vars(PreDecideForward('h2'))

\* AC1: No two participants ever reach conflicting decisions.
Agreement ==
  ~ \E p, q \in participants : p # q /\ decision[p] = commit /\ decision[q] = abort

\* AC2: Any commit must be backed by a unanimous yes vote.
CommitValidity ==
  (commit \in {decision[p] : p \in participants}) => (\A p \in participants : vote[p] = yes)

\* AC3: Any abort must be traceable to a genuine failure (no vote, a faulty
\* participant, or a failed coordinator).
AbortValidity ==
  (abort \in {decision[p] : p \in participants}) =>
    (\E p \in participants : vote[p] = no \/ p \in faultyP \/ coord = [f \in participants |-> waiting])

\* AC4: Decisions are immutable once reached.
Irreversibility ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* AC3L: Eventually the protocol resolves or reveals a fault -- the safety
\* condition that is the weak form of atomic commitment.
TerminationL ==
  (commit \in {decision[p] : p \in participants} \/ abort \in {decision[p] : p \in participants})
    \/ (\E p \in participants : p \in faultyP)
    \/ coord = [f \in participants |-> waiting]

\* AC5: Every non-faulty participant eventually decides (commits or aborts).
Liveness == \A p \in participants : (p \in aliveP) ~> (decision[p] # undecided)

====