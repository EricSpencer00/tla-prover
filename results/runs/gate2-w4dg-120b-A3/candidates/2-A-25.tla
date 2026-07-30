---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, pvote, alive, fstate, decision, fault, sent, act,
         coordState, coordVotes, coordDecision, coordAlive, coordFault, fwd

vars == <<pstate, pvote, alive, fstate, decision, fault, sent, act,
          coordState, coordVotes, coordDecision, coordAlive, coordFault, fwd>>

TypeOKNB ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ pvote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ fstate \in [participants -> {waiting, notsent}]
  /\ decision \in {yes, no}
  /\ fault \in {yes, no}
  /\ sent \in [participants -> {yes, no}]
  /\ act \in {commit, abort, waiting}
  /\ coordState \in {waiting, notsent}
  /\ coordVotes \subseteq participants
  /\ coordDecision \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFault \in {yes, no}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* The forwarding table is read twice, so TypeOKNB must cover it twice: once as
\* a mapping from participants (outer lookup) to an inner mapping, and again as
\* that inner mapping itself.
\*   fwd[i][j] = the forwarding status participant i sent to participant j.
\* The single decision a non-faulty participant may store is its own entry:
\*   fwd[i][i] = what i received, either from the coordinator or from a peer.
TypeOK ==
  /\ TypeOKNB
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Initial ==
  /\ pstate = [i \in participants |-> undecided]
  /\ pvote = [i \in participants |-> yes]
  /\ alive = [i \in participants |-> TRUE]
  /\ fstate = [i \in participants |-> waiting]
  /\ decision = yes
  /\ fault = no
  /\ sent = [i \in participants |-> yes]
  /\ act = waiting
  /\ coordState = waiting
  /\ coordVotes = {}
  /\ coordDecision = yes
  /\ coordAlive = TRUE
  /\ coordFault = no
  /\ fwd = [i \in participants |-> [j \in participants |-> notsent]]

\* The coordinator verbatim from the simple broadcast spec:
Request(i) ==
  /\ coordAlive
  /\ coordState = waiting
  /\ coordState' = notsent
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordVotes, coordDecision, coordFault, fwd>>

\* The coordinator verbatim from the simple broadcast spec:
Vote(j) ==
  /\ coordAlive
  /\ coordState = notsent
  /\ pstate[j] = undecided
  /\ act = waiting
  /\ fstate[j] = waiting
  /\ sent[j] = no
  /\ coordVotes' = coordVotes \cup {j}
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordDecision, coordAlive, coordFault, fwd>>

\* The coordinator verbatim from the simple broadcast spec:
Detect ==
  /\ coordAlive
  /\ coordState = notsent
  /\ sent[k] = no
  /\ decision' = no
  /\ coordDecision' = no
  /\ UNCHANGED <<pstate, pvote, alive, fstate, fault, sent, act,
                coordState, coordVotes, coordAlive, coordFault, fwd>>

\* The coordinator verbatim from the simple broadcast spec:
MakeDecision ==
  /\ coordAlive
  /\ coordState = notsent
  /\ decision = yes
  /\ coordVotes = participants
  /\ pstate[j] = undecided
  /\ pvote[j] = yes
  /\ coordDecision' = yes
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordAlive, coordFault, fwd>>

\* The coordinator verbatim from the simple broadcast spec:
Broadcast(i) ==
  /\ coordAlive
  /\ pstate[i] = undecided
  /\ coordDecision = yes
  /\ pstate' = [pstate EXCEPT ![i] = commit]
  /\ sent' = [sent EXCEPT ![i] = yes]
  /\ UNCHANGED <<pvote, alive, fstate, decision, fault, act, coordState,
                coordVotes, coordDecision, coordAlive, coordFault, fwd>>

\* The coordinator verbatim from the simple broadcast spec:
DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFault' = yes
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, fwd>>

SendVote(i) ==
  /\ alive[i]
  /\ pvote[i] = yes
  /\ fstate[i] = waiting
  /\ act = waiting
  /\ coordState = notsent
  /\ act' = commit
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                coordState, coordVotes, coordDecision, coordAlive, coordFault,
                fwd>>

AbortVote(i) ==
  /\ alive[i]
  /\ fstate[i] = waiting
  /\ pvote[i] = no
  /\ sent' = [sent EXCEPT ![i] = no]
  /\ decision' = no
  /\ act' = abort
  /\ UNCHANGED <<pstate, pvote, alive, fstate, fault, coordState,
                coordVotes, coordDecision, coordAlive, coordFault, fwd>>

\* Pre-decision from the coordinator's broadcast.
PreDecideCoord(i) ==
  /\ alive[i]
  /\ pstate[i] = undecided
  /\ coordState = notsent
  /\ fwd[i][i] = notsent
  /\ fwd' = [fwd EXCEPT ![i][i] = IF coordDecision = yes THEN commit ELSE abort]
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, coordAlive,
                coordFault>>

\* Pre-decision from another participant's forwarding.
PreDecidePeer(j, i) ==
  /\ alive[j]
  /\ pstate[j] = undecided
  /\ fwd[j][j] = notsent
  /\ fwd[i][j] # notsent
  /\ fwd' = [fwd EXCEPT ![j][j] = fwd[i][j]]
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, coordAlive,
                coordFault>>

\* Reliable broadcast: forward the pre-decision to another participant.
Forward(i, j) ==
  /\ alive[i]
  /\ fwd[i][i] # notsent
  /\ fwd[i][j] = notsent
  /\ fwd' = [fwd EXCEPT ![i][j] = fwd[i][i]]
  /\ UNCHANGED <<pstate, pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, coordAlive,
                coordFault>>

\* Only after forwarding to everybody may a participant finalize (non-blocking).
Decide(i) ==
  /\ alive[i]
  /\ pstate[i] = undecided
  /\ \A j \in participants : fwd[i][j] # notsent
  /\ pstate' = [pstate EXCEPT ![i] = fwd[i][i]]
  /\ UNCHANGED <<pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, coordAlive,
                coordFault, fwd>>

\* Abort if the coordinator died and no one can bring a decision.
AbortTimeout(i) ==
  /\ alive[i]
  /\ pstate[i] = undecided
  /\ ~coordAlive
  /\ \A p \in participants : fwd[p][i] = notsent
  /\ \A p \in participants : coordState = waiting \/ fwd[p][i] # notsent
  /\ pstate' = [pstate EXCEPT ![i] = abort]
  /\ UNCHANGED <<pvote, alive, fstate, decision, fault, sent,
                act, coordState, coordVotes, coordDecision, coordAlive,
                coordFault, fwd>>

Die(i) ==
  /\ alive[i]
  /\ alive' = [alive EXCEPT ![i] = FALSE]
  /\ fstate' = [fstate EXCEPT ![i] = notsent]
  /\ UNCHANGED <<pstate, pvote, decision, fault, sent, act,
                coordState, coordVotes, coordDecision, coordAlive, coordFault,
                fwd>>

Next ==
  \/ \E i \in participants : Request(i)
  \/ \E j \in participants : Vote(j)
  \/ Detect
  \/ MakeDecision
  \/ \E i \in participants : Broadcast(i)
  \/ DieCoordinator
  \/ \E i \in participants : SendVote(i)
  \/ \E i \in participants : AbortVote(i)
  \/ \E i \in participants : PreDecideCoord(i)
  \/ \E j \in participants, i \in participants : PreDecidePeer(j, i)
  \/ \E i \in participants, j \in participants : Forward(i, j)
  \/ \E i \in participants : Decide(i)
  \/ \E i \in participants : AbortTimeout(i)
  \/ \E i \in participants : Die(i)

SpecNB ==
  /\ Init == Initial
  /\ Next == Next
  /\ WF_vars(\E i \in participants : SendVote(i))
  /\ WF_vars(\E i \in participants : AbortVote(i))
  /\ WF_vars(\E i \in participants : PreDecideCoord(i))
  /\ WF_vars(\E j \in participants, i \in participants : PreDecidePeer(j, i))
  /\ WF_vars(\E i \in participants, j \in participants : Forward(i, j))
  /\ WF_vars(\E i \in participants : Decide(i))
  /\ WF_vars(\E i \in participants : AbortTimeout(i))

\* Safety: agreement, commit validity, abort validity, irrevocability.
TypeInvNB ==
  /\ TypeOK
  /\ \A i \in participants : pstate[i] \in {undecided, commit, abort}
  /\ \A i \in participants : pvote[i] \in {yes, no}
  /\ \A i \in participants : alive[i] \in BOOLEAN
  /\ \A i \in participants : fstate[i] \in {waiting, notsent}
  /\ decision \in {yes, no}
  /\ fault \in {yes, no}
  /\ sent \in [participants -> {yes, no}]
  /\ act \in {commit, abort, waiting}
  /\ coordState \in {waiting, notsent}
  /\ coordVotes \subseteq participants
  /\ coordDecision \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFault \in {yes, no}

\* Liveness: all decided or someone faulty; every non-faulty participant decides.
DecideAny == \E i \in participants : pstate[i] # undecided
\* Every non-faulty participant must decide, and can only be blocked by a
\* participant who itself has not yet decided, so strong fairness on it is
\* sufficient (weak fairness is not, hence the choice of strong here).
DecideAllStrong ==
  \A i \in participants : (alive[i] /\ pstate[i] = undecided) ~>
                      <>(pstate[i] # undecided)

Properties ==
  /\ (DecideAny \/ coordFault = yes \/ \E i \in participants : fault = yes)
  /\ DecideAllStrong

====