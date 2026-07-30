---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

\* Non-Blocking Atomic Commitment Protocol (ACP-NB): a reliable-broadcast
\* extension of ACP-SB. Each participant forwards the pre-decision it
\* receives to every other participant before finalizing locally, so a
\* participant can still learn the decision after the coordinator dies.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd

vars == <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd>>

\* fwd[i][j] is participant i's forwarding record for participant j: what
\* pre-decision i has received (stored at its own index) and which
\* participants it has already forwarded that pre-decision to.
Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = [p \in participants |-> FALSE]
  /\ request = no
  /\ vote = no
  /\ broadcast = no
  /\ decisionState = no
  /\ fwd = [i \in participants |-> [j \in participants |-> notsent]]

\* Coordinator sends a request into its inbox.
SendRequest ==
  /\ \E q \in participants : ~voteSent[q]
  /\ request = no
  /\ request' = yes
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, vote, broadcast, decisionState, fwd>>

\* A participant casts its vote for the current request.
SendVote ==
  /\ request = yes
  /\ \E q \in participants :
       /\ alive[q]
       /\ pstate[q] = undecided
       /\ \A j \in participants : j # q => voteSent[j]
       /\ pstate' = [pstate EXCEPT ![q] = vote]
       /\ voteSent' = [voteSent EXCEPT ![q] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, request, vote, broadcast, decisionState, fwd>>

\* Someone voted no: commit is impossible from now on.
AbortOnVote ==
  /\ request = yes
  /\ vote = no
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd>>

\* Timeout: the coordinator died before voting started, so abort.
AbortOnTimeout ==
  /\ request = yes
  /\ vote = no
  /\ \A q \in participants : ~alive[q]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd>>

\* Coordinator detects a fault and aborts.
Detect ==
  /\ request = yes
  /\ vote = no
  /\ broadcast' = yes
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, decisionState, fwd>>

\* Coordinator decides commit or abort (only if not abstaining).
Decide ==
  /\ request = yes
  /\ vote = yes
  /\ broadcast' = yes
  /\ decisionState' = vote
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, fwd>>

\* Coordinator broadcasts its decision to a single participant.
Broadcast ==
  /\ broadcast = yes
  /\ \E q \in participants : ~voteSent[q]
  /\ fwd[decisionState][q] = notsent
  /\ fwd' = [fwd EXCEPT ![decisionState][q] = decisionState]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState>>

\* A participant receives the coordinator's pre-decision.
PreDecideFromCoordinator ==
  /\ \E q \in participants :
       /\ alive[q]
       /\ fwd[q][q] = notsent
       /\ broadcast = yes
       /\ fwd[decisionState][q] # notsent
       /\ fwd' = [fwd EXCEPT ![q][q] = fwd[decisionState][q]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFromFwd ==
  /\ \E q \in participants :
       /\ alive[q]
       /\ fwd[q][q] = notsent
       /\ \E i \in participants :
            /\ i # q
            /\ fwd[i][q] # notsent
            /\ fwd' = [fwd EXCEPT ![q][q] = fwd[i][q]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState>>

\* Forward the pre-decision to another participant (reliable broadcast).
Forward ==
  /\ \E i, j \in participants :
       /\ alive[i]
       /\ fwd[i][i] # notsent
       /\ i # j
       /\ fwd[i][j] = notsent
       /\ fwd' = [fwd EXCEPT ![i][j] = fwd[i][i]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, request, vote, broadcast, decisionState>>

\* Finalize locally once this participant has forwarded to everyone else.
Decide ==
  /\ \E q \in participants :
       /\ alive[q]
       /\ pstate[q] = undecided
       /\ \A j \in participants : j # q => fwd[q][j] # notsent
       /\ pstate' = [pstate EXCEPT ![q] = fwd[q][q]]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd>>

\* An alive participant aborts when it can no longer learn anything.
AbortOnTimeout ==
  /\ \E q \in participants :
       /\ alive[q]
       /\ pstate[q] = undecided
       /\ request = no
       /\ \A r \in participants : alive[r] => fwd[r][q] = notsent
       /\ pstate' = [pstate EXCEPT ![q] = abort]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, request, vote, broadcast, decisionState, fwd>>

\* A participant dies (becomes faulty) silently.
Die ==
  /\ \E q \in participants :
       /\ alive[q]
       /\ alive' = [alive EXCEPT ![q] = FALSE]
       /\ faulty' = faulty \cup {q}
  /\ UNCHANGED <<pstate, decision, voteSent, request, vote, broadcast, decisionState, fwd>>

Next ==
  \/ SendRequest
  \/ SendVote
  \/ AbortOnVote
  \/ AbortOnTimeout
  \/ Detect
  \/ Decide
  \/ Broadcast
  \/ PreDecideFromCoordinator
  \/ PreDecideFromFwd
  \/ Forward
  \/ Decide
  \/ AbortOnTimeout
  \/ Die

Fairness ==
  /\ WF_vars(SendVote)
  /\ WF_vars(Decide)
  /\ WF_vars(Forward)
  /\ SF_vars(PreDecideFromCoordinator)
  /\ SF_vars(PreDecideFromFwd)

SpecNB == Init /\ [][Next]_vars /\ Fairness

\* No two participants can reach different decisions.
TypeInvNB ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \in [participants -> BOOLEAN]
  /\ request \in {no, yes}
  /\ vote \in {no, yes, waiting}
  /\ broadcast \in {no, yes}
  /\ decisionState \in {no, yes}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* Action 2 of the spec: it is the liveness property that the simple
\* broadcast variant fails to satisfy.
AllDecided == <>(\A q \in participants : pstate[q] # undecided)

\* No two participants ever commit and abort at once.
Agreement == ~(\E p, q \in participants : pstate[p] = commit /\ pstate[q] = abort)

\* Commit is only possible when every participant voted yes.
ValidCommit == (commit \in {pstate[q] : q \in participants}) => (\A q \in participants : pstate[q] = yes)
ValidAbort == (abort \in {pstate[q] : q \in participants}) => ((\E q \in participants : pstate[q] = no)
                                                             \/ (faulty # {})
                                                             \/ (decisionState = no))

\* A participant's decision is final and never flips.
Irreversible == \A q \in participants : (pstate[q] = undecided) ~> (pstate[q] # undecided)

\* At least one participant has decided or some actor has crashed.
Ac3 == <>(\A q \in participants : pstate[q] # undecided) \/ (faulty # {}) \/ (decisionState = no)

====