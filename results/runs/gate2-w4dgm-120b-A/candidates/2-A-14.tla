---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes = "yes" /\ no = "no" /\ undecided = "undecided" /\ commit = "commit" /\ abort = "abort" /\ waiting = "waiting" /\ notsent = "notsent"

VARIABLES ballot, alive, decision, faulty, voteSent, coordState, fwd

vars == <<ballot, alive, decision, faulty, voteSent, coordState, fwd>>

Init ==
  /\ ballot = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = [req |-> FALSE, vote |-> {}, bcast |-> {}, dec |-> waiting]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends request to participants.
SendReq ==
  /\ \A p \in participants : alive[p]
  /\ ~coordState.req
  /\ coordState' = [coordState EXCEPT !.req = TRUE]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, fwd>>

\* A participant sends its yes/no ballot back to the coordinator.
SendVote(p) ==
  /\ \A q \in participants : alive[q]
  /\ coordState.req
  /\ ~voteSent[p]
  /\ ballot' = [ballot EXCEPT ![p] =
        IF \E r \in participants : ballot[r] = no THEN no ELSE yes]
  /\ coordState' = [coordState EXCEPT !.vote = coordState.vote \cup {p}]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, fwd>>

\* The coordinator detects a participant has failed and aborts the transaction.
DetectFault ==
  /\ coordState.req
  /\ coordState.dec = waiting
  /\ coordState.dec' = abort
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, fwd, coordState>>

\* The coordinator decides commit only if every vote is yes.
DecideCommit ==
  /\ coordState.req
  /\ coordState.dec = waiting
  /\ coordState.vote = participants
  /\ \A p \in participants : ballot[p] = yes
  /\ coordState' = [coordState EXCEPT !.dec = commit]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, fwd>>

\* The coordinator decides abort if any vote is no.
DecideAbort ==
  /\ coordState.req
  /\ coordState.dec = waiting
  /\ \E p \in participants : ballot[p] = no
  /\ coordState' = [coordState EXCEPT !.dec = abort]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, fwd>>

\* The coordinator broadcasts its decision to all participants.
Broadcast ==
  /\ coordState.req
  /\ coordState.dec \in {commit, abort}
  /\ coordState.bcast = {}
  /\ coordState' = [coordState EXCEPT !.bcast = participants]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ballot, decision, voteSent, coordState, fwd>>

\* A participant receives the coordinator's decision as a pre-decision.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ coordState.dec \in {commit, abort}
  /\ coordState.bcast = participants
  /\ fwd' = [fwd EXCEPT ![p][p] = coordState.dec]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, coordState>>

\* A participant receives a pre-decision forwarded by another participant.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       q # p /\ fwd[q][p] # notsent /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, coordState>>

\* A participant forwards its pre-decision to another participant.
Forward(p, to) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][to] = notsent
  /\ fwd' = [fwd EXCEPT ![p][to] = fwd[p][p]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, voteSent, coordState>>

\* A participant finalizes its decision after forwarding to everyone.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<ballot, alive, faulty, voteSent, coordState, fwd>>

\* A participant aborts on timeout if the coordinator died and no path
\* exists to deliver a decision to it.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~alive[CHOOSE c \in participants : TRUE]
  /\ (\A q \in participants : coordState.bcast # participants)
  /\ \A q \in participants : ~(~alive[q] /\ \E r \in participants : fwd[r][p] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<ballot, alive, faulty, voteSent, coordState, fwd>>

Next ==
  \/ SendReq
  \/ \E p \in participants : SendVote(p)
  \/ DetectFault
  \/ DecideCommit
  \/ DecideAbort
  \/ Broadcast
  \/ \E p \in participants : Die(p)
  \/ \E p \in participants : PreDecideCoord(p)
  \/ \E p \in participants : PreDecideFwd(p)
  \/ \E p \in participants, to \in participants : Forward(p, to)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortTimeout(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFwd(p))
  /\ WF_vars(\E p \in participants, to \in participants : Forward(p, to))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : Die(p))

\* No two participants reach different decisions.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* If any participant commits, all participants voted yes.
CommitValidity ==
  (\E p \in participants : decision[p] = commit) => (\A q \in participants : ballot[q] = yes)

\* If any participant aborts, some participant voted no or is faulty or the
\* coordinator is faulty.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E q \in participants : ballot[q] = no
    \/ \E q \in participants : faulty[q]
    \/ \E c \in participants : faulty[c]

\* A decision, once committed or aborted, is permanent.
Irreversibility ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~> (decision[p] = decision[p])

\* Every non-faulty participant eventually reaches a decision.
Termination ==
  \A p \in participants : (\A q \in participants : ~faulty[q]) ~> (decision[p] \in {commit, abort})

TypeInvNB ==
  /\ ballot \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in [req : BOOLEAN, vote : SUBSET participants, bcast : SUBSET participants, dec : {waiting, commit, abort}]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

====