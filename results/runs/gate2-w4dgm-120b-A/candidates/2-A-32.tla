---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

(* Non-blocking atomic commitment with reliable broadcast.  A participant     *)
(* stores a pre-decision when it receives one, forwards it to every other     *)
(* participant, and only then finalizes locally.  This forwarding is what      *)
(* guarantees termination even if the coordinator crashes mid-broadcast.       *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, req, v, broadcasted, cdecide

vars == <<vote, alive, decision, faulty, sentVote, req, v, broadcasted, cdecide>>

TypeOK ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {commit, abort, waiting}
    /\ faulty \in [participants -> BOOLEAN]
    /\ req \in BOOLEAN
    /\ v \in BOOLEAN
    /\ broadcasted \in [participants -> BOOLEAN]
    /\ cdecide \in {commit, abort, notsent}
    /\ sentVote \in [participants -> BOOLEAN]

\* forwardMap[i][j] = decision i has forwarded to j (or notsent).
ForwardMap == [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [i \in participants |-> undecided]
    /\ alive = [i \in participants |-> TRUE]
    /\ decision = waiting
    /\ faulty = [i \in participants |-> FALSE]
    /\ sentVote = [i \in participants |-> FALSE]
    /\ req = FALSE
    /\ v = FALSE
    /\ broadcasted = [i \in participants |-> FALSE]
    /\ cdecide = notsent
    /\ \A i \in participants : [j \in participants |-> notsent]

\* The coordinator actions (they are unchanged from the simple broadcast spec).
SendReq ==
    /\ ~req
    /\ ~v
    /\ \A i \in participants : vote[i] # undecided
    /\ req' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, v, broadcasted, cdecide>>

GetVote(i) ==
    /\ req
    /\ ~v
    /\ alive[i]
    /\ ~sentVote[i]
    /\ sentVote' = [sentVote EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, req, v, broadcasted, cdecide>>

\* Failure detection: once every participant has voted, the coordinator may
\* notice a faulty participant and mark itself faulty in response.
DetectFault ==
    /\ req
    /\ ~v
    /\ \A i \in participants : sentVote[i]
    /\ \E i \in participants : faulty[i]
    /\ v' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, broadcasted, cdecide>>

MakeDecision ==
    /\ req
    /\ v
    /\ decision = waiting
    /\ decision' = IF \A i \in participants : vote[i] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, faulty, sentVote, req, v broadcasted, cdecide>>

Broadcast(i) ==
    /\ decision # waiting
    /\ alive[i]
    /\ ~broadcasted[i]
    /\ broadcasted' = [broadcasted EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, v, cdecide>>

Die ==
    /\ \E i \in participants : alive[i]
    /\ \E i \in participants : alive' = [alive EXCEPT ![i] = FALSE]
    /\ \E i \in participants : faulty' = [faulty EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, req, v, broadcasted, cdecide>>

\* A participant stores the coordinator's broadcast as its pre-decision.
ReceiveFromCoordinator(i) ==
    /\ alive[i]
    /\ ForwardMap[i][i] = notsent
    /\ broadcasted[i]
    /\ ForwardMap' = [ForwardMap EXCEPT ![i][i] = cdecide]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, v, broadcasted, cdecide>>

\* A participant stores a forwarded pre-decision from another participant.
ReceiveFromPeer(i) ==
    /\ alive[i]
    /\ ForwardMap[i][i] = notsent
    /\ \E j \in participants :
         /\ j # i
         /\ ForwardMap[j][i] # notsent
         /\ ForwardMap' = [ForwardMap EXCEPT ![i][i] = ForwardMap[j][i]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, v, broadcasted, cdecide>>

\* Once a pre-decision is stored, a participant forwards it to a peer that
\* still has not received it.
Forward(i, j) ==
    /\ alive[i]
    /\ ForwardMap[i][i] # notsent
    /\ ForwardMap[i][j] = notsent
    /\ ForwardMap' = [ForwardMap EXCEPT ![i][j] = ForwardMap[i][i]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req, v, broadcasted, cdecide>>

\* Finalize only after the pre-decision has been forwarded to everyone, which
\* is what makes the protocol non-blocking even if the coordinator dies.
Decide(i) ==
    /\ alive[i]
    /\ ForwardMap[i][i] # notsent
    /\ \A j \in participants : ForwardMap[i][j] # notsent
    /\ decision' = IF ForwardMap[i][i] = commit THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, faulty, sentVote, req, v, broadcasted, cdecide, ForwardMap>>

AbortOnTimeout(i) ==
    /\ alive[i]
    /\ decision = waiting
    /\ ~v
    /\ \A j \in participants : ~broadcasted[j]
    /\ \A j \in participants : ~(~alive[j] /\ \E k \in participants : ForwardMap[j][k] # notsent)
    /\ decision' = abort
    /\ UNCHANGED <<vote, alive, faulty, sentVote, req, v, broadcasted, cdecide, ForwardMap>>

Next ==
    \/ SendReq
    \/ DetectFault
    \/ MakeDecision
    \/ Die
    \/ \E i \in participants : GetVote(i)
    \/ \E i \in participants : Broadcast(i)
    \/ \E i \in participants : ReceiveFromCoordinator(i)
    \/ \E i \in participants : ReceiveFromPeer(i)
    \/ \E i \in participants : Decide(i)
    \/ \E i \in participants : AbortOnTimeout(i)
    \/ \E i, j \in participants : Forward(i, j)

SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(\E i \in participants : ReceiveFromCoordinator(i))
    /\ WF_vars(\E i \in participants : ReceiveFromPeer(i))
    /\ WF_vars(\E i, j \in participants : Forward(i, j))
    /\ WF_vars(\E i \in participants : Decide(i))
    /\ WF_vars(\E i \in participants : AbortOnTimeout(i))

TypeInvNB == TypeOK

(* Agreement: no two participants reach different decisions.  Termination of  *)
(* the live participants: every non-faulty participant eventually decides.   *)
Agreement == ~(decision = commit /\ decision = abort)

TerminationLiveness ==
    \A i \in participants : (alive[i] /\ faulty[i] = FALSE) ~> (decision # waiting)

====