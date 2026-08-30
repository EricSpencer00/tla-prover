---- MODULE ACP_NB ----
EXTENDS Integers, FiniteSets

(*  Non-Blocking Atomic Commitment (ACP-NB).  This extends the simple   *)
(*  broadcast protocol (ACP-SB) by adding reliable broadcast: a         *)
(*  participant forwards the coordinator's decision to every other     *)
(*  participant before finalizing locally.  This ensures termination   *)
(*  even if the coordinator crashes during broadcast.                  *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, coord, fwd

vars == <<pstate, alive, decision, faulty, voteSent, coord, fwd>>

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coord \in {waiting, commit, abort}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coord = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends the initial request to every participant.
SendReq ==
  /\ coord = waiting
  /\ coord' = commit
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

\* A participant votes yes or no and sends its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ ~voteSent[p]
  /\ pstate[p] = undecided
  /\ \E v \in {yes, no} : pstate' = [pstate EXCEPT ![p] = v]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coord, fwd>>

\* The coordinator records a vote it has received.
GetVote(p) ==
  /\ coord = commit
  /\ alive[p]
  /\ voteSent[p]
  /\ pstate[p] # undecided
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord, fwd>>

\* Crash the coordinator.
DetectFault ==
  /\ coord = commit
  /\ coord' = abort
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

\* The coordinator makes its decision once every participant has voted.
Decide ==
  /\ coord = commit
  /\ \A p \in participants : pstate[p] # undecided
  /\ coord' = (IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, fwd>>

\* The coordinator broadcasts its decision to an alive participant.
Broadcast(p) ==
  /\ coord \in {commit, abort}
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = IF coord = commit THEN commit ELSE abort]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord>>

\* The coordinator crashes.
Die ==
  /\ alive[CHOOSE p \in participants : TRUE]
  /\ coord' = waiting
  /\ alive' = [p \in participants |-> FALSE]
  /\ UNCHANGED <<pstate, decision, faulty, voteSent, fwd>>

\* A participant receives a pre-decision broadcast from the coordinator.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coord, fwd>>

\* A participant receives a pre-decision forwarded by another participant.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ decision' = [decision EXCEPT ![p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coord, fwd>>

\* A participant forwards a pre-decision it has to another alive participant.
Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # waiting
  /\ alive[q]
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord>>

\* A participant finalizes once it has forwarded its pre-decision to everyone.
DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] # waiting
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coord, fwd>>

\* An undecided participant aborts when the coordinator is dead and no
\* broadcast or forwarding from a dead participant is pending.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ coord = waiting
  /\ \A q \in participants : ~alive[q]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coord, fwd>>

\* A participant crashes silently and becomes faulty.
DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, coord, fwd>>

Next ==
  \/ SendReq \/ DetectFault \/ Decide \/ Die
  \/ \E p \in participants :
       SendVote(p) \/ GetVote(p) \/ Broadcast(p) \/ PreDecideCoord(p)
         \/ PreDecideFwd(p) \/ DecideNB(p) \/ AbortTimeout(p) \/ DieP(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(DecideNB(p))
  /\ WF_vars(DetectFault)

(* No two participants can reach different decisions.                         *)
Agreement == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

(* Commit is only possible if every participant voted yes.                     *)
CommitValid == (\E p \in participants : decision[p] = commit) => \A p \in participants : pstate[p] = yes

(* Abort is only possible if some participant voted no, or someone is faulty.   *)
AbortValid ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E p \in participants : pstate[p] = no
    \/ \E p \in participants : faulty[p]
    \/ coord = waiting

(* A participant that has decided stays decided.                                 *)
Irrevocable ==
  \A p \in participants : (decision[p] # waiting) ~> (decision[p] = decision[p])

(* Either everyone has decided, or some participant or the coordinator is       *)
(* faulty: the system eventually reaches a final state.                         *)
AllDecideOrCrash ==
  <>( \A p \in participants : decision[p] # waiting \/ \E p \in participants : faulty[p] \/ coord = waiting)

(* Every non-faulty participant eventually decides.                             *)
NoBlock == \A p \in participants : (~faulty[p]) ~> (decision[p] # waiting)

====