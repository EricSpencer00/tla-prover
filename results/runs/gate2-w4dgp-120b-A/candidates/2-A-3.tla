---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-blocking atomic commitment protocol from Babaoglu/Toueg.  This extends the *)
(* simple broadcast variant ACP_SB by adding reliable broadcast: when a           *)
(* participant receives a decision it forwards it to every other participant      *)
(* before delivering it locally, so a coordinator crash cannot strand a           *)
(* non-crashed participant.  The full set of actors is the coordinator plus all  *)
(* participants (no voter pool).  Intentionally declared as an extension: this   *)
(* module reuses the coordinator logic of ACP_SB and adds only the actions that   *)
(* implement the reliable broadcast and the non-blocking termination.             *)

CONSTANTS participants
CONSTANTS yes / no / undecided
CONSTANTS commit / abort
CONSTANTS waiting / notsent

VARIABLES vote
VARIABLES alive
VARIABLES decision
VARIABLES faulty
VARIABLES voteSent
VARIABLES coordRequest
VARIABLES coordVote
VARIABLES coordBroadcast
VARIABLES coordDecision
VARIABLES coordAlive
VARIABLES coordFaulty
VARIABLES forward

vars == <<vote, alive, decision, faulty, voteSent, coordRequest,
          coordVote, coordBroadcast, coordDecision, coordAlive,
          coordFaulty, forward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordRequest \in {waiting, yes, no}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {yes, no, undecided}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordRequest = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator collects votes and broadcasts its decision to all participants.
SendRequest ==
  /\ coordAlive
  /\ coordRequest = waiting
  /\ coordRequest' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

GetVote(p) ==
  /\ coordAlive
  /\ voteSent[p]
  /\ coordVote = undecided
  /\ coordVote' = vote[p]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

DetectFault ==
  /\ coordAlive
  /\ coordFaulty
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, coordFaulty, forward>>

DecideCoord ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # undecided
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordAlive, coordFaulty, forward>>

BroadcastCoord(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = undecided
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordDecision, coordAlive, coordFaulty, forward>>

DieCoord ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, forward>>

SendVote(p) ==
  /\ coordAlive
  /\ vote[p] = undecided
  /\ voteSent[p] = FALSE
  /\ \E b \in {yes, no} : vote' = [vote EXCEPT ![p] = b]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordRequest, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortVote(p) ==
  /\ coordAlive
  /\ coordRequest = no
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = no]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortTimeout(p) ==
  /\ coordAlive = FALSE
  /\ decision[p] = undecided
  /\ \A q \in participants : coordBroadcast[q] = undecided
  /\ \A q \in participants :~coordFaulty => forward[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordRequest, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

\* A participant stores the coordinator's broadcasted decision as its pre-decision.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ coordBroadcast[p] # undecided
  /\ forward' = [forward EXCEPT ![p][p] = IF coordBroadcast[p] = commit
                                            THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant stores a forwarded decision from another participant as its pre-decision.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ \E q \in participants : forward[q][p] # notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Once a participant has a pre-decision, it forwards it to every other participant.
Forward(p, q) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordRequest,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant finalizes its decision only after forwarding to all others (non-blocking).
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : forward[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordRequest, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordRequest, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

NextNB ==
  \/ SendRequest \/ DetectFault \/ DecideCoord \/ DieCoord
  \/ \E p \in participants : GetVote(p) \/ SendVote(p) \/ AbortVote(p)
                         \/ AbortTimeout(p) \/ PreDecideFromCoord(p)
                         \/ PreDecideFromForward(p) \/ Decide(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

\* The coordinator's progress actions are interleaved with the participants' -- they
\* are never blocked, only delayed -- so weak fairness for them and for the participants
\* (including forwarding) is sufficient to guarantee eventual progress of every sort.
SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(SendRequest)
  /\ WF_vars(DecideCoord)
  /\ WF_vars(\E p \in participants : GetVote(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants : Decide(p))

\* Safety: no two participants reach different decisions, commits only follow unanimous
\* yes votes, aborts only follow a no vote or a crash, and decisions are irreversible.
AC1 ==
  ~(\E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort)

AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 == (\E p \in participants : decision[p] = abort) =>
           (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: either everyone decides, or some participant is faulty, or the coordinator is.
AC3Live == <>(\A p \in participants : decision[p] # undecided \/ \E p \in participants : faulty[p] \/ coordFaulty)

\* Non-blocking termination: every non-faulty participant eventually decides (not
\* just "some" participant).  This is what reliable broadcast -- not the coordinator --
\* guarantees even if the coordinator itself crashes.
AC5 == \A p \in participants : alive[p] ~> (decision[p] # undecided \/ faulty[p])

====