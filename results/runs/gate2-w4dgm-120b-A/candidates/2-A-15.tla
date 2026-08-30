---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-Blocking Atomic Commitment Protocol (ACP-NB).  This extends the     *)
(* simple broadcast protocol ACP-SB with a reliable broadcast mechanism:  *)
(* a participant forwards the received decision to all others before       *)
(* finalizing its own, so a crashed coordinator can never stall the        *)
(* protocol for a non-faulty participant.                                 *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

None == "none"

VARIABLES vote, alive, decision, faulty, sent, coordState, coordReq, coordVotes, coordBcast, coordDec, fwd

vars == << vote, alive, decision, faulty, sent, coordState, coordReq, coordVotes,
           coordBcast, coordDec, fwd >>

Rec == [ p \in participants |-> [ sent |-> notsent, dec |-> undecided ] ]

TypeOK ==
  /\ vote \in [ participants -> {yes, no} ]
  /\ alive \in [ participants -> BOOLEAN ]
  /\ decision \in [ participants -> {undecided, commit, abort} ]
  /\ faulty \in [ participants -> BOOLEAN ]
  /\ sent \in [ participants -> BOOLEAN ]
  /\ coordState \in {waiting, coordReq, coordVotes, coordBcast, coordDec}
  /\ coordReq \in participants \cup {None}
  /\ coordVotes \subseteq participants
  /\ coordBcast \in [ participants -> {undecided, commit, abort} ]
  /\ coordDec \in {commit, abort}
  /\ fwd \in [ participants -> [ participants -> {notsent, commit, abort} ] ]

Init ==
  /\ vote = [ p \in participants |-> yes ]
  /\ alive = [ p \in participants |-> TRUE ]
  /\ decision = [ p \in participants |-> undecided ]
  /\ faulty = [ p \in participants |-> FALSE ]
  /\ sent = [ p \in participants |-> FALSE ]
  /\ coordState = waiting
  /\ coordReq = None
  /\ coordVotes = {}
  /\ coordBcast = [ p \in participants |-> undecided ]
  /\ coordDec = commit
  /\ fwd = [ p \in participants |-> Rec ]

SendReq ==
  /\ coordState = waiting
  /\ \E p \in participants :
       /\ coordReq' = p
       /\ alive' = [ alive EXCEPT ![p] = TRUE ]
  /\ coordState' = coordReq
  /\ UNCHANGED << vote, decision, faulty, sent, coordVotes, coordBcast, coordDec, fwd >>

GetVote ==
  /\ coordState = coordReq
  /\ coordReq \notin coordVotes
  /\ coordVotes' = coordVotes \cup {coordReq}
  /\ UNCHANGED << vote, alive, decision, faulty, sent, coordState, coordReq,
                  coordBcast, coordDec, fwd >>

DetectFault ==
  /\ coordState = coordReq
  /\ \E p \in participants :
       /\ p \notin coordVotes
       /\ ~alive[p]
       /\ faulty' = [ faulty EXCEPT ![p] = TRUE ]
  /\ coordState' = coordVotes
  /\ UNCHANGED << vote, alive, decision, sent, coordReq, coordVotes, coordBcast,
                  coordDec, fwd >>

MakeDecision ==
  /\ coordState = coordVotes
  /\ \A p \in participants : alive[p] => p \in coordVotes
  /\ coordDec' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ coordState' = coordBcast
  /\ UNCHANGED << vote, alive, decision, faulty, sent, coordReq, coordVotes,
                  coordBcast, fwd >>

Broadcast ==
  /\ coordState = coordBcast
  /\ \E p \in participants :
       /\ coordBcast[p] = undecided
       /\ coordBcast' = [ coordBcast EXCEPT ![p] = coordDec ]
  /\ sent' = [ p \in participants |-> coordBcast[p] # undecided ]
  /\ UNCHANGED << vote, alive, decision, faulty, coordState, coordReq,
                  coordVotes, coordDec, fwd >>

Die ==
  /\ coordState # coordDec
  /\ coordState' = coordDec
  /\ faulty' = [ p \in participants |-> broken ]
  /\ UNCHANGED << vote, alive, decision, sent, coordReq, coordVotes,
                  coordBcast, coordDec, fwd >>

(* A participant receives its own pre-decision directly from the          *)
(* coordinator's broadcast.                                               *)
PreDecideFromCoord ==
  \E p \in participants :
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ coordBcast[p] # undecided
    /\ fwd' = [ fwd EXCEPT ![p][p] = coordBcast[p] ]
    /\ UNCHANGED << vote, alive, decision, faulty, sent, coordState, coordReq,
                    coordVotes, coordBcast, coordDec >>

(* A participant receives a pre-decision forwarded by another participant. *)
PreDecideFromFwd ==
  \E p \in participants :
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants \ {p} : fwd[q][p] # notsent
    /\ fwd' = [ fwd EXCEPT ![p][p] = CHOOSE q \in participants \ {p} : fwd[q][p] ]
    /\ UNCHANGED << vote, alive, decision, faulty, sent, coordState, coordReq,
                    coordVotes, coordBcast, coordDec >>

Forward ==
  \E q \in participants :
    /\ alive[q]
    /\ fwd[q][q] # notsent
    /\ \E p \in participants \ {q} :
         fwd[q][p] = notsent
         /\ fwd' = [ fwd EXCEPT ![q][p] = fwd[q][q] ]
    /\ UNCHANGED << vote, alive, decision, faulty, sent, coordState, coordReq,
                    coordVotes, coordBcast, coordDec >>

Decide ==
  \E p \in participants :
    /\ alive[p]
    /\ decision[p] = undecided
    /\ fwd[p][p] # notsent
    /\ \A q \in participants \ {p} : fwd[p][q] # notsent
    /\ decision' = [ decision EXCEPT ![p] = fwd[p][p] ]
    /\ UNCHANGED << vote, alive, faulty, sent, coordState, coordReq,
                    coordVotes, coordBcast, coordDec, fwd >>

(* Coordinated abort triggered by any observed fault: a no vote, a      *)
(* faulty participant, or a faulty coordinator.                        *)
AbortOnFault ==
  \E p \in participants :
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \/ (\E q \in participants : vote[q] = no)
       \/ (\E q \in participants : faulty[q])
       \/ faulty[coordReq]
    /\ decision' = [ decision EXCEPT ![p] = abort ]
    /\ UNCHANGED << vote, alive, faulty, sent, coordState, coordReq,
                    coordVotes, coordBcast, coordDec, fwd >>

Next ==
  \/ SendReq \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast \/ Die
  \/ PreDecideFromCoord \/ PreDecideFromFwd \/ Forward \/ Decide \/ AbortOnFault

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PreDecideFromCoord)
  /\ WF_vars(PreDecideFromFwd)
  /\ WF_vars(Forward)
  /\ WF_vars(Decide)
  /\ WF_vars(AbortOnFault)

TypeInvNB == TypeOK

(* No two participants reach different decisions.                           *)
AC1 == \A p, q \in participants : (decision[p] = commit) => (decision[q] = commit)

(* Commit only when everyone voted yes.                                     *)
AC2 == \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

(* Abort only on a no vote, a faulty participant, or a faulty coordinator.   *)
AC3 == \A p \in participants :
        decision[p] = abort =>
          (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty[coordReq]

(* Decisions are permanent: once decided, a participant never changes state. *)
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

(* Liveness: every non-faulty participant eventually decides.                *)
AC5 == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

====