---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {}
ASSUME yes # no

VARIABLES vote, alive, decision, faulty, votesent, req, cVote, cast, cdecision, calive, cfaulty, fwd

vars == <<vote, alive, decision, faulty, votesent, req, cVote, cast, cdecision, calive, cfaulty, fwd>>

Quorums == {{p \in participants : vote[p] = yes}}

\* The forwarding table is per-participant: fwd[p] records the pre-decision p
\* has received and which other participants p has already forwarded it to.
Pids == participants \X participants

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ votesent = [p \in participants |-> FALSE]
  /\ req = waiting
  /\ cVote = undecided
  /\ cast = [p \in participants |-> undecided]
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (same as the base simple broadcast spec).
SendReq ==
  /\ calive
  /\ req = waiting
  /\ req' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

GetVote(p) ==
  /\ calive
  /\ req = yes
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = cVote]
  /\ UNCHANGED <<alive, decision, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

CoordFault ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

MakeDecision ==
  /\ calive
  /\ cVote = undecided
  /\ req = yes
  /\ cVote' = IF Quorums # {}
              THEN yes ELSE no
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cast,
                 cdecision, calive, cfaulty, fwd>>

Broadcast ==
  /\ calive
  /\ cVote # undecided
  /\ cdecision' = cVote
  /\ cast' = [p \in participants |-> cVote]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote,
                 cdecision, calive, cfaulty, fwd>>

Die ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote,
                 cast, cdecision, calive, cfaulty, fwd>>

\* A participant stores the pre-decision the coordinator broadcast to it.
PredecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ cdecision # undecided
  /\ cast[p] = cdecision
  /\ fwd' = [fwd EXCEPT ![p][p] = cdecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty>>

\* A participant stores a pre-decision forwarded by another participant.
PredecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][q] # notsent
       /\ fwd[q][p] = notsent
       /\ fwd' = [fwd EXCEPT ![q][p] = fwd[q][q]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty>>

\* Forward the pre-decision to another participant that has not yet received it.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty>>

\* Commit or abort only after forwarding the pre-decision to every other participant.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : q # p => fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

\* Abort when the coordinator is gone and no (alive or dead) participant can inform p.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~calive
  /\ (\A q \in participants : cast[q] = notsent \/ ~alive[q])
  /\ (\A q \in participants :
        ~(~alive[q] /\ fwd[q][p] # notsent))
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, votesent, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

SendVote(p) ==
  /\ alive[p]
  /\ ~votesent[p]
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

AbortVote(p) ==
  /\ alive[p]
  /\ ~votesent[p]
  /\ cVote = no
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, req, cVote, cast,
                 cdecision, calive, cfaulty, fwd>>

Next ==
  \/ SendReq \/ MakeDecision \/ Broadcast \/ Die \/ CoordFault
  \/ (\E p \in participants :
        SendVote(p) \/ AbortVote(p) \/ DieP(p))
  \/ (\E p \in participants : PredecideFromCoord(p) \/ PredecideFromFwd(p) \/ Decide(p))
  \/ (\E p \in participants, q \in participants : Forward(p, q))
  \/ (\E p \in participants : AbortOnTimeout(p))

SpecNB == Init /\ [][Next]_vars
         /\ WF_vars(SendReq) /\ WF_vars(SendVote(p) \/ AbortVote(p) \/ DieP(p) \/ Die \/ CoordFault)
         /\ WF_vars(PredecideFromCoord(p) \/ PredecideFromFwd(p))
         /\ WF_vars(Decide(p) \/ AbortOnTimeout(p))

TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ votesent \in [participants -> BOOLEAN]
  /\ req \in {waiting, yes}
  /\ cVote \in {undecided, yes, no}
  /\ cast \in [participants -> {undecided, yes, no}]
  /\ cdecision \in {undecided, yes, no}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* No two participants ever reach different decisions.
Agreement == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

\* A committed transaction was approved by every participant.
CommitValidity == \A p \in participants : decision[p] = commit => vote[p] = yes

\* An aborted transaction was caused by a no vote, a participant fault, or a
\* coordinator fault.
AbortValidity == \A p \in participants : decision[p] = abort
                    => (vote[p] = no \/ faulty[p] \/ cfaulty)

\* Once decided, a participant never reverts to undecided.
Irrevocability == \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
                    ~> (decision[p] = commit \/ decision[p] = abort)

\* If the coordinator's broadcast is unavailable, the protocol still makes progress:
\* the participants that remain alive must decide.
AC3 == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ cfaulty)

\* Every non-faulty participant eventually decides (the reliable broadcast ensures
\* no survivor is left waiting on a crashed coordinator alone).
AC5 == \A p \in participants : ~faulty[p] ~> (decision[p] = commit \/ decision[p] = abort)

====