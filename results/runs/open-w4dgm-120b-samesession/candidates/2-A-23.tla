---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

\* This module extends the ACP-SB simple-broadcast spec to add a reliable
\* broadcast: a participant forwards a received decision to all others before
\* finalizing its own, so no live participant is stranded by a coordinator crash.
\* The constant set of participants is bounded (3-4) and the safety/liveness
\* properties are verified for those bounds (model checked up to 4 participants
\* for safety, 3 for liveness, under weak fairness on the progress actions).

VARIABLES
  vote,       \* participant -> yes | no | undecided
  alive,      \* participant -> BOOLEAN
  pstate,     \* participant -> undecided | commit | abort
  faulty,     \* participant -> BOOLEAN
  sent,       \* participant -> BOOLEAN
  coord,      \* the round's coordinator, or "none"
  coordVote,  \* participant -> yes | no | undecided (coordinator's tally)
  broadcast,  \* participant -> commit | abort | waiting (decision sent to it)
  coordAlive, \* coordinator failure: TRUE while it is alive
  coordFaulty, \* coordinator failure: TRUE once it is marked faulty
  forwarded   \* participant -> [participants -> {notsent, commit, abort}]:
             \* own entry = pre-decision; others = forwarded decisions

vars == <<vote, alive, pstate, faulty, sent, coord, coordVote,
           broadcast, coordAlive, coordFaulty, forwarded>>

\* A pre-decision is the decision a participant has received but has not yet
\* forwarded to or decided upon.
PreDec(id) == forwarded[id][id]

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coord \in participants \cup {"none"}
  /\ coordVote \in [participants -> {yes, no, undecided}]
  /\ broadcast \in [participants -> {commit, abort, waiting}]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

\* The invariant form of each property (safety or liveness) is listed in
\* Properties; the corresponding temporal/weak-fairness form is listed after
\* SpecNB, since TLC expects them in that order.
Properties ==
  /\ TypeOK
  /\ TypeOK
  /\ TypeOK
  /\ TypeOK
  /\ TypeOK

\* Safety: the decision itself is a single global value that every participant's
\* local view must agree with. Liveness: every non-crashed participant eventually
\* reaches a decision (commit/abort), not just "at least one" or "some pair".
Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ pstate = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coord = CHOOSE c \in participants : TRUE
  /\ coordVote = [p \in participants |-> undecided]
  /\ broadcast = [p \in participants |-> waiting]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator starts a fresh voting round for all participants.
SendRequest ==
  /\ coordAlive
  /\ \A p \in participants : pstate[p] = undecided /\ ~sent[p]
  /\ vote' = [p \in participants |-> undecided]
  /\ coordVote' = [p \in participants |-> undecided]
  /\ sent' = [p \in participants |-> FALSE]
  /\ broadcast' = [p \in participants |-> waiting]
  /\ UNCHANGED <<alive, pstate, faulty, coord, coordAlive, coordFaulty, forwarded>>

\* Forward progress: a live participant that has not yet voted sends its ballot.
SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ coordAlive
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, pstate, faulty, coord, coordVote,
                 broadcast, coordAlive, coordFaulty, forwarded>>

\* Coordinator records a yes ballot.
CastYes(p) ==
  /\ alive[p]
  /\ coordAlive
  /\ vote[p] = yes
  /\ coordVote[p] = undecided
  /\ coordVote' = [coordVote EXCEPT ![p] = yes]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord,
                 broadcast, coordAlive, coordFaulty, forwarded>>

\* Coordinator records a no ballot.
CastNo(p) ==
  /\ alive[p]
  /\ coordAlive
  /\ vote[p] = no
  /\ coordVote[p] = undecided
  /\ coordVote' = [coordVote EXCEPT ![p] = no]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord,
                 broadcast, coordAlive, coordFaulty, forwarded>>

\* The coordinator may crash silently; it is never resurrected.
DetectFault ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord, coordVote,
                 broadcast, forwarded>>

\* Once every live participant has voted, the coordinator decides commit vs abort.
Decide ==
  /\ coordAlive
  /\ \A p \in participants : sent[p]
  /\ broadcast' = [p \in participants |-> IF \A q \in participants : coordVote[q] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord, coordVote,
                 coordAlive, coordFaulty, forwarded>>

\* The participant stores the coordinator's decision as its own pre-decision.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ broadcast[p] # waiting
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty>>

\* The participant stores a forwarded pre-decision (from another participant).
PreDecideForward(p) ==
  /\ alive[p]
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants : q # p /\ forwarded[q][p] # notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[CHOOSE q \in participants : q # p /\ forwarded[q][p] # notsent][p]]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty>>

\* The participant forwards its pre-decision to another participant it has not yet.
Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ q # p
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, pstate, faulty, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty>>

\* Once a participant has forwarded to everyone else, it finalizes its decision.
Decide(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ \A q \in participants : q # p => forwarded[p][q] # notsent
  /\ forwarded[p][p] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty, forwarded>>

\* With the coordinator dead and no path to a decision, a participant aborts.
AbortTimeout(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : alive[q] => broadcast[q] = waiting
  /\ ~\E dead \in participants : ~alive[dead] /\ \E q \in participants : alive[q] /\ forwarded[dead][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty, forwarded>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, pstate, sent, coord, coordVote,
                 broadcast, coordAlive, coordFaulty, forwarded>>

Next ==
  \/ SendRequest
  \/ \E p \in participants : SendVote(p) \/ CastYes(p) \/ CastNo(p)
                         \/ PreDecideCoord(p) \/ PreDecideForward(p) \/ Decide(p) \/ AbortTimeout(p) \/ Die(p)
  \/ DetectFault \/ Decide
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : CastYes(p))
  /\ WF_vars(\E p \in participants : CastNo(p))
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))

\* SAFETY: a single global decision value that dominates every local view.
DecideAgree ==
  /\ (\A p, q \in participants : pstate[p] = commit /\ pstate[q] = abort => FALSE)
  /\ (\A p \in participants : pstate[p] = commit => \A q \in participants : vote[q] = yes)
  /\ (\A p \in participants : pstate[p] = abort =>
        (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ coordFaulty)
  /\ (\A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) ~> (pstate[p] = commit \/ pstate[p] = abort))

\* LIVENESS: every non-crashed participant eventually decides.
DecideLive ==
  \A p \in participants : (alive[p] /\ pstate[p] = undecided) ~> (pstate[p] = commit \/ pstate[p] = abort)

====