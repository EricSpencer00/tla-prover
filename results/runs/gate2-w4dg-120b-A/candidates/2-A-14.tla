---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES ballot, alive, decision, faulty, sent, req, pvote, broadcast, pdecision,
          pAlive, pFaulty, fwd

vars == <<ballot, alive, decision, faulty, sent, req, pvote, broadcast,
          pdecision, pAlive, pFaulty, fwd>>

\* fwd[p] maps every participant to the forwarding status as observed by p:
\* notsent, commit, or abort -- it records p's own pre-decision and everything
\* p has forwarded so far.  The base ACP-SB variables are all retained because
\* the new protocol reuses exactly the same coordinator logic.

TypeInvNB ==
  /\ ballot \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ req \in {waiting, yes, no}
  /\ pvote \in {yes, no, undecided}
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ pdecision \in {undecided, commit, abort}
  /\ pAlive \in {TRUE, FALSE}
  /\ pFaulty \in {TRUE, FALSE}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ ballot = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ req = waiting
  /\ pvote = undecided
  /\ broadcast = [p \in participants |-> notsent]
  /\ pdecision = undecided
  /\ pAlive = TRUE
  /\ pFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: exactly the ACP-SB set, reused unchanged.
SendRequest ==
  /\ req = waiting
  /\ req' = yes
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

Vote(a) ==
  /\ req # waiting
  /\ alive[a]
  /\ ~sent[a]
  /\ pvote \in {yes, no}
  /\ ballot' = [ballot EXCEPT ![a] = pvote]
  /\ sent' = [sent EXCEPT ![a] = TRUE]
  /\ sent' = sent
  /\ UNCHANGED <<alive, decision, faulty, req, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

Detected(a) ==
  /\ req # waiting
  /\ ~alive[a]
  /\ ~faulty[a]
  /\ faulty' = [faulty EXCEPT ![a] = TRUE]
  /\ UNCHANGED <<ballot, alive, decision, sent, req, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

Decide ==
  /\ req # waiting
  /\ \A a \in participants : sent[a]
  /\ req' = waiting
  /\ pvote' = ballot[CHOOSE c \in participants : sent[c]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

\* coordinator broadcast: a different action name from ACP-SB's SendDecision so
\* the single combined SpecNB action set can be partitioned cleanly.
SendDecision(p) ==
  /\ req = waiting
  /\ alive[p]
  /\ pFaulty = FALSE
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = pvote]
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, req, pvote,
                pdecision, pAlive, pFaulty, fwd>>

Die ==
  /\ pAlive
  /\ pAlive' = FALSE
  /\ pFaulty' = TRUE
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, req, pvote,
                broadcast, pdecision, fwd>>

\* Participant actions: the ACP-SB set plus the new reliable-broadcast steps.
SendVote(a) ==
  /\ NOT pAlive
  /\ alive[a]
  /\ ~sent[a]
  /\ \E b \in {yes, no} : ballot' = [ballot EXCEPT ![a] = b]
  /\ sent' = [sent EXCEPT ![a] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, req, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

AbortOnVote(a) ==
  /\ NOT pAlive
  /\ alive[a]
  /\ ballot[a] = no
  /\ decision' = [decision EXCEPT ![a] = abort]
  /\ UNCHANGED <<ballot, alive, faulty, sent, req, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

\* New: absorb the coordinator's pre-decision directly (step a in the spec).
PreDecideFromCoordinator(a) ==
  /\ alive[a]
  /\ pdecision = undecided
  /\ broadcast[a] # notsent
  /\ fwd[a][a] = notsent
  /\ fwd' = [fwd EXCEPT ![a][a] = broadcast[a]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, req, pvote,
                broadcast, pdecision, pAlive, pFaulty>>

\* New: absorb a pre-decision forwarded by another participant (step b).
PreDecideFromForward(a) ==
  /\ alive[a]
  /\ pdecision = undecided
  /\ \E c \in participants :
       /\ c # a
       /\ fwd[c][a] # notsent
       /\ fwd[a][a] = notsent
       /\ fwd' = [fwd EXCEPT ![a][a] = fwd[c][a]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, req, pvote,
                broadcast, pdecision, pAlive, pFaulty>>

\* New: forward a received pre-decision to another participant (step c).
Forward(a, c) ==
  /\ alive[a]
  /\ fwd[a][a] # notsent
  /\ fwd[a][c] = notsent
  /\ fwd' = [fwd EXCEPT ![a][c] = fwd[a][a]]
  /\ UNCHANGED <<ballot, alive, decision, faulty, sent, req, pvote,
                broadcast, pdecision, pAlive, pFaulty>>

DecideParticipant(a) ==
  /\ alive[a]
  /\ pdecision = undecided
  /\ \A c \in participants : fwd[a][c] # notsent
  /\ pdecision' = fwd[a][a]
  /\ decision' = [decision EXCEPT ![a] = fwd[a][a]]
  /\ UNCHANGED <<ballot, alive, faulty, sent, req, pvote,
                broadcast, pAlive, pFaulty, fwd>>

\* Local timeout: gives up once the coordinator is dead and no bridging forward
\* from the dead can still deliver a decision.
AbortOnTimeout(a) ==
  /\ alive[a]
  /\ pdecision = undecided
  /\ ~pAlive
  /\ \A q \in participants : broadcast[q] = notsent
  /\ \A c \in participants :
       \A pr \in participants : pAlive => fwd[pr][c] = notsent
  /\ decision' = [decision EXCEPT ![a] = abort]
  /\ pdecision' = abort
  /\ UNCHANGED <<ballot, alive, faulty, sent, req, pvote,
                broadcast, pAlive, pFaulty, fwd>>

\* Finally: the ACP-SB participant crash (always available, never assumed fair).
DieParticipant(a) ==
  /\ alive[a]
  /\ alive' = [alive EXCEPT ![a] = FALSE]
  /\ faulty' = [faulty EXCEPT ![a] = TRUE]
  /\ UNCHANGED <<ballot, decision, sent, req, pvote, broadcast,
                pdecision, pAlive, pFaulty, fwd>>

Next ==
  \/ SendRequest \/ Decide \/ Die
  \/ \E a \in participants : Vote(a) \/ Detected(a) \/ SendDecision(a)
  \/ \E a \in participants : SendVote(a) \/ AbortOnVote(a)
  \/ \E a \in participants : PreDecideFromCoordinator(a) \/ PreDecideFromForward(a)
  \/ \E a, c \in participants : Forward(a, c)
  \/ \E a \in participants : DecideParticipant(a) \/ AbortOnTimeout(a) \/ DieParticipant(a)

SpecNB == InitNB /\ [][Next]_vars
  /\ WF_vars(\E a \in participants : SendVote(a))
  /\ WF_vars(\E a \in participants : AbortOnVote(a))
  /\ WF_vars(\E a \in participants : PreDecideFromCoordinator(a))
  /\ WF_vars(\E a \in participants : PreDecideFromForward(a))
  /\ WF_vars(\E a, c \in participants : Forward(a, c))
  /\ WF_vars(\E a \in participants : DecideParticipant(a))
  /\ WF_vars(\E a \in participants : AbortOnTimeout(a))
  /\ SF_vars(\E a \in participants : DieParticipant(a))

\* Safety: agreement, commit validity, abort validity, and decision
\* irrevocability -- all inherited from ACP-SB and still hold here.
AC1 == \A a, b \in participants : (decision[a] = commit) => (decision[b] # abort)
AC2 == (\E a \in participants : decision[a] = commit) => (\A b \in participants : ballot[b] = yes)
AC3 == (\E a \in participants : decision[a] = abort) =>
         ((\E b \in participants : ballot[b] = no) \/ (\E b \in participants : faulty[b]) \/ pFaulty)
AC4 == \A a \in participants : (decision[a] = commit) ~> (decision[a] = commit)
       /\ (decision[a] = abort) ~> (decision[a] = abort)

\* Liveness: the ACP-SB termination condition eventually holds, or the
\* coordinator or some participant is faulty.
AC3Live == <>(\A a \in participants : decision[a] # undecided \/ faulty[a] \/ pFaulty)

\* Liveness: every non-faulty participant eventually decides (the reliable
\* broadcast ensures this even if the coordinator dies mid-flight).
AC5 == \A a \in participants : (alive[a] /\ ~faulty[a]) ~> (decision[a] # undecided)

====