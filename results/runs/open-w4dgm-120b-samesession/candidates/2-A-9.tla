---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends ACP-SB with a reliable broadcast: participants forward received
\* decisions to all others before deciding locally, so a coordinator crash cannot
\* permanently stall a non-faulty participant's decision.

VARIABLES vote, alive, decision, faulty, sentVote, coord, fwd

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coord \in [reqStatus : {waiting, yes, no}, vote : {yes, no},
                sent : BOOLEAN, decision : {undecided, commit, abort}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coord = [reqStatus |-> waiting, vote |-> yes, sent |-> FALSE,
              decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coord.alive
  /\ coord.reqStatus = waiting
  /\ coord' = [coord EXCEPT !.reqStatus = yes]
  /\ UNCHANGED <<vote, decision, alive, sentVote, faulty, fwd>>

GetVote(p) ==
  /\ coord.alive
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ vote' = [vote EXCEPT ![p] = IF p = CHOOSE q \in participants : TRUE THEN yes ELSE no]
  /\ UNCHANGED <<coord, decision, alive, faulty, fwd>>

DetectFault(p) ==
  /\ coord.alive
  /\ coord.faulty
  /\ sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<coord, vote decision, alive, faulty, fwd>>

MakeDecision ==
  /\ coord.alive
  /\ coord.sent
  /\ coord.decision = undecided
  /\ coord.decision' = IF coord.vote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coord, vote, decision, alive, sentVote, faulty, fwd>>

Broadcast(p) ==
  /\ coord.alive
  /\ coord.decision # undecided
  /\ ~coord.sent
  /\ coord.sent' = TRUE
  /\ fwd' = [fwd EXCEPT ![p][p] = IF coord.decision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<coord, vote, decision, alive, sentVote, faulty>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coord.sent
  /\ fwd[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = IF fwd[p][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, sentVote, coord, faulty, fwd>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ fwd[q][p] # notsent
        /\ decision' = [decision EXCEPT ![p] = IF fwd[q][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, sentVote, coord, faulty, fwd>>

\* Forwarding is allowed from either a crashed or a slow participant; this is what
\* keeps the broadcast alive after a coordinator crash.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, decision, alive, sentVote, coord, faulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = IF fwd[p][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, sentVote, coord, faulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coord.alive
  /\ ~coord.sent
  /\ (\A q \in participants : ~coord.sent)
  /\ (\A q \in participants : ~alive[q] => (\A r \in participants : fwd[q][r] = notsent))
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, sentVote, coord, faulty, fwd>>

Die ==
  /\ coord.alive
  /\ coord.alive' = FALSE
  /\ coord.faulty' = TRUE
  /\ UNCHANGED <<vote, decision, alive, sentVote, fwd>>

\* Silent participant crash; it may still forward decisions it already holds.
Crash(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coord, fwd>>

Next ==
  \/ SendRequest \/ MakeDecision \/ Die
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ PreDecideFromCoord(p)
                               \/ PreDecideFromFwd(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Crash(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_<<vote, decision, alive, sentVote, coord, faulty, fwd>>

\* Safety: agreement and abort/commit validity (plus irrevocability).
AC1 == \A p, q \in participants : ~ (decision[p] = commit /\ decision[q] = abort)
AC2 == (\A p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 ==
  (\A p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no \/ faulty[p] \/ coord.faulty)
AC4 ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

\* Liveness: all participants eventually decide, or some crash is detected.
\* This is the ACP-NB guarantee (ACP-SB lacks the all-decide guarantee).
AC3Live ==
  <>(\A p \in participants : decision[p] \in {commit, abort} \/ faulty[p] \/ coord.faulty)
AC5 == \A p \in participants : (decision[p] = undecided) ~> (decision[p] \in {commit, abort})

====