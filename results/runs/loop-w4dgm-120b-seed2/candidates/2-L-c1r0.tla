---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumSet(f, S \ {x})

VARIABLES vote, alive, decision, faulty, votesent, coord, forwarded

vars == <<vote, alive, decision, faulty, votesent, coord, forwarded>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ votesent \in [participants -> BOOLEAN]
  /\ coord \in [req : BOOLEAN, vote : [participants -> {yes, no, undecided}],
                broadcast : [participants -> {undecided, commit, abort}],
                decision : {undecided, commit, abort}, alive : BOOLEAN]
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ votesent = [p \in participants |-> FALSE]
  /\ coord = [req |-> FALSE, vote |-> [p \in participants |-> undecided],
              broadcast |-> [p \in participants |-> undecided],
              decision |-> undecided, alive |-> TRUE]
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coord.req = FALSE
  /\ coord.alive = TRUE
  /\ coord' = [coord EXCEPT !.req = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forwarded>>

GetVote(p) ==
  /\ coord.req = TRUE
  /\ coord.vote[p] = undecided
  /\ \E v \in {yes, no} : coord' = [coord EXCEPT !.vote[p] = v]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forwarded>>

DetectCoordFault ==
  /\ coord.alive = TRUE
  /\ \E p \in participants :
       /\ vote[p] # undecided
       /\ coord' = [coord EXCEPT !.alive = FALSE]
       /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, alive, decision, votesent, forwarded>>

MakeDecision ==
  /\ coord.req = TRUE
  /\ \A p \in participants : coord.vote[p] # undecided
  /\ coord.decision = undecided
  /\ coord' = [coord EXCEPT !.decision =
                 IF \A p \in participants : coord.vote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forwarded>>

BroadcastDecision(p) ==
  /\ coord.alive = TRUE
  /\ coord.decision # undecided
  /\ coord.broadcast[p] = undecided
  /\ coord' = [coord EXCEPT !.broadcast[p] = coord.decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forwarded>>

SendVote(p) ==
  /\ alive[p] = TRUE
  /\ votesent[p] = FALSE
  /\ vote[p] # undecided
  /\ vote' = [vote EXCEPT ![p] = undecided]
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coord, forwarded>>

PreDecideCoord(p) ==
  /\ alive[p] = TRUE
  /\ forwarded[p][p] = notsent
  /\ coord.alive = TRUE
  /\ coord.decision # undecided
  /\ coord.broadcast[p] = coord.decision
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coord.decision]
  /\ UNCHANGED <<vote, alive, decision, votesent, coord, faulty>>

PreDecideForward(q, p) ==
  /\ alive[p] = TRUE
  /\ forwarded[p][p] = notsent
  /\ q # p
  /\ forwarded[q][p] # notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<vote, alive, decision, votesent, coord, faulty>>

Forward(p, q) ==
  /\ alive[p] = TRUE
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, decision, votesent, coord, faulty>>

Decide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants : forwarded[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, coord, forwarded>>

AbortOnTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ coord.alive = FALSE
  /\ \A q \in participants : coord.broadcast[q] = undecided
  /\ \A q \in participants : (alive[q] = FALSE => forwarded[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, votesent, coord, forwarded, faulty>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, votesent, coord, forwarded>>

Next ==
  \/ SendRequest \/ DetectCoordFault \/ MakeDecision
  \/ \E p \in participants :
       SendVote(p) \/ PreDecideCoord(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants :
       \E q \in participants : PreDecideForward(q, p) \/ Forward(p, q)
  \/ \E p \in participants : BroadcastDecision(p)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

AC1 == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
  \A p \in participants :
    (decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 ==
  \A p \in participants :
    (decision[p] = abort) =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : q \in faulty
      \/ coord.alive = FALSE

AC4 ==
  \A p \in participants :
    \A d \in {commit, abort} : (decision[p] = d) ~> (decision[p] = d)

AC5 ==
  \A p \in participants :
    (p \notin faulty) ~> (decision[p] # undecided)

====