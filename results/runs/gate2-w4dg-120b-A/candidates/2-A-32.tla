---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteOut, coordReq, coordVote, coordMsg,
          coordDec, coordAlive, coordFaulty, forwards

vars == << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
           coordMsg, coordDec, coordAlive, coordFaulty, forwards >>

ForwardIDs == [to: participants, val: {commit, abort, notsent}]

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteOut \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no}
  /\ coordMsg \in [participants -> {commit, abort, undecided}]
  /\ coordDec \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwards \in [participants -> SUBSET ForwardIDs]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteOut = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = yes
  /\ coordMsg = [p \in participants |-> undecided]
  /\ coordDec = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwards = [p \in participants |-> {}]

SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordVote, coordMsg,
                 coordDec, coordAlive, coordFaulty, forwards >>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ alive[p]
  /\ ~voteOut[p]
  /\ vote[p] \in {yes, no}
  /\ coordVote' = IF coordVote = yes /\ vote[p] = yes THEN yes ELSE no
  /\ voteOut' = [voteOut EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty, coordReq, coordMsg,
                 coordDec, coordAlive, coordFaulty, forwards >>

DetectCoordFault ==
  /\ coordAlive
  /\ coordReq = no
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, forwards >>

DecideCoord ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ coordDec = undecided
  /\ coordDec' = coordVote
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordAlive, coordFaulty, forwards >>

BroadcastCoord(p) ==
  /\ coordAlive
  /\ coordDec # undecided
  /\ coordMsg[p] = undecided
  /\ coordMsg' = [coordMsg EXCEPT ![p] = coordDec]
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordDec, coordAlive, coordFaulty, forwards >>

DieCoord ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, forwards >>

SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED << alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty, forwards >>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty, forwards >>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordMsg[p] # undecided
  /\ ~\E f \in forwards[p] : f.to = p
  /\ forwards' = [forwards EXCEPT ![p] = @ \cup
                    {[to |-> p, val |-> coordMsg[p]]}]
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty >>

PreDecideForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~\E f \in forwards[p] : f.to = p
  /\ \E q \in participants : \E f \in forwards[q] :
        /\ f.to = p
        /\ f.val # notsent
        /\ forwards' = [forwards EXCEPT ![p] = @ \cup
                          {[to |-> p, val |-> f.val]}]
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty >>

Forward(p) ==
  /\ alive[p]
  /\ \E f \in forwards[p] :
        /\ f.val # notsent
        /\ \E g \in participants :
             /\ g # p
             /\ \A h \in forwards[p] : h.to # g
             /\ forwards' = [forwards EXCEPT ![p] = @ \cup
                               {[to |-> g, val |-> f.val]}]
  /\ UNCHANGED << vote, alive, decision, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty >>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E f \in forwards[p] : f.val # notsent
  /\ \A q \in participants : q # p => \E f \in forwards[p] : f.to = q
  /\ decision' = [decision EXCEPT ![p] = CHOOSE f \in forwards[p] : f.to = p /\ f.val # notsent].val
  /\ UNCHANGED << vote, alive, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty, forwards >>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordMsg[q] = undecided
  /\ \A q \in participants : \A f \in forwards[q] : f.val # notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteOut, coordReq, coordVote,
                 coordMsg, coordDec, coordAlive, coordFaulty, forwards >>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, decision, voteOut, coordReq, coordVote, coordMsg,
                 coordDec, coordAlive, coordFaulty, forwards >>

NextNB ==
  \/ SendRequest \/ DetectCoordFault \/ DecideCoord \/ DieCoord
  \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ PreDecideCoord(p)
        \/ PreDecideForward(p) \/ Forward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
        \/ BroadcastCoord(p)

SpecNB == InitNB /\ [][NextNB]_vars
          /\ WF_vars(\E p \in participants : Forward(p))
          /\ WF_vars(\E p \in participants : PreDecideCoord(p))
          /\ WF_vars(\E p \in participants : PreDecideForward(p))
          /\ WF_vars(\E p \in participants : Decide(p))
          /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

AC1 == ~(\E p \in participants : decision[p] = commit /\ decision[p] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) =>
         (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordFaulty)
AC4 == \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====