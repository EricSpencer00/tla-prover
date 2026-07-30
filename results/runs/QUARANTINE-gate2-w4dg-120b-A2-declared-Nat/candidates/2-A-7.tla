---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

RECURSIVE AllFrom(_, _)
AllFrom(f, S) == IF S = {} THEN TRUE ELSE (\E x \in S : f[x] /\ AllFrom(f, S \ {x}))

TypeOK == /\ vote \in [participants -> {yes, no, undecided}]
          /\ alive \in [participants -> BOOLEAN]
          /\ decision \in [participants -> {commit, abort, undecided}]
          /\ faulty \in [participants -> BOOLEAN]
          /\ sentVote \in [participants -> BOOLEAN]
          /\ coordReq \in {waiting, yes, no}
          /\ coordVote \in {yes, no, undecided}
          /\ coordBroadcast \in [participants -> {yes, no, notsent}]
          /\ coordDecision \in {commit, abort, undecided}
          /\ coordAlive \in BOOLEAN
          /\ coordFaulty \in BOOLEAN
          /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init == /\ vote = [p \in participants |-> undecided]
        /\ alive = [p \in participants |-> TRUE]
        /\ decision = [p \in participants |-> undecided]
        /\ faulty = [p \in participants |-> FALSE]
        /\ sentVote = [p \in participants |-> FALSE]
        /\ coordReq = waiting
        /\ coordVote = undecided
        /\ coordBroadcast = [p \in participants |-> notsent]
        /\ coordDecision = undecided
        /\ coordAlive = TRUE
        /\ coordFaulty = FALSE
        /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq == /\ coordAlive
           /\ coordReq = waiting
           /\ coordReq' = yes
           /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

SendVote(p) == /\ coordAlive
               /\ alive[p]
               /\ ~sentVote[p]
               /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
               /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
               /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) == /\ alive[p]
                  /\ ~sentVote[p]
                  /\ coordReq # waiting
                  /\ vote' = [vote EXCEPT ![p] = no]
                  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
                  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault == /\ coordAlive
               /\ coordDecision = undecided
               /\ \E p \in participants : vote[p] = no
               /\ coordDecision' = abort
               /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

MakeDecision == /\ coordAlive
                /\ coordDecision = undecided
                /\ coordVote = undecided
                /\ coordReq # waiting
                /\ coordVote' = IF coordReq = yes /\ AllFrom(sentVote, participants) THEN yes ELSE no
                /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Broadcast == /\ coordAlive
             /\ coordDecision = undecided
             /\ coordVote # undecided
             /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
             /\ coordBroadcast' = [p \in participants |-> IF coordVote = yes THEN commit ELSE abort]
             /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, decision, coordAlive, coordFaulty, fwd>>

CoordDie == /\ coordAlive
            /\ coordAlive' = FALSE
            /\ coordFaulty' = TRUE
            /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, fwd>>

PreDecideFromCoordinator(p) == /\ alive[p]
                               /\ decision[p] = undecided
                               /\ coordBroadcast[p] # notsent
                               /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
                               /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
                               /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromForward(p) == /\ alive[p]
                            /\ decision[p] = undecided
                            /\ \E q \in participants : fwd[q][p] # notsent
                            /\ decision' = [decision EXCEPT ![p] = IF \E q \in participants : fwd[q][p] = commit THEN commit ELSE abort]
                            /\ fwd' = [fwd EXCEPT ![p][p] = IF \E q \in participants : fwd[q][p] = commit THEN commit ELSE abort]
                            /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) == /\ alive[p]
                 /\ decision[p] # undecided
                 /\ fwd[p][q] = notsent
                 /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
                 /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) == /\ alive[p]
              /\ decision[p] # undecided
              /\ \A q \in participants : fwd[p][q] # notsent
              /\ decision[p] = decision[p]
              /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) == /\ alive[p]
                      /\ decision[p] = undecided
                      /\ ~coordAlive
                      /\ \A q \in participants : coordBroadcast[q] = notsent
                      /\ \A q \in participants, r \in participants : (faulty[q] /\ fwd[q][r] # notsent) => FALSE
                      /\ decision' = [decision EXCEPT ![p] = abort]
                      /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) == /\ alive[p]
           /\ alive' = [alive EXCEPT ![p] = FALSE]
           /\ faulty' = [faulty EXCEPT ![p] = TRUE]
           /\ UNCHANGED <<vote, decision, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next == \/ SendReq \/ DetectFault \/ MakeDecision \/ Broadcast \/ CoordDie
        \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromCoordinator(p)
                                 \/ PreDecideFromForward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
        \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB == /\ Init
          /\ [][Next]_vars
          /\ WF_vars(\E q \in participants : Forward(coordDecision, q))
          /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
          /\ WF_vars(\E p \in participants : PreDecideFromForward(p))

TypeInvNB == TypeOK

AC1 == ~(\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => ((\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty)
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p]
AC5 == \A p \in participants : decision[p] # undecided

====