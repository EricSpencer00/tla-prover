---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward

vars == <<vote, alive, decision, faulty, sent, coordRequest, coordVote, coordBroadcast,
           coordDecision, coordAlive, coordFaulty, forward>>

RECURSIVE TableDomain(_)
TableDomain(S) == IF S = {} THEN {}
                  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup TableDomain(S \ {x})

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coordRequest \in {yes, no, waiting}
    /\ coordVote \in [participants -> {yes, no, undecided}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {commit, abort, notsent, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forward \in [participants -> [participants -> {commit, abort, notsent}]]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ coordRequest = waiting
    /\ coordVote = [p \in participants |-> undecided]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordRequest = waiting
    /\ coordAlive
    /\ coordRequest' = yes
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

GetVote(p) ==
    /\ coordRequest # waiting
    /\ coordVote[p] = undecided
    /\ coordAlive
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

DetectFault ==
    /\ coordRequest # waiting
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordVote,
                   coordBroadcast, coordDecision, forward>>

Decide ==
    /\ coordRequest # waiting
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordVote,
                   coordBroadcast, coordAlive, coordFaulty, forward>>

Broadcast ==
    /\ coordDecision # undecided
    /\ coordAlive
    /\ \A p \in participants : coordBroadcast[p] = notsent
    /\ coordBroadcast' = [p \in participants |-> coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordVote,
                   coordDecision, coordAlive, coordFaulty, forward>>

Die == /\ coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
        /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordVote,
                       coordBroadcast, coordDecision, forward>>

SendVote(p) ==
    /\ alive[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordRequest, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortOnVote == /\ ~coordAlive
               /\ \E p \in participants : vote[p] = no
               /\ decision' = [p \in participants |-> abort]
               /\ UNCHANGED <<vote, alive, faulty, sent, coordRequest, coordVote, coordBroadcast,
                              coordDecision, coordAlive, coordFaulty, forward>>

PredecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordRequest, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

PredecideForward(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in participants : forward[q][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = forward[CHOOSE q \in participants : forward[q][p] # notsent][p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordRequest, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

Forward(p, q) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = decision[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequest, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty>>

DecideNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = decision[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordRequest, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

AbortOnTimeout ==
    /\ ~coordAlive
    /\ \A p \in participants : coordBroadcast[p] = notsent
    /\ \A p \in participants : ~faulty[p]
    /\ \A p \in participants : \A q \in participants : forward[p][q] = notsent
    /\ decision' = [p \in participants |-> abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordRequest, coordVote, coordBroadcast,
                   coordDecision, coordAlive, coordFaulty, forward>>

Next ==
    \/ SendRequest \/ DetectFault \/ Decide \/ Broadcast \/ Die \/ AbortOnVote \/ AbortOnTimeout
    \/ \E p \in participants :
           SendVote(p) \/ PredecideCoord(p) \/ PredecideForward(p) \/ DecideNB(p)
           \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : PredecideCoord(p))
    /\ WF_vars(\E p \in participants : PredecideForward(p))
    /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : DecideNB(p))

AC1 == ~(\E p \in participants : decision[p] = commit)
       \/ ~(\E p \in participants : decision[p] = abort)

AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AC3 == (\E p \in participants : decision[p] = abort) =>
          (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
                            => (decision[p] = [q \in participants |-> decision[q]][p])

AC3Liveness == <>(\A p \in participants : decision[p] # undecided \/ \E p \in participants : faulty[p] \/ coordFaulty)

AC5 == \A p \in participants : <>(decision[p] # undecided)

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3Liveness /\ AC5

====