---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

AllRecvd == \A p \in participants : Recv[p] # waiting
AllBroadcast == \A p \in participants : Send[p] # notsent

VARIABLES Vote, Alive, Decision, Faulty, Sent, CoordStep, Recv, Send

vars == <<Vote, Alive, Decision, Faulty, Sent, CoordStep, Recv, Send>>

TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ Decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
    /\ Faulty \subseteq (participants \cup {"coord"})
    /\ Sent \subseteq participants
    /\ CoordStep \in [participants -> {waiting, notsent}]
    /\ Recv \in [participants -> {waiting, commit, abort}]
    /\ Send \subseteq participants

Init ==
    /\ Vote \in [participants -> {yes, no}]
    /\ Alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ Decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
    /\ Faulty = {}
    /\ Sent = {}
    /\ CoordStep = [p \in participants |-> waiting]
    /\ Recv = [p \in participants |-> waiting]
    /\ Send = {}

SendReq(p) ==
    /\ "coord" \in participants
    /\ "coord" \in Domain(Alive)
    /\ Alive["coord"]
    /\ CoordStep[p] = waiting
    /\ CoordStep' = [CoordStep EXCEPT ![p] = notsent]
    /\ UNCHANGED <<Vote, Alive, Decision, Faulty, Sent, Recv, Send>>

RecvVote(p) ==
    /\ Alive["coord"]
    /\ Decision["coord"] = undecided
    /\ CoordStep[p] # waiting
    /\ Recv[p] = waiting
    /\ p \in Sent
    /\ Recv' = [Recv EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED <<Vote, Alive, Decision, Faulty, Sent, CoordStep, Send>>

DetectFault(p) ==
    /\ Alive["coord"]
    /\ Decision["coord"] = undecided
    /\ CoordStep[p] # waiting
    /\ Recv[p] = waiting
    /\ ~Alive[p]
    /\ Decision' = [Decision EXCEPT !["coord"] = abort]
    /\ UNCHANGED <<Vote, Alive, Faulty, Sent, CoordStep, Recv, Send>>

MakeDecision ==
    /\ Alive["coord"]
    /\ Decision["coord"] = undecided
    /\ AllRecvd
    /\ Decision' = [Decision EXCEPT !["coord"] =
                     IF \A p \in participants : Recv[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<Vote, Alive, Faulty, Sent, CoordStep, Recv, Send>>

BroadcastDecision(p) ==
    /\ Alive["coord"]
    /\ Decision["coord"] \in {commit, abort}
    /\ p \notin Send
    /\ Send' = Send \cup {p}
    /\ UNCHANGED <<Vote, Alive, Decision, Faulty, Sent, CoordStep, Recv>>

CoordDie ==
    /\ "coord" \in Domain(Alive)
    /\ Alive["coord"]
    /\ Alive' = [Alive EXCEPT !["coord"] = FALSE]
    /\ Faulty' = Faulty \cup {"coord"}
    /\ UNCHANGED <<Vote, Decision, Sent, CoordStep, Recv, Send>>

SendVote(p) ==
    /\ Alive[p]
    /\ CoordStep[p] # waiting
    /\ p \notin Sent
    /\ Sent' = Sent \cup {p}
    /\ UNCHANGED <<Vote, Alive, Decision, Faulty, CoordStep, Recv, Send>>

AbortOnVote(p) ==
    /\ Alive[p]
    /\ Decision[p] = undecided
    /\ p \in Sent
    /\ Vote[p] = no
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<Vote, Alive, Faulty, Sent, CoordStep, Recv, Send>>

AbortOnTimeout(p) ==
    /\ Alive[p]
    /\ Decision[p] = undecided
    /\ ~Alive["coord"]
    /\ CoordStep[p] = waiting
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<Vote, Alive, Faulty, Sent, CoordStep, Recv, Send>>

DecideFromCoord(p) ==
    /\ Alive[p]
    /\ Decision[p] = undecided
    /\ p \in Send
    /\ Decision' = [Decision EXCEPT ![p] = Decision["coord"]]
    /\ UNCHANGED <<Vote, Alive, Faulty, Sent, CoordStep, Recv, Send>>

Die(p) ==
    /\ Alive[p]
    /\ Alive' = [Alive EXCEPT ![p] = FALSE]
    /\ Faulty' = Faulty \cup {p}
    /\ UNCHANGED <<Vote, Decision, Sent, CoordStep, Recv, Send>>

Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromCoord(p)
    \/ \E p \in participants : Die(p)

Spec == Init /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(SendVote(p))
    /\ \A p \in participants : WF_vars(AbortOnVote(p))
    /\ \A p \in participants : WF_vars(DecideFromCoord(p))
    /\ WF_vars(MakeDecision)
    /\ \A p \in participants : WF_vars(Died(p))

AC1 ==
    \A p, q \in participants :
        (Decision[p] = commit /\ Decision[q] = abort) => p = q

AC2 ==
    (\E p \in participants : Decision[p] = commit) =>
        (\A p \in participants : Vote[p] = yes)

AC3 ==
    (\E p \in participants : Decision[p] = abort) =>
        (\E p \in participants : Vote[p] = no) \/ Faulty # {} \/ "coord" \in Faulty

AC4 ==
    /\ \A p \in participants : (Decision[p] = commit) ~> (Decision[p] = commit)
    /\ \A p \in participants : (Decision[p] = abort) ~> (Decision[p] = abort)

Liveness ==
    <>(\A p \in participants : Decision[p] # undecided \/ Faulty # {} \/ "coord" \in Faulty)

====