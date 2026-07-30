---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Decision tracks whether a participant has adopted the coordinator's broadcast;
\* Faulty is a permanent marker used for liveness reasoning only.
VARIABLES vote, alive, decision, faulty, sent, reqsent, recv, sentd

vars == <<vote, alive, decision, faulty, sent, reqsent, recv, sentd>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ reqsent \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ sentd \in [participants -> {commit, abort, notsent}]

\* Weak fairness on every progress action except death keeps the system moving.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordSendVoteReq)
    /\ WF_vars(CoordReceiveVote)
    /\ WF_vars(CoordMakeDecision)
    /\ WF_vars(CoordBroadcast)
    /\ WF_vars(PartSendVote)
    /\ WF_vars(PartDecideAbortByVote)
    /\ WF_vars(PartDecideAbortByTimeout)
    /\ WF_vars(PartDecideFromCoord)

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ reqsent = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ sentd = [p \in participants |-> notsent]

CoordSendVoteReq ==
    /\ alive["coord"]
    /\ \E p \in participants :
         /\ ~reqsent[p]
         /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, recv, sentd>>

CoordReceiveVote ==
    /\ alive["coord"]
    /\ \E p \in participants :
         /\ reqsent[p]
         /\ recv[p] = waiting
         /\ sent[p]
         /\ recv' = [recv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, reqsent, sentd>>

\* Immediate failure detection makes this a simple conditional.
CoordDetectFault ==
    /\ alive["coord"]
    /\ \E p \in participants :
         /\ reqsent[p]
         /\ recv[p] = waiting
         /\ ~alive[p]
         /\ decision' = [q \in participants |-> abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqsent, recv, sentd>>

CoordMakeDecision ==
    /\ alive["coord"]
    /\ decision = undecided
    /\ \A p \in participants : recv[p] # waiting
    /\ decision' = [q \in participants |->
                       IF \A p \in participants : recv[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqsent, recv, sentd>>

CoordBroadcast ==
    /\ alive["coord"]
    /\ decision # undecided
    /\ \E p \in participants :
         /\ sentd[p] = notsent
         /\ sentd' = [sentd EXCEPT ![p] = decision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, reqsent, recv>>

CoordDie ==
    /\ alive["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, reqsent, recv, sentd>>

PartSendVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ reqsent[p]
         /\ ~sent[p]
         /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqsent, recv, sentd>>

PartDecideAbortByVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ sent[p]
         /\ vote[p] = no
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqsent, recv, sentd>>

PartDecideAbortByTimeout ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ ~alive["coord"]
         /\ ~reqsent[p]
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqsent, recv, sentd>>

PartDecideFromCoord ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ sentd[p] # notsent
         /\ decision' = [decision EXCEPT ![p] = sentd[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqsent, recv, sentd>>

PartDie ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, reqsent, recv, sentd>>

Next ==
    \/ CoordSendVoteReq
    \/ CoordReceiveVote
    \/ CoordDetectFault
    \/ CoordMakeDecision
    \/ CoordBroadcast
    \/ CoordDie
    \/ PartSendVote
    \/ PartDecideAbortByVote
    \/ PartDecideAbortByTimeout
    \/ PartDecideFromCoord
    \/ PartDie

\* No two participants ever decide differently.
Agreement == ~(\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)

\* Commit only if every participant voted yes.
CommitValid == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* Abort only if someone voted no or some node failed.
AbortValid ==
    (\E p \in participants : decision[p] = abort)
        => (\/ \E p \in participants : vote[p] = no
            \/ \E p \in participants : faulty[p]
            \/ faulty["coord"])

\* A participant decides at most once, and the decision is permanent.
Irreversible ==
    \A p \in participants :
        /\ (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

\* Either everyone decides, or a failure occurs that blocks the protocol.
Termination ==
    <>(\A p \in participants : decision[p] # undecided
        \/ \E p \in participants : faulty[p]
        \/ faulty["coord"])

====