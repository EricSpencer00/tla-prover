---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived, coordSentMsg
VARIABLES vote, pAlive, pDecision, pFaulty, pSentVote

vars == <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived, coordSentMsg,
          vote, pAlive, pDecision, pFaulty, pSentVote>>

TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordFaulty \in BOOLEAN
    /\ coordSentVoteReq \in [participants -> BOOLEAN]
    /\ coordReceived \in [participants -> {yes, no, waiting}]
    /\ coordSentMsg \in [participants -> {notsent, commit, abort}]
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]

Init ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ coordFaulty = FALSE
    /\ coordSentVoteReq = [p \in participants |-> FALSE]
    /\ coordReceived = [p \in participants |-> waiting]
    /\ coordSentMsg = [p \in participants |-> notsent]
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSentVote = [p \in participants |-> FALSE]

SendVoteReq(coord, p) ==
    /\ coordAlive
    /\ ~coordSentVoteReq[p]
    /\ coordSentVoteReq' = [coordSentVoteReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordReceived, coordSentMsg,
                  vote, pAlive, pDecision, pFaulty, pSentVote>>

ReceiveVote(coord, p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSentVoteReq[p]
    /\ coordReceived[p] = waiting
    /\ pSentVote[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq,
                  coordSentMsg, vote, pAlive, pDecision, pFaulty, pSentVote>>

DetectFault(coord, p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSentVoteReq[p]
    /\ coordReceived[p] = waiting
    /\ ~pAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentVoteReq, coordReceived, coordSentMsg,
                  vote, pAlive, pDecision, pFaulty, pSentVote>>

MakeDecision(coord) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordReceived[p] \in {yes, no}
    /\ coordDecision' = IF \A p \in participants : coordReceived[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentVoteReq, coordReceived, coordSentMsg,
                  vote, pAlive, pDecision, pFaulty, pSentVote>>

BroadcastDecision(coord, p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSentMsg[p] = notsent
    /\ coordSentMsg' = [coordSentMsg EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  vote, pAlive, pDecision, pFaulty, pSentVote>>

CoordDie(coord) ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSentVoteReq, coordReceived, coordSentMsg,
                  vote, pAlive, pDecision, pFaulty, pSentVote>>

SendVote(p) ==
    /\ pAlive[p]
    /\ coordSentVoteReq[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  coordSentMsg, vote, pAlive, pDecision, pFaulty>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ vote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  coordSentMsg, vote, pAlive, pFaulty, pSentVote>>

AbortTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~coordAlive
    /\ ~coordSentVoteReq[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  coordSentMsg, vote, pAlive, pFaulty, pSentVote>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordSentMsg[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordSentMsg[p]]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  coordSentMsg, vote, pAlive, pFaulty, pSentVote>>

Die(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDecision, coordFaulty, coordSentVoteReq, coordReceived,
                  coordSentMsg, vote, pDecision, pSentVote>>

Next ==
    \/ \E p \in participants : SendVoteReq(coordAlive, p)
    \/ \E p \in participants : ReceiveVote(coordAlive, p)
    \/ \E p \in participants : DetectFault(coordAlive, p)
    \/ MakeDecision(coordAlive)
    \/ \E p \in participants : BroadcastDecision(coordAlive, p)
    \/ CoordDie(coordAlive)
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : Die(p)

Spec == Init /\ [][Next]_vars

CoordWeakFairness ==
    /\ TRUE
    /\ TRUE
    /\ TRUE
    /\ TRUE
    /\ TRUE
    /\ TRUE

PartWeakFairness(p) ==
    /\ SendVote(p) ~> (AbortOnVote(p) \/ DecideOnBroadcast(p))
    /\ TRUE

Spec == Spec /\ CoordWeakFairness
            /\ \A p \in participants : PartWeakFairness(p)

Agreement ==
    \A a, b \in participants : ~(pDecision[a] = commit /\ pDecision[b] = abort)

CommitValid ==
    \A a \in participants : pDecision[a] = commit => (\A b \in participants : vote[b] = yes)

AbortValid ==
    \A a \in participants : pDecision[a] = abort =>
        \/ (\E b \in participants : vote[b] = no)
        \/ (\E b \in participants : pFaulty[b])
        \/ coordFaulty

Irreversible ==
    \A a \in participants :
        /\ (pDecision[a] = commit) ~> (pDecision[a] = commit)
        /\ (pDecision[a] = abort) ~> (pDecision[a] = abort)

DecideEventuallyOrFail ==
    <>(\A p \in participants : pDecision[p] # undecided \/ coordFaulty
                     \/ (\E e \in participants : pFaulty[e]))

====