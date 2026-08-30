---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  Replicated   *)
(* from Babaoglu and Toueg's paper; the coordinator collects votes from  *)
(* participants and then broadcasts its decision one participant at a    *)
(* time, so a coordinator failure mid-broadcast can strand a participant  *)
(* undecided -- a blocking failure.                                      *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sentVote, sentReq,
    recVote, broadcast, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote, sentReq,
          recVote, broadcast, decisionC, aliveC, faultyC>>

Voters == [p \in participants |-> vote[p]]

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ sentReq \in [participants -> BOOLEAN]
    /\ recVote \in [participants -> {yes, no, waiting}]
    /\ broadcast \in [participants -> {waiting, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ \E r \in [participants -> {yes, no}] : vote = r
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ sentReq = [p \in participants |-> FALSE]
    /\ recVote = [p \in participants |-> waiting]
    /\ broadcast = [p \in participants |-> waiting]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* Coordinator actions.
SendReq(p) ==
    /\ aliveC /\ ~sentReq[p]
    /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   recVote, broadcast, decisionC, aliveC, faultyC>>

RecvVote(p) ==
    /\ aliveC /\ decisionC = undecided /\ sentReq[p]
    /\ recVote[p] = waiting /\ sentVote[p]
    /\ recVote' = [recVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   sentReq, broadcast, decisionC, aliveC, faultyC>>

DetectFault(p) ==
    /\ aliveC /\ decisionC = undecided /\ sentReq[p]
    /\ recVote[p] = waiting /\ ~aliveP[p] /\ ~sentVote[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   sentReq, recVote, broadcast, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC /\ decisionC = undecided
    /\ \A p \in participants : sentReq[p]
    /\ (\A p \in participants : recVote[p] # waiting)
    /\ decisionC' = IF \A p \in participants : recVote[p] = yes
                    THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   sentReq, recVote, broadcast, aliveC, faultyC>>

Broadcast(p) ==
    /\ aliveC /\ decisionC # undecided /\ broadcast[p] = waiting
    /\ broadcast' = [broadcast EXCEPT ![p] = notsent]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   sentReq, recVote, decisionC, aliveC, faultyC>>

DieC ==
    /\ aliveC /\ aliveC' = FALSE /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   sentReq, recVote, broadcast, decisionC, aliveC>>

\* Participant actions.
SendVote(p) ==
    /\ aliveP[p] /\ sentReq[p] /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentReq,
                   recVote, broadcast, decisionC, aliveC, faultyC>>

AbortOnVote(p) ==
    /\ aliveP[p] /\ decisionP[p] = undecided
    /\ sentVote[p] /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, sentReq, recVote,
                   broadcast, decisionC, aliveC, faultyC>>

AbortOnTimeout(p) ==
    /\ aliveP[p] /\ decisionP[p] = undecided
    /\ ~aliveC /\ ~sentReq[p]
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, sentReq, recVote,
                   broadcast, decisionC, aliveC, faultyC>>

Decide(p) ==
    /\ aliveP[p] /\ decisionP[p] = undecided
    /\ broadcast[p] = notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote, sentReq, recVote,
                   broadcast, decisionC, aliveC, faultyC>>

DieP(p) ==
    /\ aliveP[p] /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentVote, sentReq, recVote,
                   broadcast, decisionC, aliveC, faultyC>>

Next ==
    \/ \E p \in participants : SendReq(p) \/ RecvVote(p) \/ DetectFault(p)
                               \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                               \/ AbortOnTimeout(p) \/ Decide(p) \/ DieP(p)
    \/ MakeDecision \/ DieC

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendReq(p))
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : DetectFault(p))
    /\ WF_vars(\E p \in participants : Broadcast(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : Decide(p))

(* No two participants ever decide differently.  A decision is           *)
(* unanimous for commit, or abort caused by a no vote or a fault.         *)
NoConflictingDecisions ==
    \A p, q \in participants :
        (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

CommitOnlyOnUnanimous ==
    \A p \in participants : decisionP[p] = commit => \A q \in participants : Voters[q]

AbortOnlyOnVoteOrFault ==
    \A p \in participants :
        decisionP[p] = abort =>
            (\E q \in participants : Voters[q] = no) \/ (\E q \in participants : faultyP[q])
                \/ faultyC

DecideAtMostOnce ==
    \A p \in participants :
        (decisionP[p] = commit => (\A d \in {commit, abort} : decisionP[p] = d))
            /\ (decisionP[p] = abort => (\A d \in {commit, abort} : decisionP[p] = d))

(\* The simple-broadcast variant does NOT guarantee termination:           *)
(\* if the coordinator dies mid-broadcast, some participant can stay       *)
(\* undecided forever.  So the liveness property is the weaker "eventual    *)
(\* decision or fault" property, not "every non-crashed participant decides". *)
DecideOrFault ==
    <>(\A p \in participants : decisionP[p] # undecided \/ faultyP[p] \/ faultyC)

====