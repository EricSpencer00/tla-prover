---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Votes sent from participants to the coordinator travel over an unreliable
\* channel and may arrive in any order, so the coordinator may pick them up
\* in a different order than they were sent.
VARIABLES vote, alive, decision, faulty, sent, requested, got, broadcast

vars == <<vote, alive, decision, faulty, sent, requested, got, broadcast>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ requested \in [participants -> BOOLEAN]
    /\ got \in [participants -> {yes, no, waiting}]
    /\ broadcast \in [participants -> {commit, abort, notsent}]

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ requested = [p \in participants |-> FALSE]
    /\ got = [p \in participants |-> waiting]
    /\ broadcast = [p \in participants |-> notsent]

SendVoteRequest(p) ==
    /\ alive["coord"]
    /\ ~requested[p]
    /\ requested' = [requested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, got, broadcast>>

ReceiveVote(p) ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ requested[p]
    /\ got[p] = waiting
    /\ sent[p]
    /\ got' = [got EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested, broadcast>>

DetectFault(p) ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ requested[p]
    /\ got[p] = waiting
    /\ ~alive[p]
    /\ decision' = [decision EXCEPT !["coord"] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, requested, got, broadcast>>

MakeDecision ==
    /\ alive["coord"]
    /\ decision["coord"] = undecided
    /\ \A p \in participants : got[p] # waiting
    /\ decision' = [decision EXCEPT !["coord"] =
                      IF \A p \in participants : got[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, requested, got, broadcast>>

BroadcastDecision(p) ==
    /\ alive["coord"]
    /\ decision["coord"] \in {commit, abort}
    /\ broadcast[p] = notsent
    /\ broadcast' = [broadcast EXCEPT ![p] = decision["coord"]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested, got>>

CoordDie ==
    /\ alive["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, requested, got, broadcast>>

SendVote(p) ==
    /\ alive[p]
    /\ requested[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, requested, got, broadcast>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, requested, got, broadcast>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~alive["coord"]
    /\ ~requested[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, requested, got, broadcast>>

DecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcast[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, requested, got, broadcast>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, requested, got, broadcast>>

Next ==
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants :
        \/ SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
        \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p)
        \/ PartDie(p)

\* The fairness assumptions cover every progress-capable action EXCEPT death,
\* which is allowed to happen silently and without justification.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ TRUE
    /\ TRUE
    /\ WF_vars(\E p \in participants : SendVoteRequest(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : DetectFault(p))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))
    /\ SF_vars(\E p \in participants : SendVote(p))
    /\ SF_vars(\E p \in participants : AbortOnVote(p))
    /\ SF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ SF_vars(\E p \in participants : DecideFromBroadcast(p))

\* SAFETY PROPERTY: Agreement -- no two participants ever decide differently.
Consistency ==
    ~( \E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort )

\* SAFETY PROPERTY: Commit only with unanimous yes votes.
CommitValidity ==
    \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* SAFETY PROPERTY: Abort only when at least one no vote or a crash explains it.
AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faulty[q]
            \/ faulty["coord"]

\* SAFETY PROPERTY: Irreversibility -- decisions are final.
Irreversibility ==
    \A p \in participants :
        /\ (decision[p] = commit => (decision' [p] = commit))
        /\ (decision[p] = abort => (decision' [p] = abort))

\* LIVENESS PROPERTY: The run eventually resolves or crashes.
Resolution ==
    <>( \A p \in participants : decision[p] \in {commit, abort} \/ faulty[p] \/ faulty["coord"] )

====