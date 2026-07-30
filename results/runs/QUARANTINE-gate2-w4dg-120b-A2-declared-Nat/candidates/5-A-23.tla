---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES voted, aliveP, decisionP, faultyP, sentVote, asked, coordVote, sentDecision, decisionC, aliveC, faultyC

vars == <<voted, aliveP, decisionP, faultyP, sentVote, asked, coordVote, sentDecision,
           decisionC, aliveC, faultyC>>

Init ==
  /\ \E v \in {yes, no} : voted = [p \in participants |-> v]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decisionP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ asked = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

SendRequest(p) ==
  /\ aliveC
  /\ ~asked[p]
  /\ asked' = [asked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                  coordVote, sentDecision, decisionC, aliveC, faultyC>>

ReceiveVote(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ asked[p]
  /\ coordVote[p] = waiting
  /\ sentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = voted[p]]
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                 asked, sentDecision, decisionC, aliveC, faultyC>>

DetectFault(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ asked[p]
  /\ coordVote[p] = waiting
  /\ ~aliveP[p]
  /\ decisionC' = abort
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                 asked, coordVote, sentDecision, aliveC, faultyC>>

MakeDecision ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ decisionC' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                 asked, coordVote, sentDecision, aliveC, faultyC>>

BroadcastDecision(p) ==
  /\ aliveC
  /\ decisionC # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = decisionC]
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                 asked, coordVote, decisionC, aliveC, faultyC>>

DieCoordinator ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, sentVote,
                 asked, coordVote, sentDecision, decisionC, faultyC>>

SendMyVote(p) ==
  /\ aliveP[p]
  /\ asked[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<voted, aliveP, decisionP, faultyP, asked,
                 coordVote, sentDecision, decisionC, aliveC, faultyC>>

AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentVote[p]
  /\ voted[p] = no
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<voted, aliveP, faultyP, sentVote, asked,
                 coordVote, sentDecision, decisionC, aliveC, faultyC>>

AbortOnTimeout(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ ~asked[p]
  /\ ~aliveC
  /\ decisionP' = [decisionP EXCEPT ![p] = abort]
  /\ UNCHANGED <<voted, aliveP, faultyP, sentVote, asked,
                 coordVote, sentDecision, decisionC, aliveC, faultyC>>

DecideOnBroadcast(p) ==
  /\ aliveP[p]
  /\ decisionP[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decisionP' = [decisionP EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<voted, aliveP, faultyP, sentVote, asked,
                 coordVote, sentDecision, decisionC, aliveC, faultyC>>

DieParticipant(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<voted, decisionP, sentVote, asked, coordVote,
                 sentDecision, decisionC, aliveC, faultyC>>

Next ==
  \E p \in participants :
    \/ SendRequest(p)
    \/ ReceiveVote(p)
    \/ DetectFault(p)
    \/ BroadcastDecision(p)
    \/ SendMyVote(p)
    \/ AbortOnVote(p)
    \/ AbortOnTimeout(p)
    \/ DecideOnBroadcast(p)
    \/ DieParticipant(p)
  \/ MakeDecision
  \/ DieCoordinator

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendMyVote(p))
        /\ WF_vars(\E p \in participants : AbortOnVote(p))
        /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
        /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
        /\ WF_vars(\E p \in participants : SendRequest(p))

TypeInv ==
  /\ voted \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decisionP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ asked \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {waiting, yes, no}]
  /\ sentDecision \in [participants -> {notsent, commit, abort}]
  /\ decisionC \in {undecided, commit, abort}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Agree ==
  \A p, q \in participants :
    (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

CommitValid ==
  \A p \in participants :
    decisionP[p] = commit => (\A q \in participants : voted[q] = yes)

AbortValid ==
  \A p \in participants :
    decisionP[p] = abort => (\E q \in participants : voted[q] = no \/ faultyP[q] \/ faultyC)

Irreversible ==
  \A p \in participants :
    (decisionP[p] = commit => \A s \in [participants -> {undecided, commit, abort}]:
                                 (s[p] = commit => s[p] = commit))
    /\ (decisionP[p] = abort => \A s \in [participants -> {undecided, commit, abort}]:
                                (s[p] = abort => s[p] = abort))

DecideEventually ==
  <>((\A p \in participants : decisionP[p] # undecided) \/ (\E p \in participants : faultyP[p] \/ faultyC))

====