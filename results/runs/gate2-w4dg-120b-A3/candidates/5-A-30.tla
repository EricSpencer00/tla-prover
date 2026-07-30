---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  A single
\* coordinator collects votes from participants, decides commit/abort,
\* and broadcasts the decision.  The broadcast is simple (sequential),
\* so a coordinator crash during broadcast is a real blocking case.
\* Both the coordinator and participants can crash (die).

\* The constant set participants is declared in the .cfg file (not here);
\* all other identifiers are declared below.
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordReqSent,
         coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent, coordReqSent,
          coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ coordReqSent \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ coordReqSent = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions
SendRequest(p) ==
  /\ coordAlive
  /\ ~coordReqSent[p]
  /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqSent[p]
  /\ coordVote[p] = waiting
  /\ sent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReqSent,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReqSent[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReqSent,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Participant actions
SendVote(p) ==
  /\ alive[p]
  /\ coordReqSent[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReqSent[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AdoptDecision(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, coordReqSent,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
                               \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                               \/ AbortOnTimeout(p) \/ AdoptDecision(p) \/ PartDie(p)
  \/ MakeDecision \/ CoordDie

Spec == Init /\ [][Next]_vars
        /\ \A p \in participants :
             WF_vars(SendVote(p)) /\ WF_vars(AbortOnVote(p)) /\ WF_vars(AdoptDecision(p))

\* No two participants decide differently: commit and abort are mutually exclusive.
AC1 == \A i, j \in participants :
         ~ (decision[i] = commit /\ decision[j] = abort)

\* Commit only if all participants voted yes.
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Abort only if some no vote or some fault exists somewhere.
AC3 == \A p \in participants :
         decision[p] = abort =>
           \/ \E q \in participants : vote[q] = no
           \/ \E q \in participants : faulty[q]
           \/ coordFaulty

\* Each participant decides at most once: a commit commits forever, an abort aborts forever.
AC4 == \A p \in participants :
         /\ (decision[p] = commit => \A q \in participants : decision[q] # abort)
         /\ (decision[p] = abort => \A q \in participants : decision[q] # commit)

\* Progress: either everybody decides, or some fault is present.
AC5 ==
  <>(\A p \in participants : decision[p] # undecided) \/
      (\E p \in participants : faulty[p]) \/
      coordFaulty

====