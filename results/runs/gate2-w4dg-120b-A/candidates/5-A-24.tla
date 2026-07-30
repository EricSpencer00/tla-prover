---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator state.
VARIABLES coordAlive, coordFaulty, coordDecision, coordReq, coordVote, coordSent

\* Participant per-id state.
VARIABLES alive, faulty, vote, decision, sentVote

vars == <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
          coordSent, alive, faulty, vote, decision, sentVote>>

Loc == participants \cup {commit, abort, undecided, waiting, notsent}

TypeOK ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in Loc
  /\ coordReq \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> Loc]
  /\ coordSent \in [participants -> Loc]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ vote \in [participants -> {yes, no}]
  /\ decision \in [participants -> Loc]
  /\ sentVote \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordReq = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ vote \in [participants -> {yes, no}]
  /\ decision = [p \in participants |-> undecided]
  /\ sentVote = [p \in participants |-> FALSE]

\* Coordinator actions.
ReqVote(p) ==
  /\ coordAlive
  /\ coordReq[p] = FALSE
  /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVote,
                coordSent, alive, faulty, vote, decision, sentVote>>

Recv(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p] = TRUE
  /\ coordVote[p] = waiting
  /\ sentVote[p] = TRUE
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq,
                coordSent, alive, faulty, vote, decision, sentVote>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p] = TRUE
  /\ coordVote[p] = waiting
  /\ alive[p] = FALSE
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordSent,
                alive, faulty, vote, decision, sentVote>>

Decide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordVote, coordSent,
                alive, faulty, vote, decision, sentVote>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                alive, faulty, vote, decision, sentVote>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordReq, coordVote, coordSent,
                alive, faulty, vote, decision, sentVote>>

\* Participant actions.
SendVote(p) ==
  /\ alive[p]
  /\ coordReq[p]
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                coordSent, alive, faulty, vote, decision>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p] = TRUE
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                coordSent, alive, faulty, vote, sentVote>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ coordReq[p] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                coordSent, alive, faulty, vote, sentVote>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                coordSent, alive, faulty, vote, sentVote>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordReq, coordVote,
                coordSent, vote, decision, sentVote>>

Next ==
  \/ \E p \in participants : ReqVote(p) \/ Recv(p) \/ DetectFault(p)
                         \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
                         \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p)
                         \/ ParticipantDie(p)
  \/ Decide \/ CoordDie

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
  /\ WF_vars(Decide)

\* Safety: no two participants ever decide differently.
Agree ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit is only possible if all participants voted yes.
CommitValid ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort is only possible because someone voted no, or something crashed.
AbortValid ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ coordFaulty

\* A participant decides at most once.
Irreversible ==
  \A p \in participants :
    /\ decision[p] = commit => decision' = [decision EXCEPT ![p] = commit]
    /\ decision[p] = abort => decision' = [decision EXCEPT ![p] = abort]

\* Liveness: either everyone decides or something crashed.
DecideOrCrash ==
  <>(\A p \in participants : decision[p] # undecided) \/ coordFaulty
    \/ \E p \in participants : faulty[p]

====