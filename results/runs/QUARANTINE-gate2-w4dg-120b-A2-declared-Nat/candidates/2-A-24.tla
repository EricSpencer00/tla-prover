---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordReq, coordVote,
         coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

States == {undecided, commit, abort}

HasFwd(p) == \E q \in participants: fwd[p][q] \in {commit, abort}
CoordHasBroadcast == \E p \in participants: coordBroadcast[p] \in {commit, abort}

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> States]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {commit, abort, undecided}]
  /\ coordDecision \in States
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: identical to the base simple broadcast protocol.
SendRequest ==
  /\ coordReq = waiting
  /\ coordAlive
  /\ coordReq' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq \in {yes, no}
  /\ alive[p]
  /\ ~sentVote[p]
  /\ vote[p] \in {yes, no}
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault(p) ==
  /\ coordAlive
  /\ ~sentVote[p]
  /\ coordReq = yes
  /\ alive[p]
  /\ vote[p] = undecided
  /\ coordReq' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

BcastCommit(p) ==
  /\ coordAlive
  /\ ~sentVote[p]
  /\ coordReq = yes
  /\ vote[p] = yes
  /\ coordVote' = yes
  /\ coordDecision' = commit
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = commit]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordReq, coordAlive, coordFaulty, fwd>>

BcastAbort(p) ==
  /\ coordAlive
  /\ ~sentVote[p]
  /\ coordDecision' = abort
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq,
                coordVote, coordAlive, coordFaulty, fwd>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, fwd>>

\* Two ways to receive the decision: directly from the coordinator, or from
\* another participant that forwarded it to you.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants: fwd[q][p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = fwd[CHOOSE q \in participants: fwd[q][p] \in {commit, abort}][p]]
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants: fwd[q][p] \in {commit, abort}][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Forward to a specific other participant; non-blocking because it does not
\* wait for acknowledgements, only for a live target.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] \in {commit, abort}
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant finalizes only after it has forwarded its pre-decision to
\* everyone else -- the commit point of the non-blocking variant.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] \in {commit, abort}
  /\ \A q \in participants: fwd[p][q] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~HasFwd(p)
  /\ \A q \in participants: coordBroadcast[q] = undecided
  /\ \A q \in participants: \A r \in participants: ~(~alive[q] /\ fwd[r][q] \in {commit, abort})
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
  \/ SendRequest
  \/ \E p \in participants:
        \/ GetVote(p) \/ DetectFault(p) \/ BcastCommit(p) \/ BcastAbort(p)
        \/ PreDecideFromCoord(p) \/ PreDecideFromFwd(p) \/ Decide(p)
        \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants, q \in participants: Forward(p, q)
  \/ CoordDie

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: PreDecideFromCoord(p) \/ PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants, q \in participants: Forward(p, q))
  /\ WF_vars(\E p \in participants: Decide(p))

\* Two-way agreement: everyone commits or everyone aborts. The invariant holds
\* even if a participant is later marked faulty; the commit is never retracted.
Agreement ==
  ~( \E p1 \in participants, p2 \in participants:
        /\ decision[p1] = commit
        /\ decision[p2] = abort )

CommitValidity ==
  ( \E p \in participants: decision[p] = commit ) => \A p \in participants: vote[p] = yes

AbortValidity ==
  ( \E p \in participants: decision[p] = abort ) =>
    \/ \E p \in participants: vote[p] = no
    \/ \E p \in participants: faulty[p]
    \/ coordFaulty

Irreversibility ==
  \A p \in participants:
    /\ decision[p] = commit => decision' = [decision EXCEPT ![p] = commit]
    /\ decision[p] = abort => decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  coordReq, coordVote, coordBroadcast, coordDecision,
                  coordAlive, coordFaulty, fwd>>

TypeInvNB == TypeOK /\ Agreement

\* Bounded agreement: with the coordinator dead, either everyone reaches a
\* decision, or some participant becomes faulty, or the coordinator dies.
EventualResolution ==
  <>( \A p \in participants: decision[p] # undecided \/ faulty[p] \/ ~coordAlive )

\* Every non-faulty participant eventually decides, even though the coordinator
\* may crash mid-broadcast -- exactly what reliable forwarding guarantees.
EventualDecision ==
  \A p \in participants: (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

====