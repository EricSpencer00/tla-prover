---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP with Simple Broadcast (ACP-SB): messages are sent one at a time, so a
\* coordinator crash mid-broadcast can leave participants undecided.
\* Both coordinator and participants can crash silently; the fault model is
\* exactly what prevents an action rather than what enables it.

VARIABLES vote, alive, decision, faulty, sent,
          coordRequested, coordVote, coordSent, coordDecision, coordAlive

vars == << vote, alive, decision, faulty, sent,
            coordRequested, coordVote, coordSent, coordDecision, coordAlive >>

TypeOK ==
  /\ vote \in [ participants -> { yes, no } ]
  /\ alive \in [ participants -> BOOLEAN ]
  /\ decision \in [ participants -> { undecided, commit, abort } ]
  /\ faulty \in [ participants -> BOOLEAN ]
  /\ sent \subseteq participants
  /\ coordRequested \in [ participants -> BOOLEAN ]
  /\ coordVote \in [ participants -> { yes, no, waiting } ]
  /\ coordSent \in [ participants -> { sent, notsent } ]
  /\ coordDecision \in { commit, abort, undecided }
  /\ coordAlive \in BOOLEAN

Init ==
  /\ vote \in [ participants -> { yes, no } ]
  /\ alive = [ p \in participants |-> TRUE ]
  /\ decision = [ p \in participants |-> undecided ]
  /\ faulty = [ p \in participants |-> FALSE ]
  /\ sent = {}
  /\ coordRequested = [ p \in participants |-> FALSE ]
  /\ coordVote = [ p \in participants |-> waiting ]
  /\ coordSent = [ p \in participants |-> notsent ]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE

\* Coordinator actions -----------------------------------------------------

CoordRequestVote(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [ coordRequested EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, alive, decision, faulty, sent,
                  coordVote, coordSent, coordDecision, coordAlive >>

CoordReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ p \in sent
  /\ coordVote' = [ coordVote EXCEPT ![p] = vote[p] ]
  /\ UNCHANGED << vote, alive, decision, faulty, sent,
                  coordRequested, coordSent, coordDecision, coordAlive >>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED << vote, alive, decision, faulty, sent,
                  coordRequested, coordVote, coordSent, coordAlive >>

CoordDecide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRequested[p]
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' =
       IF \A p \in participants : coordVote[p] = yes
       THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, sent,
                  coordRequested, coordVote, coordSent, coordAlive >>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [ coordSent EXCEPT ![p] = sent ]
  /\ UNCHANGED << vote, alive, decision, faulty, sent,
                  coordRequested, coordVote, coordDecision, coordAlive >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ faulty' = [ faulty EXCEPT ![ "coordinator" ] = TRUE ]
  /\ UNCHANGED << vote, alive, decision, sent,
                  coordRequested, coordVote, coordSent, coordDecision >>

\* Participant actions -----------------------------------------------------

PVote(p) ==
  /\ alive[p]
  /\ ~decision[p]
  /\ coordRequested[p]
  /\ sent' = sent \cup { p }
  /\ UNCHANGED << vote, alive, decision, faulty, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive >>

PAbortOnVote(p) ==
  /\ alive[p]
  /\ ~decision[p]
  /\ p \in sent
  /\ vote[p] = no
  /\ decision' = [ decision EXCEPT ![p] = abort ]
  /\ UNCHANGED << vote, alive, sent, faulty,
                  coordRequested, coordVote, coordSent, coordDecision, coordAlive >>

PAbortOnTimeout(p) ==
  /\ alive[p]
  /\ ~decision[p]
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [ decision EXCEPT ![p] = abort ]
  /\ UNCHANGED << vote, alive, sent, faulty,
                  coordRequested, coordVote, coordSent, coordDecision, coordAlive >>

PDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ ~decision[p]
  /\ coordSent[p] = sent
  /\ decision' = [ decision EXCEPT ![p] = coordDecision ]
  /\ UNCHANGED << vote, alive, sent, faulty,
                  coordRequested, coordVote, coordSent, coordDecision, coordAlive >>

PDie(p) ==
  /\ alive[p]
  /\ alive' = [ alive EXCEPT ![p] = FALSE ]
  /\ faulty' = [ faulty EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << vote, decision, sent,
                  coordRequested, coordVote, coordSent, coordDecision, coordAlive >>

Next ==
  \/ \E p \in participants : CoordRequestVote(p)
  \/ \E p \in participants : CoordReceiveVote(p)
  \/ \E p \in participants : CoordDetectFault(p)
  \/ CoordDecide
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants : PVote(p)
  \/ \E p \in participants : PAbortOnVote(p)
  \/ \E p \in participants : PAbortOnTimeout(p)
  \/ \E p \in participants : PDecideFromCoordinator(p)
  \/ \E p \in participants : PDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PVote(p))
  /\ WF_vars(\E p \in participants : PAbortOnVote(p))
  /\ WF_vars(\E p \in participants : PAbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : PDecideFromCoordinator(p))

\* Safety: No two participants disagree about the transaction outcome.
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValid ==
  \A p \in participants :
    decision[p] = abort =>
      \/ (\E q \in participants : vote[q] = no)
      \/ (\E q \in participants : ~alive[q])
      \/ ~coordAlive

Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit => [ decision EXCEPT ![p] = commit ] = decision)
    /\ (decision[p] = abort => [ decision EXCEPT ![p] = abort ] = decision)

\* Liveness: not guaranteed under simple broadcast, but at least some fault is
\* eventually evident whenever participants cannot all decide.
EventuallyDecideOrFail ==
  <> ( \A p \in participants : decision[p] # undecided
       \/ \E p \in participants : ~alive[p]
       \/ ~coordAlive )

Properties == Agreement /\ CommitValid /\ AbortValid /\ Irreversible

====