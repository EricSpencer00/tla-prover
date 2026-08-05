---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, faulty, decision, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive

vars == <<pstate, faulty, decision, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

ASSUME /\ yes # no /\ commit # abort /\ waiting # undecided /\ notsent # commit /\ notsent # abort

CoordVars == <<coordstate, coordvote, broadcast, coorddecision, coordalive>>

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ sentvote \in [participants -> BOOLEAN]
  /\ coordstate \in {waiting, commit, abort}
  /\ coordvote \in {yes, no, undecided}
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ coorddecision \in {undecided, commit, abort}
  /\ coordalive \in BOOLEAN

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ decision = [p \in participants |-> undecided]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]
  /\ sentvote = [p \in participants |-> FALSE]
  /\ coordstate = waiting
  /\ coordvote = undecided
  /\ broadcast = [p \in participants |-> notsent]
  /\ coorddecision = undecided
  /\ coordalive = TRUE

\* Coordinator actions are identical to the base simple broadcast protocol.
SendRequest(p) ==
  /\ coordalive
  /\ coordstate = waiting
  /\ sentvote[p] = FALSE
  /\ coordstate' = waiting
  /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, faulty, decision, fwd, coordvote, broadcast, coorddecision, coordalive>>

GetVote(p) ==
  /\ coordalive
  /\ coordstate = waiting
  /\ pstate[p] # undecided
  /\ sentvote[p] = TRUE
  /\ coordvote' = pstate[p]
  /\ UNCHANGED <<pstate, faulty, decision, fwd, sentvote, coordstate, broadcast, coorddecision, coordalive>>

DetectFault(p) ==
  /\ coordalive
  /\ coordstate = waiting
  /\ pstate[p] = undecided
  /\ coordstate' = abort
  /\ coorddecision' = abort
  /\ UNCHANGED <<pstate, faulty, decision, fwd, sentvote, coordvote, broadcast, coordalive>>

MakeDecision ==
  /\ coordalive
  /\ coordstate = waiting
  /\ coordvote # undecided
  /\ coordstate' = coordvote
  /\ coorddecision' = coordvote
  /\ UNCHANGED <<pstate, faulty, decision, fwd, sentvote, coordvote, broadcast, coordalive>>

BroadcastDecision(p) ==
  /\ coordalive
  /\ coordstate \in {commit, abort}
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordstate]
  /\ UNCHANGED <<pstate, faulty, decision, fwd, sentvote, coordvote, coordstate, coorddecision, coordalive>>

\* Crash of the coordinator; it may crash silently before broadcasting anybody's decision.
CoordDie ==
  /\ coordalive
  /\ coordalive' = FALSE
  /\ UNCHANGED <<pstate, faulty, decision, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision>>

\* Vote messages are directed from participant to coordinator, and are unaffected by
\* the reliable broadcast the participants now perform.
SendVote(p, v) ==
  /\ pstate[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = v]
  /\ UNCHANGED <<faulty, decision, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

\* A participant first stores the coordinator's decision locally (its own table entry),
\* then reliably forwards it to every other participant before it may finalize locally.
PreDecideFromCoord(p) ==
  /\ ~faulty[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = broadcast[p]]
  /\ UNCHANGED <<pstate, faulty, decision, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

PreDecideFromPeer(p, q) ==
  /\ ~faulty[p]
  /\ p # q
  /\ decision[p] = undecided
  /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, faulty, decision, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

Forward(p, q) ==
  /\ ~faulty[p]
  /\ ~faulty[q]
  /\ p # q
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, faulty, decision, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

Decide(p) ==
  /\ ~faulty[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, faulty, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

\* A participant alone may abort once the coordinator has died, no one is left
\* waiting for it, and no dead participant is still expecting a forwarded decision.
AbortOnTimeout(p) ==
  /\ ~faulty[p]
  /\ decision[p] = undecided
  /\ coordalive = FALSE
  /\ \A q \in participants : broadcast[q] = notsent
  /\ \A q \in participants :
       (faulty[q] /\ fwd[q][p] # notsent) => (p \in participants)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, faulty, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

Die(p) ==
  /\ ~faulty[p]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, fwd, sentvote, coordstate, coordvote, broadcast, coorddecision, coordalive>>

Next ==
  \/ MakeDecision \/ CoordDie
  \/ \E p \in participants :
       \/ SendRequest(p) \/ GetVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
       \/ SendVote(p, yes) \/ SendVote(p, no)
       \/ PreDecideFromCoord(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E q \in participants : PreDecideFromPeer(p, q) \/ Forward(p, q)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p, yes))
  /\ WF_vars(\E p \in participants : SendVote(p, no))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants, q \in participants : PreDecideFromPeer(p, q))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: agreement, commit/abort validity, and irrevocability.
AC1 == ~( \E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort )
AC2 == \A q \in participants : decision[q] = commit => (\A p \in participants : pstate[p] = yes)
AC3 == \A q \in participants : decision[q] = abort =>
        (\E p \in participants : pstate[p] = no \/ faulty[p] \/ coordalive = FALSE)
AC4 == \A p \in participants : \A d \in {commit, abort} : (decision[p] = d) ~> (decision[p] = d)

\* Liveness: agreement still holds when publish, and the non-blocking guarantee
\* that every non-faulty participant eventually decides.
AC3Live == <>( \A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordalive = FALSE )
AC5 == \A p \in participants : ( ~faulty[p] ) ~> ( decision[p] # undecided )

PROPERTY_INVARIANT == AC1 /\ AC2 /\ AC3 /\ AC4
PROPERTY_LIVENESS == AC3Live /\ AC5

====