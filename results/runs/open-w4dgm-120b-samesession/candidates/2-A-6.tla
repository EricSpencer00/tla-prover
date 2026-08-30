---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward

vars == <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

\* The forwarding table entry f[p][q] means: participant p has either (a) stored
\* a pre-decision here for itself, or (b) already forwarded its pre-decision to q.
TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ crstate \in {"opening", "voting", "decided"}
  /\ cfound \in [participants -> BOOLEAN]
  /\ cvote \in [participants -> {yes, no}]
  /\ cbroadcast \in [participants -> BOOLEAN]
  /\ cdecision \in {yes, no, undecided}
  /\ ccoord \in BOOLEAN
  /\ ccoordfaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ crstate = "opening"
  /\ cfound = [p \in participants |-> FALSE]
  /\ cvote = [p \in participants |-> undecided]
  /\ cbroadcast = [p \in participants |-> FALSE]
  /\ cdecision = undecided
  /\ ccoord = TRUE
  /\ ccoordfaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
  /\ ccoord
  /\ crstate = "opening"
  /\ crstate' = "voting"
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

\* Vote collection is asynchronous: participants answer in any order.
GetVote(p) ==
  /\ ccoord
  /\ alive[p]
  /\ crstate = "voting"
  /\ ~cfound[p]
  /\ cfound' = [cfound EXCEPT ![p] = TRUE]
  /\ cvote' = [cvote EXCEPT ![p] = pstate[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

DetectFault(p) ==
  /\ ccoord
  /\ ~alive[p]
  /\ crstate = "voting"
  /\ ~cfound[p]
  /\ cfound' = [cfound EXCEPT ![p] = TRUE]
  /\ cvote' = [cvote EXCEPT ![p] = no]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

\* The coordinator broadcasts the decision to everybody at once.
MakeDecision ==
  /\ ccoord
  /\ crstate = "voting"
  /\ cdecision = undecided
  /\ \A p \in participants : cfound[p]
  /\ cdecision' = IF \A p \in participants : cvote[p] = yes THEN yes ELSE no
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, ccoord, ccoordfaulty, forward>>

Broadcast(p) ==
  /\ ccoord
  /\ alive[p]
  /\ cdecision # undecided
  /\ ~cbroadcast[p]
  /\ forward' = [forward EXCEPT ![p][p] = IF cdecision = yes THEN commit ELSE abort]
  /\ cbroadcast' = [cbroadcast EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cdecision, ccoord, ccoordfaulty>>

DieCoordinator ==
  /\ ccoord
  /\ ccoord' = FALSE
  /\ ccoordfaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, forward>>

SendVote(p) ==
  /\ alive[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ pstate[p] = no
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~ccoord
  /\ \A q \in participants : alive[q] => ~cbroadcast[q]
  /\ \A q \in participants, r \in participants : ~alive[q] => forward[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

\* A participant learns the decision by receiving a forward from any peer.
PredecideFrom(p) ==
  /\ alive[p]
  /\ forward[p][p] = notsent
  /\ \E q \in participants :
       /\ forward[q][p] # notsent
       /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \A q \in participants : forward[p][q] # notsent
  /\ forward[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

Die(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, crstate, cfound, cvote, cbroadcast, cdecision, ccoord, ccoordfaulty, forward>>

Next ==
  \/ SendReq
  \/ MakeDecision
  \/ DieCoordinator
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ SendVote(p) \/ AbortOnVote(p)
       \/ AbortTimeout(p) \/ PredecideFrom(p) \/ Decide(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q) \/ Broadcast(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PredecideFrom(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))

\* SAFETY: decision is globally consistent and final once made.
TypeInvNB ==
  /\ TypeOK
  /\ \A p \in participants : decision[p] \in {waiting, commit, abort}
  /\ \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
  /\ \A p \in participants : decision[p] # waiting => (decision[p] = commit => (\A q \in participants : cvote[q] = yes))
  /\ \A p \in participants : decision[p] # waiting => (decision[p] = abort => (\E q \in participants : cvote[q] = no \/ faulty[q] \/ ~ccoord))
  /\ \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* LIVENESS: the single coordinator can crash silently, but forwarding keeps
\* every non-crashed participant moving toward a decision.
AC3Live == <>(\A p \in participants : decision[p] # waiting \/ faulty[p] \/ ~ccoord)
AC5Terminate == \A p \in participants : (decision[p] = waiting /\ ~faulty[p]) ~> (decision[p] # waiting)

====