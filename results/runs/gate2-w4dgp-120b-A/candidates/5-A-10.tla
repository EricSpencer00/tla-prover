---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AllVoted == \A p \in participants : coordVote[p] # waiting
AllSent == \A p \in participants : coordSent[p] # notsent

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ sent \subseteq participants
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sent = {}
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions ---------------------------------------------------------

SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ p \in sent
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequested, coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ AllVoted
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequested, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordRequested, coordVote, coordSent, coordDecision>>

CoordProgress == SendRequest(any) \/ ReceiveVote(any) \/ DetectFault(any) \/ MakeDecision \/ Broadcast(any)

\* Participant actions ---------------------------------------------------------

SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in sent
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sent, coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

PartProgress == SendVote(any) \/ AbortOnVote(any) \/ AbortTimeout(any) \/ DecideOnBroadcast(any)

Next ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p) \/ AbortTimeout(p) \/ DecideOnBroadcast(p) \/ PartDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ WF_vars(PartProgress)

\* Safety properties -------------------------------------------------------------

\* No two participants decide differently: a commit and an abort never coexist.
AC1 == ~(\E p \in participants, q \in participants : decision[p] = commit /\ decision[q] = abort)

\* A commit is only possible if every participant voted yes.
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort happens only when justified: at least one no vote, or at least one crash.
AC3 ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : q \in faulty
    \/ coordFaulty

\* A participant decides at most once, and never flips its irreversible decision.
AC4 ==
  \A p \in participants :
    /\ (decision[p] = commit => [][decision[p] = commit]_(vars))
    /\ (decision[p] = abort => [][decision[p] = abort]_(vars))

\* Progress: either every participant decides or a crash has occurred.
\* (A non-faulty participant reaching a decision is NOT guaranteed here -- the
\* simple broadcast variant can leave undecided participants after a crash.)
AC5 ==
  <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ coordFaulty)

====