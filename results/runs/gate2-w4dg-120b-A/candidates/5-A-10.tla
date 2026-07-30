---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordSend, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordSend, coordDecision, coordAlive, coordFaulty>>

\* The actions that are covered by weak fairness: every live actor that can
\* make progress (vote, decide, abort, broadcast) eventually does.
Actors == participants \cup {"coord"}

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq (participants \cup {"coord"})
  /\ voteSent \subseteq participants
  /\ coordReq \subseteq participants
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSend \in [participants -> {waiting, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \subseteq {"coord"}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = {}
  /\ coordReq = {}
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSend = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = {}

\* Coordinator actions, labelled a1..a6 to ease the fairness spec.
CoordRequest(p) ==
  /\ coordAlive
  /\ p \notin coordReq
  /\ coordReq' = coordReq \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote,
                coordSend, coordDecision, coordAlive, coordFaulty>>

CoordReceive(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq = participants
  /\ coordVote[p] = waiting
  /\ p \in voteSent
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordSend, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq = participants
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ coordFaulty' = {"coord"}
  /\ UNCHANGED <<vote, decision, faulty, voteSent, coordReq, coordVote,
                coordSend, coordAlive>>

CoordMakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                        THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordSend, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSend[p] = notsent
  /\ coordSend' = [coordSend EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = {"coord"}
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordSend, coordDecision, coordAlive>>

\* Participant actions, labelled b1..b5 to ease the fairness spec.
SendVote(p) ==
  /\ alive[p]
  /\ p \in coordReq
  /\ p \notin voteSent
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote,
                coordSend, coordDecision, coordAlive, coordFaulty>>

AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in voteSent
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordSend, coordDecision, coordAlive, coordFaulty>>

AbortOnRequestTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ p \notin coordReq
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ faulty' = faulty \cup {p}
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, voteSent, coordReq, coordVote, coordSend,
                coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSend[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordSend, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, voteSent, coordReq, coordVote, coordSend,
                coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : CoordRequest(p)
  \/ \E p \in participants : CoordReceive(p)
  \/ \E p \in participants : CoordDetectFault(p)
  \/ CoordMakeDecision
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnNo(p)
  \/ \E p \in participants : AbortOnRequestTimeout(p)
  \/ \E p \in participants : DecideOnBroadcast(p)
  \/ \E p \in participants : PartDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Actors : WF_vars(SendVote(p))
  /\ \A p \in Actors : WF_vars(DecideOnBroadcast(p))
  /\ \A p \in Actors : WF_vars(AbortOnNo(p))
  /\ \A p \in Actors : WF_vars(AbortOnRequestTimeout(p))
  /\ \A p \in Actors : WF_vars(CoordRequest(p))
  /\ \A p \in Actors : WF_vars(CoordReceive(p))
  /\ \A p \in Actors : WF_vars(CoordDetectFault(p))
  /\ \A p \in Actors : WF_vars(CoordMakeDecision)
  /\ \A p \in Actors : WF_vars(CoordBroadcast(p))

\* Safety: participants never disagree, and a commit can only follow all-yes.
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : q \in faulty
    \/ coordFaulty # {}

Irrevocability ==
  \A p \in participants :
    /\ (decision[p] = commit => decision' [p] = commit)
    /\ (decision[p] = abort => decision' [p] = abort)

Decide ==
  \/ Agreement
  \/ CommitValid
  \/ AbortValid
  \/ Irrevocability

\* Liveness: either everyone decides, or somebody has crashed.
DecideEventually ==
  <>(\E p \in participants : decision[p] # undecided \/ p \in faulty \/ coordFaulty # {})
====