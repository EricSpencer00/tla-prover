---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the simple broadcast ACP-SB by adding a per-participant forwarding
\* table: what pre-decision it has received and which peers it has forwarded to.
\* A participant finalizes locally only once it has forwarded to everyone,
\* so a crash of the coordinator cannot permanently block termination.

VARIABLES vote, alive, decision, faulty, voteSent, forwarded

Choices == {"yes", "no"}

TypeInvNB ==
    /\ vote \in [participants -> Choices \cup {undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {waiting, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ \A p \in participants : vote[p] = undecided
    /\ \E p \in participants : vote' = [vote EXCEPT ![p] = "yes"]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, forwarded>>

\* The coordinator collects a yes vote and moves on -- it does not wait for
\* everybody, granting termination progress when messages are slow.
GatherVote ==
    /\ \E p \in participants :
         /\ vote[p] = "yes"
         /\ voteSent[p] = FALSE
         /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, forwarded>>

DetectFault ==
    /\ \A p \in participants : decision[p] = waiting
    /\ \E p \in participants :
         /\ vote[p] = no
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forwarded>>

MakeDecision ==
    /\ \A p \in participants : decision[p] = waiting
    /\ \A p \in participants : vote[p] = "yes"
    /\ \E p \in participants :
         decision' = [decision EXCEPT ![p] = commit]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forwarded>>

\* Broadcast from coordinator: the message sits in the recipient's forwarding
\* table until that recipient actually processes it.
Broadcast ==
    /\ \E p \in participants :
         /\ decision[p] # waiting
         /\ \A q \in participants :
              /\ alive[q]
              /\ forwarded[p][q] = notsent
              /\ forwarded' = [forwarded EXCEPT ![p][q] = decision[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

Die ==
    /\ Cardinality({p \in participants : alive[p]}) > 1
    /\ \E p \in participants :
         /\ alive[p] = TRUE
         /\ faulty[p] = FALSE
         /\ alive' = [alive EXCEPT ![p] = FALSE]
         /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, forwarded>>

PreDecideFromCoordinator ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ forwarded[p][p] = notsent
         /\ \E c \in participants :
              /\ decision[c] # waiting
              /\ forwarded[c][p] # notsent
              /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[c][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

PreDecideFromForward ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ forwarded[p][p] = notsent
         /\ \E q \in participants :
              /\ forwarded[q][p] # notsent
              /\ forwarded[q][p] # notsent
              /\ q # p
              /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

Forward ==
    /\ \E p \in participants, q \in participants :
         /\ p # q
         /\ alive[p]
         /\ forwarded[p][p] # notsent
         /\ forwarded[p][q] = notsent
         /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent>>

Decide ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = waiting
         /\ forwarded[p][p] # notsent
         /\ \A q \in participants : q # p => forwarded[p][q] # notsent
         /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forwarded>>

AbortOnTimeout ==
    /\ \A p \in participants : decision[p] = waiting
    /\ \E p \in participants :
         /\ alive[p]
         /\ (faulty[p] \/ \A q \in participants : decision[q] = waiting)
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, forwarded>>

Next == SendRequest \/ GatherVote \/ DetectFault \/ MakeDecision \/ Broadcast
        \/ Die \/ PreDecideFromCoordinator \/ PreDecideFromForward
        \/ Forward \/ Decide \/ AbortOnTimeout

SpecNB == Init /\ [][Next]_<<vote, alive, decision, faulty, voteSent, forwarded>>

\* Safety: no two participants disagree on the outcome; a commit requires all
\* yes votes, and an abort needs a no vote or a fault.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit)
           => (\A p \in participants : vote[p] = "yes")
AC3 == (\E p \in participants : decision[p] = abort)
           => (\E p \in participants : vote[p] = no \/ faulty[p]) \/ faulty["c"]
AC4 == \A p \in participants : (decision[p] # waiting) ~> (decision[p] # waiting)

\* Liveness: every non-faulty participant eventually decides. Forwarding
\* guarantees this even if the coordinator dies mid-broadcast.
AC5 == \A p \in participants : faulty[p] ~> (decision[p] # waiting)

====