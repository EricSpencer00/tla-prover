---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  alive, faulty, vote, finalDecision, sentVote, receivedVotes,
  requestSent, coordinatorDecision, decisionSent

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInv ==
  /\ alive \subseteq participants \cup {Coordinator}
  /\ faulty \subseteq participants \cup {Coordinator}
  /\ vote \in [participants -> {yes, no}]
  /\ finalDecision \in [participants -> {undecided, commit, abort}]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ receivedVotes \in [participants -> {waiting} \cup {yes, no}]
  /\ requestSent \in [participants -> BOOLEAN]
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ decisionSent \in [participants -> {notsent} \cup {commit, abort}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ alive = participants \cup {Coordinator}
  /\ faulty = {}
  /\ vote = [p \in participants |-> chOOSE v \in {yes, no} : v]
  /\ finalDecision = [p \in participants |-> undecided]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ receivedVotes = [p \in participants |-> waiting]
  /\ requestSent = [p \in participants |-> FALSE]
  /\ coordinatorDecision = undecided
  /\ decisionSent = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteRequest == \E p \in participants :
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ coordinatorDecision = undecided
  /\ requestSent[p] = FALSE
  /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << alive, faulty, vote, finalDecision, sentVote,
                receivedVotes, coordinatorDecision, decisionSent >>

ReceiveVote(p) == \E v \in {yes, no} :
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ coordinatorDecision = undecided
  /\ requestSent[p] = TRUE
  /\ receivedVotes[p] = waiting
  /\ sentVote[p] = TRUE
  /\ receivedVotes' = [receivedVotes EXCEPT ![p] = v]
  /\ UNCHANGED << alive, faulty, vote, finalDecision, sentVote,
                requestSent, coordinatorDecision, decisionSent >>

DetectFault(p) == 
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ coordinatorDecision = undecided
  /\ requestSent[p] = TRUE
  /\ receivedVotes[p] = waiting
  /\ faulty = faulty \cup {p}
  /\ coordinatorDecision' = abort
  /\ UNCHANGED << alive, vote, finalDecision, sentVote,
                requestSent, receivedVotes, decisionSent >>

MakeDecision ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants : receivedVotes[p] \in {yes, no}
  /\ IF \A p \in participants : receivedVotes[p] = yes
       THEN coordinatorDecision' = commit
       ELSE coordinatorDecision' = abort
  /\ UNCHANGED << alive, faulty, vote, finalDecision, sentVote,
                requestSent, receivedVotes, decisionSent >>

BroadcastDecision(p) ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ coordinatorDecision \in {commit, abort}
  /\ decisionSent[p] = notsent
  /\ decisionSent' = [decisionSent EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED << alive, faulty, vote, finalDecision, sentVote,
                requestSent, receivedVotes, coordinatorDecision >>

CoordinatorDie ==
  /\ Coordinator \in alive
  /\ alive' = alive \ {Coordinator}
  /\ faulty' = faulty \cup {Coordinator}
  /\ UNCHANGED << vote, finalDecision, sentVote, requestSent,
                receivedVotes, coordinatorDecision, decisionSent >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ alive[p]
  /\ not faulty[p]
  /\ requestSent[p] = TRUE
  /\ sentVote[p] = FALSE
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << alive, faulty, vote, finalDecision,
                requestSent, receivedVotes,
                coordinatorDecision, decisionSent >>

AbortOnOwnVote(p) ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ alive[p]
  /\ not faulty[p]
  /\ vote[p] = no
  /\ sentVote[p] = TRUE
  /\ finalDecision[p] = undecided
  /\ finalDecision' = [finalDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << alive, faulty, vote, sentVote,
                requestSent, receivedVotes,
                coordinatorDecision, decisionSent >>

AbortOnTimeout(p) ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \notin alive
  /\ alive[p]
  /\ not faulty[p]
  /\ requestSent[p] = FALSE
  /\ finalDecision[p] = undecided
  /\ finalDecision' = [finalDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, sentVote, requestSent,
                receivedVotes, coordinatorDecision, decisionSent >>

DecideFromBroadcast(p) ==
  /\ alive = participants \cup {Coordinator}
  /\ Coordinator \in alive
  /\ alive[p]
  /\ not faulty[p]
  /\ decisionSent[p] \in {commit, abort}
  /\ finalDecision[p] = undecided
  /\ finalDecision' = [finalDecision EXCEPT ![p] = decisionSent[p]]
  /\ UNCHANGED << vote, sentVote, requestSent,
                receivedVotes, coordinatorDecision >>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = alive \ {p}
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, finalDecision, sentVote,
                requestSent, receivedVotes,
                coordinatorDecision, decisionSent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in participants : SendVoteRequest(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordinatorDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnOwnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromBroadcast(p)
  \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< alive, faulty, vote, finalDecision, sentVote,
                  requestSent, receivedVotes, coordinatorDecision, decisionSent >>

\* ----------------------------------------------------------------------
\* Safety invariants (not required by .cfg but useful for TLC)
\* ----------------------------------------------------------------------
TypeOK == TypeInv

====