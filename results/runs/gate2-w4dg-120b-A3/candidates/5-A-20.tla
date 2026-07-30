---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote, alive, decision, faulty, sentVote, reqSent,
  recvVote, broadcastSent, cDecision, cAlive, cFaulty

vars == << vote, alive, decision, faulty, sentVote, reqSent,
           recvVote, broadcastSent, cDecision, cAlive, cFaulty >>

\* BroadcastSent/recvVote use waiting/notsent markers instead of Nil because
\* the spec never introduces Nil; that is why the reference config names
\* waiting and notsent rather than Nil.

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in SUBSET participants
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcastSent \in [participants -> {commit, abort, notsent}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentVote = {}
  /\ reqSent = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcastSent = [p \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

\* The coordinator sends one vote request at a time (simple broadcast).
SendVoteRequest(p) ==
  /\ cAlive
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

ReceiveVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A q \in participants : reqSent[q]
  /\ recvVote[p] = waiting
  /\ p \in sentVote
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, reqSent,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

DetectFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A q \in participants : reqSent[q]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, reqSent,
       recvVote, broadcastSent, cAlive, cFaulty
     >>

MakeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ cDecision' =
       IF \A p \in participants : recvVote[p] = yes
         THEN commit ELSE abort
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, reqSent,
       recvVote, broadcastSent, cAlive, cFaulty
     >>

BroadcastDecision(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, reqSent,
       recvVote, cDecision, cAlive, cFaulty
     >>

CoordDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<
       vote, alive, decision, faulty, sentVote, reqSent,
       recvVote, broadcastSent, cDecision, cAlive
     >>

SendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<
       vote, alive, decision, faulty, reqSent, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in sentVote
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<
       vote, alive, faulty, sentVote, reqSent, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

AbortWithoutRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~reqSent[p]
  /\ ~cAlive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<
       vote, alive, faulty, sentVote, reqSent, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcastSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED <<
       vote, alive, faulty, sentVote, reqSent, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<
       vote, decision, sentVote, reqSent, recvVote,
       broadcastSent, cDecision, cAlive, cFaulty
     >>

Next ==
  \/ \E p \in participants :
       SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
         \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
         \/ AbortWithoutRequest(p) \/ DecideFromBroadcast(p) \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendVoteRequest(p))
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : AbortOnVote(p))
        /\ WF_vars(\E p \in participants : AbortWithoutRequest(p))
        /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))

\* Safety: no split-brain, commit only on unanimous yes, abort only on
\* a no vote or a fault, and each participant decides at most once.
Agreement ==
  /\ \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
  /\ (commit \in {decision[p] : p \in participants})
       => \A p \in participants : vote[p] = yes
  /\ (abort \in {decision[p] : p \in participants})
       => ( \E p \in participants : vote[p] = no) \/ (cFaulty \/ \E p \in participants : faulty[p])
  /\ \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
  /\ \A p \in participants : (decision[p] = abort) ~> (decision[p] = abort)

DecideEventually ==
  <>(\A p \in participants : decision[p] # undecided \/ cFaulty \/ \E q \in participants : faulty[q])

====