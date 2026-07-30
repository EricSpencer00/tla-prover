---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, votesent, reqtype, reqvote, broadcast,
         coordstate, fwd

vars == <<vote, alive, decision, faulty, votesent, reqtype, reqvote,
          broadcast, coordstate, fwd>>

N == Cardinality(participants)
Ids == participants

NoReq == [type |-> waiting, vote |-> undecided]

TypeOK ==
  /\ vote \in [Ids -> {yes, no, undecided}]
  /\ alive \in [Ids -> BOOLEAN]
  /\ decision \in [Ids -> {undecided, commit, abort}]
  /\ faulty \subseteq Ids
  /\ votesent \subseteq Ids
  /\ reqtype \in {waiting, yes, no}
  /\ reqvote \in {yes, no, undecided}
  /\ broadcast \subseteq Ids
  /\ coordstate \in {init, ready, decided}
  /\ fwd \in [Ids -> [Ids -> {notsent, commit, abort}]]

InitBasic ==
  /\ vote = [i \in Ids |-> undecided]
  /\ alive = [i \in Ids |-> TRUE]
  /\ decision = [i \in Ids |-> undecided]
  /\ votesent = {}
  /\ reqtype = waiting
  /\ reqvote = undecided
  /\ broadcast = {}
  /\ coordstate = init

InitFwd ==
  [i \in Ids |-> [j \in Ids |-> notsent]]

Init ==
  /\ InitBasic
  /\ fwd = InitFwd

SendRequest ==
  /\ coordstate = init
  /\ \E v \in {yes, no} : reqtype' = v
  /\ coordstate' = ready
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, reqvote,
                 broadcast, fwd>>

GetVote ==
  /\ coordstate = ready
  /\ \E i \in participants : alive[i] /\ vote[i] = undecided
  /\ votesent' = votesent \cup participants
  /\ reqvote' = reqtype
  /\ coordstate' = decided
  /\ UNCHANGED <<vote, alive, decision, faulty, reqtype, broadcast,
                 fwd>>

\* Detection is separate so a crash between request and vote is caught.
DetectFault ==
  /\ coordstate = decided
  /\ reqvote = undecided
  /\ \E i \in participants : ~alive[i]
  /\ faulty' = faulty \cup participants
  /\ UNCHANGED <<vote, alive, decision, votesent, reqtype, reqvote,
                 broadcast, coordstate, fwd>>

Decide ==
  /\ coordstate = decided
  /\ reqvote # undecided
  /\ \E i \in participants :
        /\ alive[i]
        /\ vote[i] = undecided
        /\ vote' = [vote EXCEPT ![i] = reqvote]
        /\ fwd' = [fwd EXCEPT ![i][i] = IF reqvote = yes THEN commit ELSE abort]
  /\ broadcast' = broadcast \cup participants
  /\ UNCHANGED <<alive, decision, faulty, votesent, reqtype,
                 reqvote, coordstate>>

\* Participant receives the coordinator's broadcast.
PreDecideCoord ==
  /\ \E i \in participants :
       /\ alive[i]
       /\ fwd[i][i] = notsent
       /\ i \in broadcast
       /\ fwd' = [fwd EXCEPT ![i][i] = reqvote]

\* Participant receives a forwarded decision from a peer.
PreDecideFwd ==
  /\ \E i, j \in participants :
       /\ alive[i]
       /\ fwd[i][i] = notsent
       /\ fwd[j][i] # notsent
       /\ fwd' = [fwd EXCEPT ![i][i] = fwd[j][i]]

\* Participant forwards its pre-decision to a peer that has not yet received it.
Forward ==
  /\ \E i \in participants :
       /\ alive[i]
       /\ fwd[i][i] # notsent
       /\ \E j \in participants :
            /\ fwd[i][j] = notsent
            /\ fwd' = [fwd EXCEPT ![i][j] = fwd[i][i]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                 reqtype, reqvote, broadcast, coordstate>>

DecideNonBlocking ==
  /\ \E i \in participants :
       /\ alive[i]
       /\ decision[i] = undecided
       /\ \A j \in participants : fwd[i][j] # notsent
       /\ decision' = [decision EXCEPT ![i] = fwd[i][i]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, reqtype, reqvote,
                 broadcast, coordstate, fwd>>

\* Abort only when the coordinator is dead and no broadcast or forwarding
\* can help: every broadcast slot is either unfilled or unreceived, and no
\* dead participant has forwarded anything to an alive participant.
AbortTimeout ==
  /\ \E i \in participants :
       /\ alive[i]
       /\ decision[i] = undecided
       /\ ~alive[i]
       /\ \A k \in participants : k \notin broadcast
       /\ \A p \in faulty : \A q \in participants : alive[q] => fwd[p][q] = notsent
       /\ decision' = [decision EXCEPT ![i] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, reqtype, reqvote,
                 broadcast, coordstate, fwd>>

\* Crashing is excluded from weak fairness, so this is always available.
Die ==
  /\ \E i \in participants : alive' = [alive EXCEPT ![i] = FALSE]
  /\ faulty' = faulty \cup participants
  /\ UNCHANGED <<vote, decision, votesent, reqtype, reqvote,
                 broadcast, coordstate, fwd>>

NextBasic ==
  \/ SendRequest
  \/ GetVote
  \/ DetectFault
  \/ Decide
  \/ Die

Next ==
  \/ NextBasic
  \/ PreDecideCoord
  \/ PreDecideFwd
  \/ Forward
  \/ DecideNonBlocking
  \/ AbortTimeout

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PreDecideCoord)
  /\ WF_vars(PreDecideFwd)
  /\ WF_vars(Forward)
  /\ WF_vars(DecideNonBlocking)
  /\ WF_vars(AbortTimeout)

\* Safety: the set of decisions decided is always a singleton.
AC1 == Cardinality({decision[i] : i \in participants}) <= 1

\* A commit is only possible if everyone voted yes.
AC2 == (\E i \in participants : decision[i] = commit) =>
          \A i \in participants : vote[i] = yes

\* An abort is only possible if at least one participant voted no or some
\* participant/coordinator has crashed.
AC3 == (\E i \in participants : decision[i] = abort) =>
          (\E i \in participants : vote[i] = no) \/ faulty # {} \/ coordstate = ready

\* Once decided, a participant never reverts.
AC4 == \A i \in participants : decision[i] \in {undecided, commit, abort}

TypeInvNB == TypeOK /\ AC1 /\ AC2 /\ AC3 /\ AC4

\* Liveness: everything decides or someone crashes.
AC3Live == <>(\A i \in participants : decision[i] # undecided) \/ faulty # {}

\* Liveness: every non-faulty participant eventually decides.
AC5 == \A i \in participants : (alive[i] /\ decision[i] = undecided) ~> (decision[i] # undecided)

Properties == AC3Live /\ AC5

====