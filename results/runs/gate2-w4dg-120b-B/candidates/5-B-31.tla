---- MODULE W4DG_5m9p1t0 ----
\* Simple Broadcast atomic-commit protocol; a broadcast is a series of messages,
\* each of which may be interrupted by a failure, so the algorithm is non-terminating.
EXTENDS Naturals

CONSTANTS participants

ASSUME participants = {p1, p2, p3}

\* Votes and decisions are modelled by the usual three values, encoded as integers.
yes == 1
no == 0

\* Coordinator: participant-indexed records of request sent, vote received, and
\* broadcast message sent. The coordinator is a single point of failure.
Coordinator == [request : [participants -> BOOLEAN],
                vote : [participants -> {yes, no, -1}],
                broadcast : [participants -> {yes, no, -1}],
                decision : {yes, no, -1},
                alive : BOOLEAN,
                faulty : BOOLEAN]

\* A participant: its vote, life/health flags, and its decision (none/commit/abort).
Participant == [vote : {yes, no},
                alive : BOOLEAN,
                faulty : BOOLEAN,
                decision : {yes, no, -1}]

VARIABLES coordinator, participant

vars == <<coordinator, participant>>

TypeInv == /\ coordinator \in Coordinator
           /\ participant \in [participants -> Participant]

\* Initially: no request sent, no vote received, no broadcast sent, all alive.
Init == /\ coordinator = [request |-> [p \in participants |-> FALSE],
                          vote |-> [p \in participants |-> -1],
                          broadcast |-> [p \in participants |-> -1],
                          decision |-> -1,
                          alive |-> TRUE,
                          faulty |-> FALSE]
        /\ participant = [p \in participants |->
                            [vote |-> yes,
                             alive |-> TRUE,
                             faulty |-> FALSE,
                             decision |-> -1]]

\* request(i): the coordinator asks participant i to vote.
Request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                                   [coordinator.request EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

\* sendVote(i): an alive participant i sends its vote back.
SendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ coordinator' = [coordinator EXCEPT !.vote =
                                    [coordinator.vote EXCEPT ![i] = participant[i].vote]]
               /\ UNCHANGED participant

\* coordinator makes its decision once every participant has voted.
MakeDecision == /\ coordinator.alive
                /\ coordinator.decision = -1
                /\ \A p \in participants : coordinator.vote[p] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                                     IF \A p \in participants : coordinator.vote[p] = yes
                                        THEN yes ELSE no]
                /\ UNCHANGED participant

\* coordBroadcast(i): the coordinator sends its decision to participant i.
CoordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision \in {yes, no}
                     /\ coordinator.broadcast[i] = -1
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                                          [coordinator.broadcast EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

\* decide(i): an alive participant i adopts the coordinator's decision.
Decide(i) == /\ participant[i].alive
             /\ participant[i].decision = -1
             /\ coordinator.broadcast[i] \in {yes, no}
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

\* abortOnVote(i): an alive participant with a NO vote aborts unilaterally.
AbortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = -1
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = no]
                  /\ UNCHANGED coordinator

\* abortOnTimeout(i): an alive participant aborts if the coordinator dies silently.
AbortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = -1
                     /\ ~coordinator.alive
                     /\ ~coordinator.request[i]
                     /\ participant' = [participant EXCEPT ![i].decision = no]
                     /\ UNCHANGED coordinator

\* coordDie: the coordinator dies silently and becomes forever faulty.
CoordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* parDie(i): participant i dies silently and becomes forever faulty.
ParDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
             /\ UNCHANGED coordinator

\* The next-state relation. Death transitions are left outside fairness.
Next == \/ \E i \in participants : Request(i) \/ SendVote(i) \/ CoordBroadcast(i)
                           \/ Decide(i) \/ AbortOnVote(i) \/ AbortOnTimeout(i) \/ ParDie(i)
        \/ MakeDecision
        \/ CoordDie

\* Fairness: every participant eventually acts, and the coordinator eventually
\* receives every vote and makes a decision (given nobody is faulty).
Fairness == /\ \A i \in participants : WF_vars(Request(i))
           /\ \A i \in participants : WF_vars(SendVote(i))
           /\ \A i \in participants : WF_vars(Decide(i))
           /\ \A i \in participants : WF_vars(CoordBroadcast(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Correctness: at most one commit decision, and commit only on a unanimous YES.
AC1 == \A i, j \in participants :
          (participant[i].decision = yes /\ participant[j].decision = no) => FALSE

AC2 == \A i \in participants :
          participant[i].decision = yes => \A j \in participants : participant[j].vote = yes

=============================================================================