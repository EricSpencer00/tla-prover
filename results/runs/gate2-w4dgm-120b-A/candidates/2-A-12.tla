---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, commit, or abort.
Status == {notsent, commit, abort}

VARIABLES partVote, partAlive, partDecision, partFaulty, partVoteSent, coord

vars == <<partVote, partAlive, partDecision, partFaulty, partVoteSent, coord>>

TypeOK ==
  /\ partVote \in [participants -> {yes, no, undecided}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {waiting, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partVoteSent \in [participants -> BOOLEAN]
  /\ coord \in [req : BOOLEAN, vote : {yes, no}, broadcast : BOOLEAN,
               decision : {yes, no}, alive : BOOLEAN, faulty : BOOLEAN, ft : Status]
  /\ coord vt = [req |-> FALSE, vote |-> undecided, broadcast |-> FALSE,
                 decision |-> undecided, alive |-> TRUE, faulty |-> FALSE,
                 ft |-> notsent]

Init ==
  /\ partVote = [p \in participants |-> undecided]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> waiting]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partVoteSent = [p \in participants |-> FALSE]
  /\ coord = [req |-> FALSE, vote |-> undecided, broadcast |-> FALSE,
              decision |-> undecided, alive |-> TRUE, faulty |-> FALSE, ft |-> notsent]

CoordSendReq ==
  /\ coord.alive
  /\ ~coord.req
  /\ coord' = [coord EXCEPT !.req = TRUE]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

CoordGetVote(p) ==
  /\ coord.alive
  /\ partAlive[p]
  /\ coord.req
  /\ coord.vote = undecided
  /\ partVote[p] # undecided
  /\ coord' = [coord EXCEPT !.vote = partVote[p]]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

CoordDetectFault(p) ==
  /\ coord.alive
  /\ ~partAlive[p]
  /\ coord.vote = undecided
  /\ coord' = [coord EXCEPT !.vote = no]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

CoordMakeDecision ==
  /\ coord.alive
  /\ coord.req
  /\ coord.vote # undecided
  /\ ~coord.broadcast
  /\ coord' = [coord EXCEPT !.decision = coord.vote, !.broadcast = TRUE]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

CoordBroadcast(p) ==
  /\ coord.broadcast
  /\ coord.ft = notsent
  /\ partAlive[p]
  /\ coord' = [coord EXCEPT !.ft = IF coord.vote = yes THEN commit ELSE abort]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

CoordDie ==
  /\ coord.alive
  /\ ~coord.faulty
  /\ coord' = [coord EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<partVote, partAlive, partDecision, partFaulty, partVoteSent>>

\* A participant stores a pre-decision it received from the coordinator.
PartPreDecideFromCoord(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = waiting
  /\ coord.broadcast
  /\ partAlive[p]
  /\ coord.ft \in {commit, abort}
  /\ coord.ft # notsent
  /\ coord' = [coord EXCEPT !.ft = notsent]
  /\ partDecision' = [partDecision EXCEPT ![p] = IF coord.ft = commit THEN commit ELSE abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partVoteSent, coord>>

\* A participant stores a pre-decision it received forwarded from another participant.
PartPreDecideFromForward(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = waiting
  /\ \E q \in participants : q # p /\ partAlive[q]
       /\ partDecision[q] # waiting
       /\ partDecision[p] = waiting
       /\ partDecision' = [partDecision EXCEPT ![p] = partDecision[q]]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partVoteSent, coord>>

\* Forward a received pre-decision to another participant.
PartForward(p, q) ==
  /\ p # q
  /\ partAlive[p]
  /\ partAlive[q]
  /\ partDecision[p] # waiting
  /\ partDecision[q] = waiting
  /\ partDecision' = [partDecision EXCEPT ![q] = partDecision[p]]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partVoteSent, coord>>

\* Decide non-blockingly once the pre-decision has been forwarded to everyone.
PartDecide(p) ==
  /\ partAlive[p]
  /\ partDecision[p] # waiting
  /\ \A q \in participants : partDecision[q] # waiting \/ q = p
  /\ partDecision' = [partDecision EXCEPT ![p] = IF partDecision[p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partVoteSent, coord>>

\* Abort on timeout when the coordinator is dead and no live broadcast exists.
PartAbortOnTimeout(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = waiting
  /\ ~coord.alive
  /\ \A q \in participants : partAlive[q] => ~coord.broadcast
  /\ \A q \in participants : partFaulty[q] => partDecision[q] = waiting
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<partVote, partAlive, partFaulty, partVoteSent, coord>>

PartSendVote(p) ==
  /\ partAlive[p]
  /\ ~partVoteSent[p]
  /\ partVote' = [partVote EXCEPT ![p] = yes]
  /\ partVoteSent' = [partVoteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partAlive, partDecision, partFaulty, coord>>

PartAbort(p) ==
  /\ partAlive[p]
  /\ ~partVoteSent[p]
  /\ partVote' = [partVote EXCEPT ![p] = no]
  /\ partVoteSent' = [partVoteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partAlive, partDecision, partFaulty, coord>>

PartDie(p) ==
  /\ partAlive[p]
  /\ ~partFaulty[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<partVote, partDecision, partVoteSent, coord>>

Next ==
  \/ CoordSendReq \/ CoordMakeDecision \/ CoordDie
  \/ \E p \in participants : CoordGetVote(p) \/ CoordDetectFault(p) \/ CoordBroadcast(p)
       \/ PartPreDecideFromCoord(p) \/ PartPreDecideFromForward(p)
       \/ PartDecide(p) \/ PartAbortOnTimeout(p) \/ PartSendVote(p) \/ PartAbort(p) \/ PartDie(p)
  \/ \E p, q \in participants : PartForward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PartDecide(<<p \in participants>>))
  /\ SF_vars(CoordMakeDecision)
  /\ WF_vars(PartAbortOnTimeout(<<p \in participants>>))

\* Safety: no two participants ever reach different decisions.
Agreement ==
  \A p, q \in participants :
    (partDecision[p] = commit /\ partDecision[q] = abort) => FALSE

\* AC2: a commit only happens if everyone voted yes.
CommitValidity ==
  (\E p \in participants : partDecision[p] = commit) =>
    (\A q \in participants : partVote[q] = yes)

\* AC3: an abort is backed by a no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
  (\E p \in participants : partDecision[p] = abort) =>
    (\E q \in participants : partVote[q] = no) \/ coord.faulty

\* AC4: decisions are final.
Irreversibility ==
  \A p \in participants :
    partDecision[p] \in {commit, abort} => (partDecision' = [partDecision EXCEPT ![p] = partDecision[p]])

TypeInvNB == TypeOK

BatteryAC3 ==
  <>(\A p \in participants : partDecision[p] # waiting \/ coord.faulty \/ \E q \in participants : partFaulty[q])

\* AC5: every live participant eventually decides (not just some).
EventualDecision ==
  \A p \in participants : (partAlive[p] /\ partDecision[p] = waiting) ~> (partDecision[p] # waiting)

====