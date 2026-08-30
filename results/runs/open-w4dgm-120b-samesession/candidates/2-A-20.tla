---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends the simple broadcast variant ACP-SB with reliable forwarding:
\* each participant has a forwarding table that records (a) its own
\* pre-decision (if any) and (b) which other participants it has forwarded to.
\* A participant finalizes its decision only after forwarding to everyone.
VARIABLES
  partVote,        \* each participant's yes/no vote (or no vote yet)
  partAlive,       \* true iff the participant has not crashed
  decision,        \* each participant's final decision (undecided, commit, abort)
  faulty,          \* participants that crashed silently
  sentVote,        \* each participant's vote-sent-flag
  coordReq,        \* coordinator awaiting a vote from this participant
  coordVote,       \* coordinator's recorded vote (yes/no, or no vote yet)
  coordBroadcast,  \* participants the coordinator has broadcast the decision to
  coordDecision,   \* commit/abort once decided, or undecided
  coordAlive,      \* coordinator up?
  coordFaulty,     \* coordinator crashed?
  forwarded        \* forwarded[p][q]: p's table entry for q (notsent/commit/abort)

vars == << partVote, partAlive, decision, faulty, sentVote,
           coordReq, coordVote, coordBroadcast, coordDecision,
           coordAlive, coordFaulty, forwarded >>

TypeOK ==
  /\ partVote \in [participants -> {yes, no, undecided}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordReq \in participants
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> BOOLEAN]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ partVote = [p \in participants |-> undecided]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordReq = CHOOSE p \in participants : TRUE
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> FALSE]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest(n) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq' = n
  /\ coordVote' = undecided
  /\ sentVote' = [sentVote EXCEPT ![n] = FALSE]
  /\ UNCHANGED << partVote, partAlive, decision, faulty,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forwarded >>

\* The bidder is slow but never fails, so its vote is always eventually in.
GetVote(n) ==
  /\ coordAlive
  /\ ~sentVote[n]
  /\ partAlive[n]
  /\ sentVote' = [sentVote EXCEPT ![n] = TRUE]
  /\ UNCHANGED << partVote, partAlive, decision, faulty,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, forwarded >>

DetectCoordFault(n) ==
  /\ coordAlive
  /\ ~sentVote[n]
  /\ ~partAlive[n]
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision, forwarded >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ sentVote[coordReq]
  /\ coordVote' = partVote[coordReq]
  /\ coordDecision' = IF partVote[coordReq] = yes THEN commit ELSE abort
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordBroadcast, coordAlive, coordFaulty, forwarded >>

Broadcasted ==
  \E n \in participants : coordBroadcast[n]

BroadcastCoord ==
  /\ coordDecision # undecided
  /\ coordAlive
  /\ ~Broadcasted
  /\ coordBroadcast' = [n \in participants |-> TRUE]
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordDecision, coordAlive, coordFaulty, forwarded >>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision, forwarded >>

SendVote(n) ==
  /\ partAlive[n]
  /\ decision[n] = undecided
  /\ coordAlive
  /\ coordBroadcast[n]
  /\ sentVote[n]
  /\ decision' = [decision EXCEPT ![n] = coordDecision]
  /\ UNCHANGED << partVote, partAlive, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, forwarded >>

PreDecideCoord(n) ==
  /\ partAlive[n]
  /\ decision[n] = undecided
  /\ coordBroadcast[n]
  /\ forwarded[n][n] = notsent
  /\ forwarded' = [forwarded EXCEPT ![n][n] = coordDecision]
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

PreDecideFwd(n, m) ==
  /\ partAlive[n]
  /\ decision[n] = undecided
  /\ forwarded[m][m] = notsent
  /\ forwarded[m][n] # notsent
  /\ forwarded' = [forwarded EXCEPT ![n][m] = forwarded[m][n]]
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

Forward(n, m) ==
  /\ partAlive[n]
  /\ forwarded[n][m] = notsent
  /\ forwarded[n][n] # notsent
  /\ forwarded' = [forwarded EXCEPT ![n][m] = forwarded[n][n]]
  /\ UNCHANGED << partVote, partAlive, decision, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

Decide(n) ==
  /\ partAlive[n]
  /\ decision[n] = undecided
  /\ \A m \in participants : forwarded[n][m] # notsent
  /\ decision' = [decision EXCEPT ![n] = forwarded[n][n]]
  /\ UNCHANGED << partVote, partAlive, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, forwarded >>

AbortOnTimeout(n) ==
  /\ partAlive[n]
  /\ decision[n] = undecided
  /\ coordFaulty
  /\ \A m \in participants :
       ~(coordBroadcast[m] /\ partAlive[m])
  /\ \A m \in participants :
       ~(\A k \in participants :
           (faulty[k] /\ forwarded[k][m] # notsent))
  /\ decision' = [decision EXCEPT ![n] = abort]
  /\ UNCHANGED << partVote, partAlive, faulty, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, forwarded >>

Die(n) ==
  /\ partAlive[n]
  /\ partAlive' = [partAlive EXCEPT ![n] = FALSE]
  /\ faulty' = [faulty EXCEPT ![n] = TRUE]
  /\ UNCHANGED << partVote, decision, sentVote,
                 coordReq, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, forwarded >>

Next ==
  \/ \E n \in participants :
       SendRequest(n) \/ GetVote(n) \/ DetectCoordFault(n) \/ SendVote(n)
         \/ PreDecideCoord(n) \/ Die(n) \/ AbortOnTimeout(n)
  \/ MakeDecision \/ BroadcastCoord \/ DieCoordinator
  \/ \E n \in participants, m \in participants :
       PreDecideFwd(n, m) \/ Forward(n, m) \/ Decide(n)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E n \in participants : SendRequest(n))
  /\ WF_vars(\E n \in participants : GetVote(n))
  /\ WF_vars(\E n \in participants : SendVote(n))
  /\ WF_vars(\E n \in participants : PreDecideCoord(n))
  /\ WF_vars(\E n \in participants, m \in participants : PreDecideFwd(n, m))
  /\ WF_vars(\E n \in participants, m \in participants : Forward(n, m))
  /\ WF_vars(\E n \in participants : Decide(n))
  /\ WF_vars(\E n \in participants : AbortOnTimeout(n))

\* No two participants reach different decisions.
AC1 == \A p, q \in participants :
  (decision[p] = commit) => (decision[q] # abort)

\* A commit requires unanimous yes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : partVote[p] = yes)

\* An abort is backed by a no-vote or a fault.
AC3 == (\E p \in participants : decision[p] = abort) =>
  (\E p \in participants : partVote[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

\* Decisions are irreversible.
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] = decision[p])

\* Every non-faulty participant eventually decides.
AC5 == \A p \in participants : (partAlive[p] /\ (decision[p] = undecided))
           ~> (decision[p] # undecided)

\* Weak fairness on progress actions (no deadlock, no stuck participant).
AC3l == <>(\A p \in participants : (decision[p] # undecided) \/ faulty[p] \/ coordFaulty)
====