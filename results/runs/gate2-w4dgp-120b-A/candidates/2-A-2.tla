---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table

vars == <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table>>

\* ACP-NB extends the simple broadcast protocol (ACP_SB) by a reliable broadcast:
\* each participant forwards the pre-decision it receives to all others before
\* finalizing its own decision. The table[i][j] entry tracks what i has sent to j
\* (notsent, commit, or abort) and, at the i index, what i has pre-decided.
\* The forwarded-decision check in Abort3NF (below) is the non-crash progress
\* guarantee: a participant may still learn the decision from a dead peer's
\* forwarding, so no-one is left undecided forever if any surviving node can decide.

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ cstate = waiting
  /\ cphase = waiting
  /\ cdecision = undecided
  /\ csent = FALSE
  /\ ccoord = TRUE
  /\ table = [i \in participants |-> [j \in participants |-> notsent]]

\* Coordinator protocol (identical to ACP_SB, inherited unchanged):
SendReq ==
  /\ cstate = waiting
  /\ ccoord
  /\ cstate' = [cstate EXCEPT ![waiting |-> FALSE]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cphase, cdecision, csent, ccoord, table>>

GetVote(p) ==
  /\ cstate = [waiting |-> FALSE]
  /\ ccoord
  /\ alive[p]
  /\ ~sent[p]
  /\ vote[p] \in {yes, no}
  /\ sent' = [sent EXCEPT ![p |-> TRUE]]
  /\ UNCHANGED <<vote, alive, decision, faulty, cstate, cphase, cdecision, csent, ccoord, table>>

DetectFault(p) ==
  /\ cstate = [waiting |-> FALSE]
  /\ ccoord
  /\ alive[p]
  /\ ~sent[p]
  /\ ~faulty[p]
  /\ faulty' = [faulty EXCEPT ![p |-> TRUE]]
  /\ UNCHANGED <<vote, alive, decision, sent, cstate, cphase, cdecision, csent, ccoord, table>>

Decide ==
  /\ ccoord
  /\ \E x \in {commit, abort} :
       /\ cphase = waiting
       /\ cdecision' = x
       /\ cphase' = x
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, csent, ccoord, table>>

Broadcast ==
  /\ ccoord
  /\ cphase \in {commit, abort}
  /\ ~csent
  /\ csent' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, ccoord, table>>

DieCoord ==
  /\ ccoord
  /\ ccoord' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, table>>

Coordinator ==
  \/ SendReq \/ Decide \/ Broadcast \/ DieCoord
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p)

\* Participant actions: the base ACP_SB actions plus a pre-decide step (2),
\* a forwarding step (3), and a non-blocking finalization step (4).
SendVote(p) ==
  /\ alive[p]
  /\ ~sent[p]
  /\ \E x \in {yes, no} : vote' = [vote EXCEPT ![p |-> x]]
  /\ sent' = [sent EXCEPT ![p |-> TRUE]]
  /\ UNCHANGED <<alive, decision, faulty, cstate, cphase, cdecision, csent, ccoord, table>>

AbortTimer(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ccoord = FALSE
  /\ decision' = [decision EXCEPT ![p |-> abort]]
  /\ UNCHANGED <<vote, alive, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table>>

\* (1) Pre-decide from the coordinator's broadcast.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ csent
  /\ cdecision # undecided
  /\ table[p][p] = notsent
  /\ table' = [table EXCEPT ![p][p] = cdecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord>>

\* (2) Pre-decide from another participant's forwarding.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ table[q][p] # notsent /\ table[p][p] = notsent
  /\ table' = [table EXCEPT ![p][p] = IF \E q \in participants : q # p /\ table[q][p] # notsent THEN table[q][p] ELSE notsent]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord>>

\* (3) Forward the received pre-decision to another participant.
Forward(p) ==
  /\ alive[p]
  /\ table[p][p] # notsent
  /\ \E q \in participants : q # p /\ table[p][q] = notsent
  /\ table' = [table EXCEPT ![p][q] = table[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord>>

\* (4) Non-blocking local finalization: commit/abort only after all forwardings.
DecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => table[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p |-> table[p][p]]]
  /\ UNCHANGED <<vote, alive, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table>>

\* (5) Abort on timeout when the coordinator dead and no forwardings remain.
Abort3NF(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ccoord = FALSE
  /\ \A q \in participants : ~alive[q] \/ csent
  /\ \A q \in participants : alive[q] => (table[q][p] = notsent /\ table[p][q] = notsent)
  /\ decision' = [decision EXCEPT ![p |-> abort]]
  /\ UNCHANGED <<vote, alive, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p |-> FALSE]
  /\ UNCHANGED <<vote, decision, faulty, sent, cstate, cphase, cdecision, csent, ccoord, table>>

Participant ==
  \/ \E p \in participants : SendVote(p) \/ AbortTimer(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Forward(p) \/ DecideFwd(p) \/ Abort3NF(p) \/ Die(p)

Next ==
  \/ Coordinator
  \/ Participant

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(PreDecideCoord)
  /\ WF_vars(PreDecideFwd)
  /\ WF_vars(Forward)
  /\ WF_vars(DecideFwd)
  /\ WF_vars(AbortTimer)
  /\ WF_vars(Abort3NF)

\* Agreement: no two participants commit and abort.
TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ cstate \in {waiting, [waiting |-> TRUE, waiting |-> FALSE]}
  /\ cphase \in {waiting, commit, abort}
  /\ cdecision \in {undecided, commit, abort}
  /\ csent \in BOOLEAN
  /\ ccoord \in BOOLEAN
  /\ table \in [participants -> [participants -> {notsent, commit, abort}]]

\* Explicitly name the base properties (safety unchanged from ACP_SB).
AC1 ==
  ~(commit \in {decision[p] : p \in participants} /\ abort \in {decision[p] : p \in participants})

AC2 ==
  (commit \in {decision[p] : p \in participants}) => (\A p \in participants : vote[p] = yes)

AC3 ==
  (abort \in {decision[p] : p \in participants}) =>
    (\E p \in participants : vote[p] = no \/ faulty[p] \/ ~ccoord)

AC4 ==
  \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

\* Liveness restores progress: the reliable broadcast guarantees termination for
\* every non-crashed participant, which the simple broadcast version cannot.
DecideNbFwd ==
  \A p \in participants : (decision[p] = undecided) ~> (decision[p] \in {commit, abort})

AC5 == DecideNbFwd

====