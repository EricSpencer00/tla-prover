---- MODULE ACP_NB ----
\* Non-Blocking Atomic Commitment Protocol with reliable broadcast forwarding.
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

None == "none"

VARIABLES pstate, faulty, decision, voted, votesent, coord

vars == <<pstate, faulty, decision, voted, votesent, coord>>

TypeInvNB ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ decision \in [participants -> {yes, no, waiting}]
  /\ coord \in {undecided, commit, abort}
  /\ voted \in [participants -> {yes, no}]
  /\ votesent \in [participants -> BOOLEAN]
  /\ faulty \in [participants \cup {None} -> BOOLEAN]

InitNB ==
  /\ pstate = [p \in participants |-> undecided]
  /\ decision = [p \in participants |-> waiting]
  /\ voted = [p \in participants |-> no]
  /\ votesent = [p \in participants |-> FALSE]
  /\ coord = undecided
  /\ faulty = [p \in participants \cup {None} |-> FALSE]

\* Coordinator actions (inherited from the simple broadcast protocol).
Request(p) ==
  /\ ~faulty[p]
  /\ pstate[p] = undecided
  /\ ~votesent[p]
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<decision, pstate, voted, coord, faulty>>

GetVote(p) ==
  /\ ~faulty[p]
  /\ votesent[p]
  /\ pstate[p] = undecided
  /\ UniMod(voted[p]) \in {yes, no}
  /\ voted' = [voted EXCEPT ![p] = UniMod(voted[p])]
  /\ UNCHANGED <<decision, pstate, votesent, coord, faulty>>

DetectFault(p) ==
  /\ pstate[p] = undecided
  /\ ~votesent[p]
  /\ UniMod(voted[p]) \in {yes, no}
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<decision, voted, votesent, coord, faulty>>

MakeDecision ==
  /\ coord = undecided
  /\ \A p \in participants : pstate[p] \in {commit, abort}
  /\ \E b \in {commit, abort} : coord' = b
  /\ UNCHANGED <<pstate, decision, voted, votesent, faulty>>

BroadcastDecision(p) ==
  /\ ~faulty[p]
  /\ pstate[p] \in {commit, abort}
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = coord]
  /\ UNCHANGED <<pstate, voted, votesent, coord, faulty>>

CoordDie ==
  /\ ~faulty[None]
  /\ ~votesent[None]
  /\ coord' = abort
  /\ faulty' = [faulty EXCEPT ![None] = TRUE]
  /\ UNCHANGED <<pstate, decision, voted, votesent>>

\* Everyone must forward their pre-decision before deciding locally.
PreDecideCoordinator(p) ==
  /\ decision[p] = waiting
  /\ decision[p] # waiting
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<pstate, voted, votesent, coord, faulty>>

PreDecideForward(p) ==
  /\ decision[p] = waiting
  /\ \E q \in participants \ {{p}} : decision[q] = pstate[p]
  /\ decision' = [decision EXCEPT ![p] = pstate[p]]
  /\ UNCHANGED <<pstate, voted, votesent, coord, faulty>>

Forward(p) ==
  /\ decision[p] # waiting
  /\ decision[p] # pstate[p]
  /\ \E q \in participants \ {{p}} : decision' = [decision EXCEPT ![q] = decision[p]]
  /\ UNCHANGED <<pstate, voted, votesent, coord, faulty>>

DecideNB(p) ==
  /\ decision[p] # waiting
  /\ \A q \in participants : decision[q] # waiting
  /\ pstate[p] = undecided
  /\ pstate' = [pstate EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<decision, voted, votesent, coord, faulty>>

AbortOnTimeoutNB(p) ==
  /\ pstate[p] = undecided
  /\ coord = abort
  /\ \A q \in participants : decision[q] = waiting
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<decision, voted, votesent, coord, faulty>>

DieNB(p) ==
  /\ ~faulty[p]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voted, votesent, coord>>

NextNB ==
  \E p \in participants \cup {None} :
    \/ Request(p) \/ GetVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
    \/ DieNB(p) \/ PreDecideCoordinator(p) \/ PreDecideForward(p)
    \/ Forward(p) \/ DecideNB(p) \/ AbortOnTimeoutNB(p)
    \/ (p = None /\ CoordDie)

\* Weak fairness for all progress actions except crashing.
SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : Request(p))
  /\ WF_vars(\E p \in participants : GetVote(p))
  /\ WF_vars(\E p \in participants : DetectFault(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))
  /\ WF_vars(\E p \in participants : PreDecideCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ WF_vars(\E p \in participants : Forward(p))
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeoutNB(p))

\* Safety: no conflicting decisions, and decisions only backed by all yes or a fault.
AC1 ==
  \A p, q \in participants : ~(pstate[p] = commit /\ pstate[q] = abort)

AC2 ==
  \A p \in participants :
    pstate[p] = commit => \A q \in participants : voted[q] = yes

AC3 ==
  \A p \in participants :
    pstate[p] = abort =>
      \/ \E q \in participants : voted[q] = no
      \/ \E q \in participants : faulty[q]
      \/ faulty[None]

AC4 ==
  \A p \in participants : (pstate[p] \in {commit, abort}) ~> (pstate[p] \in {commit, abort})

\* Liveness: progress to a decision, and non-faulty participants terminate.
AC3live ==
  <>(\A p \in participants : pstate[p] \in {commit, abort}
       \/ faulty[p] \/ faulty[None])

Terminate ==
  \A p \in participants : ~(faulty[p] \/ pstate[p] \in {commit, abort}) ~>
                         (pstate[p] \in {commit, abort})

====