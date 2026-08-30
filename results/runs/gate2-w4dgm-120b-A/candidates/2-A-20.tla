---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, calive, decision, pcrashed, vote, bsent, cstate, fwdtable

vars == <<pstate, calive, decision, pcrashed, vote, bsent, cstate, fwdtable>>

TypeOK ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ calive \in BOOLEAN
  /\ decision \in {commit, abort, waiting}
  /\ pcrashed \in [participants -> BOOLEAN]
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ bsent \in [participants -> BOOLEAN]
  /\ cstate \in {waiting, yes, no}
  /\ fwdtable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ calive = TRUE
  /\ decision = waiting
  /\ pcrashed = [p \in participants |-> FALSE]
  /\ vote = [p \in participants |-> undecided]
  /\ bsent = [p \in participants |-> FALSE]
  /\ cstate = waiting
  /\ fwdtable = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions inherited from the simple broadcast protocol; unchanged
SendRequest ==
  /\ calive
  /\ cstate = waiting
  /\ cstate' = yes
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, bsent, fwdtable>>

GetVote(p) ==
  /\ calive
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, bsent, cstate, fwdtable>>

DetectFault(p) ==
  /\ pcrashed[p]
  /\ cstate = waiting
  /\ cstate' = no
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, bsent, fwdtable>>

MakeDecision ==
  /\ calive
  /\ cstate = yes
  /\ decision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, calive, pcrashed, vote, bsent, cstate, fwdtable>>

Broadcast(p) ==
  /\ calive
  /\ ~bsent[p]
  /\ bsent' = [bsent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, cstate, fwdtable>>

DieCoordinator ==
  /\ calive
  /\ calive' = FALSE
  /\ UNCHANGED <<pstate, decision, pcrashed, vote, bsent, cstate, fwdtable>>

\* Participant pre-decision from the coordinator's broadcast
PredecideFromCoord(p) ==
  /\ ~pcrashed[p]
  /\ fwdtable[p][p] = notsent
  /\ decision # waiting
  /\ fwdtable' = [fwdtable EXCEPT ![p][p] = decision]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, bsent, cstate>>

\* Participant pre-decision from another participant's forwarding
PredecideFromPeer(p) ==
  /\ ~pcrashed[p]
  /\ fwdtable[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ fwdtable[q][p] # notsent
       /\ fwdtable' = [fwdtable EXCEPT ![p][p] = fwdtable[q][p]]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, bsent, cstate>>

SendVote(p) ==
  /\ ~pcrashed[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, bsent, cstate, fwdtable>>

\* Forward a pre-decision to another participant; part of reliable broadcast
Forward(p, q) ==
  /\ ~pcrashed[p]
  /\ p # q
  /\ fwdtable[p][p] # notsent
  /\ fwdtable[p][q] = notsent
  /\ fwdtable' = [fwdtable EXCEPT ![p][q] = fwdtable[p][p]]
  /\ UNCHANGED <<pstate, calive, decision, pcrashed, vote, bsent, cstate>>

\* Decide only after forwarding the pre-decision to everyone else
Decide(p) ==
  /\ ~pcrashed[p]
  /\ pstate[p] = undecided
  /\ fwdtable[p][p] # notsent
  /\ \A q \in participants : q # p => fwdtable[p][q] = fwdtable[p][p]
  /\ pstate' = [pstate EXCEPT ![p] = fwdtable[p][p]]
  /\ UNCHANGED <<calive, decision, pcrashed, vote, bsent, cstate, fwdtable>>

\* Abort by timeout when the coordinator is dead and no decision source remains
AbortByTimeout(p) ==
  /\ ~pcrashed[p]
  /\ pstate[p] = undecided
  /\ ~calive
  /\ (\A q \in participants : ~bsent[q])
  /\ (\A q \in participants : pcrashed[q] => \A r \in participants : fwdtable[q][r] = notsent)
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<calive, decision, pcrashed, vote, bsent, cstate, fwdtable>>

\* Any participant may crash silently, becoming faulty
Die(p) ==
  /\ ~pcrashed[p]
  /\ pcrashed' = [pcrashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, calive, decision, vote, bsent, cstate, fwdtable>>

Next ==
  \/ SendRequest \/ MakeDecision \/ DieCoordinator
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ Broadcast(p)
  \/ \E p \in participants : PredecideFromCoord(p) \/ PredecideFromPeer(p)
  \/ \E p \in participants : SendVote(p) \/ Decide(p) \/ AbortByTimeout(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : SF_vars(SendVote(p)) /\ WF_vars(Decide(p))
  /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision)
  /\ WF_vars(DieCoordinator)

\* Safety: no two participants ever reach different decisions
AC1 ==
  \A p, q \in participants :
    (pstate[p] = commit /\ pstate[q] = abort) => FALSE

\* Commit was only possible with unanimous yes votes
AC2 ==
  (\E p \in participants : pstate[p] = commit) =>
    (\A q \in participants : vote[q] = yes)

\* Abort means some vote was no, some participant died, or the coordinator died
AC3 ==
  (\E p \in participants : pstate[p] = abort) =>
    (\E q \in participants : vote[q] = no \/ pcrashed[q]) \/ ~calive

\* A participant's decision is final once it is made
AC4 ==
  \A p \in participants :
    (pstate[p] # undecided) ~> (pstate[p] = pstate[p])

\* Every non-faulty participant eventually decides (commit or abort)
AC5 ==
  \A p \in participants :
    (~pcrashed[p]) ~> (pstate[p] # undecided)

\* Weak fairness on coordinator progress (excluding death) and participant progress
CoordProgressFair ==
  /\ SF_vars(SendRequest)
  /\ WF_vars(MakeDecision)
  /\ WF_vars(DieCoordinator)

ParticipantProgressFair ==
  \A p \in participants :
    /\ SF_vars(SendVote(p))
    /\ WF_vars(Decide(p))
    /\ WF_vars(PredecideFromCoord(p))
    /\ WF_vars(PredecideFromPeer(p))

TypeInvNB == TypeOK

====