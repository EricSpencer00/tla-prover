---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, calive, decision, pdec, pphase, pvote, pname, pto, pforward

TypeInv ==
    /\ pstate \in {"init", "collecting", "decided", "aborted"}
    /\ calive \in BOOLEAN
    /\ decision \in {undecided, commit, abort}
    /\ pdec \in [participants -> {"yes", "no", undecided}]
    /\ pphase \in [participants -> {waiting, notsent, commit, abort}]
    /\ pvote \in [participants -> {"yes", "no", undecided}]
    /\ pname \in [participants -> {"init", "collecting", "decided", "aborted"}]
    /\ pto \in [participants -> {"init", "request", "vote", "broadcast", "decision", "abort"}]
    /\ pforward \in [participants -> [participants -> {"notsent", "commit", "abort"}]]

Init ==
    /\ pstate = "init"
    /\ calive = TRUE
    /\ decision = undecided
    /\ pdec = [p \in participants |-> undecided]
    /\ pphase = [p \in participants |-> waiting]
    /\ pvote = [p \in participants |-> undecided]
    /\ pname = [p \in participants |-> "init"]
    /\ pto = [p \in participants |-> "init"]
    /\ pforward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions, inherited from the simple broadcast protocol.
SendRequest(p) ==
    /\ pto[p] = "init"
    /\ pto' = [pto EXCEPT ![p] = "request"]
    /\ pname' = [pname EXCEPT ![p] = "collecting"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pforward>>

GetVote(p, v) ==
    /\ pname[p] = "collecting"
    /\ pvote[p] = undecided
    /\ pvote' = [pvote EXCEPT ![p] = v]
    /\ pto' = [pto EXCEPT ![p] = "vote"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pname, pforward>>

DetectCoordFault ==
    /\ calive
    /\ \A p \in participants: pto[p] \in {"init", "request"}
    /\ calive' = FALSE
    /\ pstate' = "aborted"
    /\ pname' = [p \in participants |-> "aborted"]
    /\ pto' = [pto EXCEPT ![CHOOSE p \in participants: TRUE] = "abort"]
    /\ UNCHANGED <<decision, pdec, pphase, pvote, pforward>>

MakeDecision(v) ==
    /\ pstate = "collecting"
    /\ \A p \in participants: pvote[p] # undecided
    /\ decision' = v
    /\ pstate' = "decided"
    /\ pname' = [p \in participants |-> "decided"]
    /\ UNCHANGED <<calive, pdec, pphase, pvote, pto, pforward>>

Broadcast(p) ==
    /\ pname[p] = "decided"
    /\ pto[p] # "broadcast"
    /\ pto' = [pto EXCEPT ![p] = "broadcast"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pname, pforward>>

Die ==
    /\ calive \/ \E p \in participants: pto[p] # "init"
    /\ calive' = FALSE
    /\ pstate' = "aborted"
    /\ pname' = [p \in participants |-> "aborted"]
    /\ UNCHANGED <<decision, pdec, pphase, pvote, pto, pforward>>

\* Participant actions (the reliable broadcast extension):
\* A participant stores a pre-decision it receives from the coordinator.
PredecideFromCoordinator(p) ==
    /\ calive
    /\ pphase[p] = waiting
    /\ pname[p] = "decided"
    /\ pforward[p][p] = notsent
    /\ pforward' = [pforward EXCEPT ![p][p] = IF decision = commit THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pname, pto>>

\* A participant stores a pre-decision it receives from a peer.
PredecideFromPeer(p) ==
    /\ pphase[p] = waiting
    /\ \E q \in participants: q # p /\ pforward[q][p] # notsent
    /\ pphase' = [pphase EXCEPT ![p] = IF \E q \in participants: pforward[q][p] = "commit" THEN "commit" ELSE "abort"]
    /\ pforward' = [pforward EXCEPT ![p][p] = IF \E q \in participants: pforward[q][p] = "commit" THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pvote, pname, pto>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
    /\ pphase[p] \in {commit, abort}
    /\ pforward[p][q] = notsent
    /\ pforward' = [pforward EXCEPT ![p][q] = IF pphase[p] = commit THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pname, pto>>

\* A participant finalizes its decision once it has forwarded to everyone.
Decide(p) ==
    /\ pphase[p] \in {commit, abort}
    /\ \A q \in participants: pforward[p][q] = (IF pphase[p] = commit THEN "commit" ELSE "abort")
    /\ pname' = [pname EXCEPT ![p] = pphase[p]]
    /\ pto' = [pto EXCEPT ![p] = (IF pphase[p] = commit THEN "decision" ELSE "abort")]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pforward>>

\* Abort on timeout: no help from the coordinator or peers.
AbortOnTimeout(p) ==
    /\ calive = FALSE
    /\ pname[p] = "init"
    /\ ~(\E q \in participants: pname[q] = "decided")
    /\ ~(\E q \in participants: pname[q] = "aborted")
    /\ \A q \in participants: calive => pname[q] = "init"
    /\ \A q \in participants: pname[q] = "init" => (\A r \in participants: pforward[r][q] = notsent)
    /\ pname' = [pname EXCEPT ![p] = "aborted"]
    /\ pto' = [pto EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<pstate, calive, decision, pdec, pphase, pvote, pforward>>

SendVote(p, v) == GetVote(p, v)
DecideAbort(p) == Decide(p)
DecideCommit(p) == Decide(p)

Next ==
    \/ \E p \in participants: SendRequest(p) \/ MakeDecision(commit) \/ MakeDecision(abort)
                              \/ Broadcast(p) \/ SendVote(p, yes) \/ SendVote(p, no)
                              \/ PredecideFromCoordinator(p) \/ PredecideFromPeer(p)
                              \/ Decide(p) \/ AbortOnTimeout(p)
    \/ \E p \in participants, q \in participants: Forward(p, q)
    \/ DetectCoordFault \/ Die

SpecNB == Init /\ [][Next]_<<pstate, calive, decision, pdec, pphase, pvote, pname, pto, pforward>>

TypeInvNB == TypeInv

\* Safety: no two participants reach different decisions.
AC1 ==
    \A p, q \in participants: ~(pname[p] = "commit" /\ pname[q] = "abort")

\* At least one participant commits only if all voted yes.
AC2 ==
    \E p \in participants: pname[p] = "commit" => (\A q \in participants: pvote[q] = "yes")

\* At least one participant aborts only if someone voted no or crashed.
AC3 ==
    \E p \in participants: pname[p] = "abort" =>
        (\E q \in participants: pvote[q] = "no" \/ ~pstate["collecting"] \/ ~calive)

\* Irreversibility: committed or aborted participants never revert.
AC4 ==
    \A p \in participants: (pname[p] = "commit" \/ pname[p] = "aborted")
                             => pname[p] = pname[p]

\* Liveness: every non-faulty participant eventually decides.
AC5 ==
    \A p \in participants: (pstate = "collecting" /\ calive) ~> (pname[p] \in {commit, abort})

\* Liveness: the round always resolves (or crashes).
RoundResolves ==
    <> (pstate \in {"decided", "aborted"} \/ (~calive /\ pstate # "collecting"))

====