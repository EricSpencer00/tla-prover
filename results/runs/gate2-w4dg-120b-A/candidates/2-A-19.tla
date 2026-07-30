---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decid, faulty, voted, sent, pdec, pbroadcast, pdecision, pdriving, ptable

vars == <<pstate, alive, decid, faulty, voted, sent, pdec, pbroadcast, pdecision, pdriving, ptable>>

Range(f) == {f[p] : p \in participants}

\* The forwarding table records, for each participant, every participant it has sent
\* a pre-decision to and the decision it sent, plus the decision it has itself
\* received (stored at its own index).
Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decid = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> undecided]
    /\ sent = [p \in participants |-> FALSE]
    /\ pdec = [p \in participants |-> notsent]
    /\ pbroadcast = [p \in participants |-> FALSE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ pdriving = [p \in participants |-> undecided]
    /\ ptable = [p \in participants |-> [q \in participants |-> notsent]]

TypeInvNB ==
    /\ pstate \in [participants -> {undecided, commit, abort}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decid \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> {undecided, yes, no}]
    /\ sent \in [participants -> BOOLEAN]
    /\ pdec \in [participants -> {notsent, yes, no}]
    /\ pbroadcast \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pdriving \in [participants -> {undecided, commit, abort}]
    /\ ptable \in [participants -> [participants -> {notsent, commit, abort}]]

Coordinator == CHOOSE p \in participants : TRUE

\* The coordinator collects votes, decides, and broadcasts the result.
SendRequest ==
    /\ alive[Coordinator] = TRUE
    /\ pdriving[Coordinator] = undecided
    /\ pdriving' = [pdriving EXCEPT ![Coordinator] = waiting]
    /\ UNCHANGED <<pstate, alive, decid, faulty, voted, sent, pdec,
                   pbroadcast, pdecision, ptable>>

CollectVote(p) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ sent[p] = FALSE
    /\ pdriving[p] = waiting
    /\ \E v \in {yes, no} : voted' = [voted EXCEPT ![p] = v]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, alive, decid, faulty, pdec, pbroadcast,
                   pdecision, pdriving, ptable>>

\* Detects a participant that failed to vote; not a crash.
AbortOnVote(p) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ sent[p] = FALSE
    /\ voted[p] = no
    /\ pstate' = [pstate EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, decid, faulty, voted, sent, pdec, pbroadcast,
                   pdecision, pdriving, ptable>>

DetectFault ==
    /\ alive[Coordinator] = TRUE
    /\ decid[Coordinator] = undecided
    /\ \E p \in participants : sent[p] = FALSE /\ voted[p] = no
    /\ decid' = [decid EXCEPT ![Coordinator] = abort]
    /\ UNCHANGED <<pstate, alive, faulty, voted, sent, pdec, pbroadcast,
                   pdecision, pdriving, ptable>>

MakeDecision ==
    /\ alive[Coordinator] = TRUE
    /\ decid[Coordinator] = undecided
    /\ \A p \in participants : sent[p] = TRUE => voted[p] = yes
    /\ decid' = [decid EXCEPT ![Coordinator] = commit]
    /\ UNCHANGED <<pstate, alive, faulty, voted, sent, pdec, pbroadcast,
                   pdecision, pdriving, ptable>>

BroadcastDecision ==
    /\ alive[Coordinator] = TRUE
    /\ decid[Coordinator] # undecided
    /\ \A p \in participants : pbroadcast[p] = FALSE
    /\ pbroadcast' = [p \in participants |-> IF alive[p] = TRUE THEN TRUE ELSE pbroadcast[p]]
    /\ pdecision' = [p \in participants |-> IF alive[p] = TRUE THEN decid[Coordinator] ELSE pdecision[p]]
    /\ UNCHANGED <<pstate, alive, decid, faulty, voted, sent, pdec,
                   pdriving, ptable>>

\* Receiving a coordinator broadcast is a pre-decision, not a final one.
PreDecideCoord(p) ==
    /\ alive[p] = TRUE
    /\ pdec[p] = notsent
    /\ pbroadcast[p] = TRUE
    /\ pdec' = [pdec EXCEPT ![p] = pdecision[p]]
    /\ UNCHANGED <<pstate, alive, decid, faulty, voted, sent, pbroadcast,
                   pdecision, pdriving, ptable>>

PreDecideForward(p, q) ==
    /\ alive[p] = TRUE
    /\ pdec[p] = notsent
    /\ ptable[q][p] # notsent
    /\ pdec' = [pdec EXCEPT ![p] = ptable[q][p]]
    /\ UNCHANGED <<pstate, alive, decid, faulty, voted, sent, pbroadcast,
                   pdecision, pdriving, ptable>>

\* Forwarding happens before a participant finalizes.
Forward(p, q) ==
    /\ alive[p] = TRUE
    /\ pdec[p] # notsent
    /\ ptable[p][q] = notsent
    /\ ptable' = [ptable EXCEPT ![p][q] = IF pdec[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<pstate, alive, decid, faulty, voted, sent, pdec,
                   pbroadcast, pdecision, pdriving>>

Decide(p) ==
    /\ alive[p] = TRUE
    /\ pdec[p] # notsent
    /\ \A q \in participants : q # p => ptable[p][q] # notsent
    /\ pstate' = [pstate EXCEPT ![p] = IF pdec[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<alive, decid, faulty, voted, sent, pdec,
                   pbroadcast, pdecision, pdriving, ptable>>

\* A participant aborts once the coordinator is dead and no live path exists.
AbortOnTimeout(p) ==
    /\ alive[p] = TRUE
    /\ pstate[p] = undecided
    /\ alive[Coordinator] = FALSE
    /\ ~(pbroadcast[p] = TRUE \/ (pbroadcast[p] = FALSE /\ Range(ptable[p]) \subseteq {commit, abort}))
    /\ \A q \in participants : faulty[q] = FALSE => pstate[q] \in {undecided, commit}
    /\ \A q \in participants : faulty[q] = TRUE => pstate[q] = undecided
    /\ pstate' = [pstate EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, decid, faulty, voted, sent, pdec,
                   pbroadcast, pdecision, pdriving, ptable>>

Die(p) ==
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, decid, voted, sent, pdec, pbroadcast,
                   pdecision, pdriving, ptable>>

Next ==
    \/ SendRequest \/ DetectFault \/ MakeDecision \/ BroadcastDecision
    \/ \E p \in participants : CollectVote(p) \/ AbortOnVote(p) \/ PreDecideCoord(p)
                               \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
    \/ \E p, q \in participants : PreDecideForward(p, q) \/ Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : CollectVote(p))
    /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants : PreDecideCoord(p))
    /\ WF_vars(\E p \in participants : \E q \in participants : PreDecideForward(p, q))
    /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))

\* Agreement: no two participants reach different decisions.
Agreement ==
    \A p, q \in participants : (pstate[p] = commit) => (pstate[q] # abort)

CommitValidity == (commit \in Range(pstate)) => (\A p \in participants : voted[p] = yes)

AbortValidity ==
    (abort \in Range(pstate)) =>
        \/ (\E p \in participants : voted[p] = no)
        \/ (\E p \in participants : faulty[p] = TRUE)
        \/ (faulty[Coordinator] = TRUE)

Irreversibility == \A p \in participants : (pstate[p] \in {commit, abort}) => (pstate[p] = pstate[p])

AllDecidedOrFailed == <>(\A p \in participants : pstate[p] \in {commit, abort} \/ faulty[p] = TRUE)

Decided == <>(\A p \in participants : pstate[p] \in {commit, abort} \/ faulty[p] = TRUE)

====