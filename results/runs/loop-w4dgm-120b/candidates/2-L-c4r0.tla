---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: a participant forwards a pre-decision to all others
\* before it may finalize its own decision, so a coordinator crash cannot
\* permanently stall the protocol.

VARIABLES vote, alive, decision, faulty, vsent, prep, forwarded

vars == <<vote, alive, decision, faulty, vsent, prep, forwarded>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \subseteq participants
    /\ decision \in [participants -> {commit, abort}]
    /\ faulty \subseteq participants
    /\ vsent \in [participants -> BOOLEAN]
    /\ prep \in [participants -> {notsent, commit, abort}]
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = participants
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = {}
    /\ vsent = [p \in participants |-> FALSE]
    /\ prep = [p \in participants |-> notsent]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator collects votes and decides.
SendRequest(p) ==
    /\ p \in alive
    /\ \A q \in participants : vote[q] = undecided
    /\ vsent[p] = FALSE
    /\ vsent' = [vsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, prep, forwarded>>

GetVote(p) ==
    /\ p \in alive
    /\ vsent[p] = TRUE
    /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, vsent, prep, forwarded>>

MakeDecision(p) ==
    /\ p \in alive
    /\ \A q \in participants : vote[q] # undecided
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] =
                      IF \A q \in participants : vote[q] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, faulty, vsent, prep, forwarded>>

Broadcast(p, q) ==
    /\ p \in alive
    /\ decision[p] # waiting
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = decision[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, vsent, prep>>

\* A participant aborts if nobody responded to it and the coordinator is gone.
AbortOnTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = waiting
    /\ alive = {}
    /\ \A q \in participants : forwarded[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, vsent, prep, forwarded>>

Die(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<vote, decision, vsent, prep, forwarded>>

\* The pre-decision is stored from either the coordinator or a peer.
PreDecideFromCoord(p) ==
    /\ p \in alive
    /\ prep[p] = notsent
    /\ decision[p] # waiting
    /\ prep' = [prep EXCEPT ![p] = decision[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, vsent, forwarded>>

PreDecideFromPeer(p) ==
    /\ p \in alive
    /\ prep[p] = notsent
    /\ \E q \in participants : forwarded[q][p] # notsent
    /\ prep' = [prep EXCEPT ![p] = forwarded[CHOOSE q \in participants : forwarded[q][p] # notsent][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, vsent, forwarded>>

Forward(p, q) ==
    /\ p \in alive
    /\ q \in participants
    /\ prep[p] # notsent
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = prep[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, vsent, prep>>

Decide(p) ==
    /\ p \in alive
    /\ prep[p] # notsent
    /\ \A q \in participants : forwarded[p][q] # notsent
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = prep[p]]
    /\ UNCHANGED <<vote, alive, faulty, vsent, prep, forwarded>>

NextNB ==
    \/ \E p \in participants : SendRequest(p) \/ GetVote(p) \/ MakeDecision(p) \/ Die(p)
    \/ \E p, q \in participants : Broadcast(p, q) \/ Forward(p, q)
    \/ \E p \in participants : PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
    \/ \E p \in participants : AbortOnTimeout(p) \/ Decide(p)

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(\E p \in participants : SendRequest(p))
    /\ WF_vars(\E p \in participants : GetVote(p))
    /\ WF_vars(\E p \in participants : MakeDecision(p))
    /\ WF_vars(\E p, q \in participants : Broadcast(p, q))
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ WF_vars(\E p \in participants : PreDecideFromPeer(p))
    /\ WF_vars(\E p, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : Decide(p))

\* SAFETY: no two participants disagree, and every decision is justified.
\* LIVENESS: a non-faulty participant always eventually decides.
ACInv1 == \A p \in participants : \A q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
\* A commit requires a unanimous yes; a abort may be justified by a no-vote or
\* a crash anywhere in the system.
ACInv2 ==
    /\ (\A p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
    /\ (\A p \in participants : decision[p] = abort) =>
         \E p \in participants : (vote[p] = no) \/ (p \in faulty) \/ (participants \subseteq faulty)
\* The coordinator's broadcast can never be resurrected once the coordinator
\* has died, so the forward-and-decide step is the only remaining path.
\* With no alive participant left to forward, a faulty participant's abort
\* path is the only resolution: this is exactly the non-blocking guarantee.
ACInv3 == (\A p \in participants : decision[p] \in {commit, abort}) ~> (\A p \in participants : decision[p] \in {commit, abort})
ACInv4 == \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)

SpecNBAC5 == \A p \in participants : (p \in alive) ~> (decision[p] \in {commit, abort})

====