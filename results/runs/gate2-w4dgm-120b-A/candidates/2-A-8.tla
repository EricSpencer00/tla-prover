---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd

vars == <<vote, al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

Phases == {waiting, "decided"}

\* fwd[p][q] tracks what participant p has forwarded to q (not-sent, commit, or abort):
\* fwd[p][p] additionally stores the pre-decision p itself received.
FwdVals == {notsent, commit, abort}

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ al \in [participants -> {"alive", "crashed"}]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \subseteq participants
  /\ sentVote \subseteq participants
  /\ req \in {"none", "pending"}
  /\ gvote \in {yes, no, undecided}
  /\ broadcast \subseteq participants
  /\ cstate \in {"alive", "crashed"}
  /\ cvote \in {yes, no, undecided}
  /\ cdecision \in {commit, abort, undecided}
  /\ cphase \in Phases
  /\ fwd \in [participants -> [participants -> FwdVals]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ al = [p \in participants |-> "alive"]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sentVote = {}
  /\ req = "none"
  /\ gvote = undecided
  /\ broadcast = {}
  /\ cstate = "alive"
  /\ cvote = undecided
  /\ cdecision = undecided
  /\ cphase = "waiting"
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator collects votes, makes a decision, and broadcasts it.
SendReq ==
  /\ cstate = "alive"
  /\ req = "none"
  /\ cphase = "waiting"
  /\ req' = "pending"
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

GetVote(p) ==
  /\ cstate = "alive"
  /\ req = "pending"
  /\ vote[p] = undecided
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<vote, al, decision, faulty, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

CoordDetectFault(p) ==
  /\ cstate = "alive"
  /\ vote[p] = undecided
  /\ al[p] = "crashed"
  /\ p \notin faulty
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, al, decision, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

\* The coordinator decides only after hearing from every participant.
Decide ==
  /\ cstate = "alive"
  /\ req = "pending"
  /\ sentVote = participants
  /\ gvote' = IF \A p \in participants : vote[p] = yes THEN yes ELSE no
  /\ cvote' = gvote
  /\ cdecision' = IF gvote = yes THEN commit ELSE abort
  /\ cphase' = "decided"
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, broadcast, cstate, fwd>>

Broadcast ==
  /\ cstate = "alive"
  /\ cphase = "decided"
  /\ broadcast # participants
  /\ broadcast' = participants
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, gvote, cstate, cvote, cdecision, cphase, fwd>>

CoordDie ==
  /\ cstate = "alive"
  /\ cstate' = "crashed"
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, gvote, broadcast, cvote, cdecision, cphase, fwd>>

Vote(p) ==
  /\ al[p] = "alive"
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<vote, al, decision, faulty, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

AbortOnVote(p) ==
  /\ al[p] = "alive"
  /\ vote[p] = undecided
  /\ p \in sentVote
  /\ vote' = [vote EXCEPT ![p] = no]
  /\ UNCHANGED <<al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

\* A participant receives the coordinator's broadcast and stores it as its pre-decision.
PreDecideFromCoord(p) ==
  /\ al[p] = "alive"
  /\ decision[p] = undecided
  /\ cstate = "alive"
  /\ p \in broadcast
  /\ fwd' = [fwd EXCEPT ![p][p] = cdecision]
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase>>

\* A participant receives a forwarded decision from another participant.
PreDecideFromFwd(p) ==
  /\ al[p] = "alive"
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase>>

\* Forward a pre-decision to a participant from which it has not yet been forwarded.
Forward(p, q) ==
  /\ al[p] = "alive"
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, al, decision, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase>>

DecideP(p) ==
  /\ al[p] = "alive"
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants \ {p} : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = IF fwd[p][p] = commit THEN commit ELSE abort]
  /\ UNCHANGED <<vote, al, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

\* Timeout abort when the coordinator is dead and no broadcast or forward is available.
AbortOnTimeout(p) ==
  /\ al[p] = "alive"
  /\ decision[p] = undecided
  /\ cstate = "crashed"
  /\ broadcast = {}
  /\ \A q \in participants \ {p} : (q \in faulty) => (fwd[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, al, faulty, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

Die(p) ==
  /\ al[p] = "alive"
  /\ al' = [al EXCEPT ![p] = "crashed"]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sentVote, req, gvote, broadcast, cstate, cvote, cdecision, cphase, fwd>>

Next ==
  \/ SendReq \/ Decide \/ Broadcast \/ CoordDie
  \/ \E p \in participants :
       \/ GetVote(p) \/ CoordDetectFault(p) \/ Vote(p) \/ AbortOnVote(p)
       \/ PreDecideFromCoord(p) \/ PreDecideFromFwd(p) \/ DecideP(p)
       \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

\* Weak fairness on every participant progress action, plus coordinator progress,
\* with death transitions excluded from fairness.
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : Vote(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants : DecideP(p))
  \/ WF_vars(\E p \in participants : Die(p))
  /\ WF_vars(Decide)
  /\ WF_vars(Broadcast)

\* Safety: no two participants reach different decisions.
AC1 ==
  \A p, q \in participants :
    ~(decision[p] = commit /\ decision[q] = abort)

\* Safety: a commit is backed by unanimity.
AC2 ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Safety: an abort is always justified.
AC3 ==
  \A p \in participants : decision[p] = abort =>
    \E q \in participants : vote[q] = no \/ q \in faulty \/ cstate = "crashed"

\* Safety: a decision is permanent.
AC4 ==
  \A p \in participants :
    (decision[p] # undecided) ~> (decision[p] = decision[p])

\* Liveness: every non-faulty participant eventually decides.
AC5 == \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

TypeInvNB == TypeOK
====