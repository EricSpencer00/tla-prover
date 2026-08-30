---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-blocking atomic commitment protocol based on reliable broadcast.  A  *)
(* participant first stores the pre-decision it receives, forwards it to the *)
(* other participants, and only then finalizes its own decision.  A         *)
(* participant may crash silently at any point.  No two participants ever     *)
(* commit and abort respectively.                                             *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, sent, coord, forwarded

vars == << pstate, alive, decision, faulty, sent, coord, forwarded >>

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN f[x] + SumF(f, S \ {x})

Messages == participants \X participants

TypeInv ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, waiting}]
    /\ faulty \subseteq participants
    /\ sent \in [participants -> BOOLEAN]
    /\ coord \in {waiting, commit, abort}
    /\ forwarded \in [participants -> [Messages -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> waiting]
    /\ faulty = {}
    /\ sent = [p \in participants |-> FALSE]
    /\ coord = waiting
    /\ forwarded = [p \in participants |-> [m \in Messages |-> notsent]]

\* Request: the coordinator asks every alive participant to vote.
Request ==
    /\ coord = waiting
    /\ \A p \in participants : alive[p]
    /\ coord' = waiting
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, forwarded >>

\* Vote: a live participant sends yes or no up to the coordinator.
Vote(p) ==
    /\ alive[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pstate, alive, decision, faulty, coord, forwarded >>

\* Crash: any participant (or the coordinator) may crash silently.
Crash(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << pstate, decision, sent, coord, forwarded >>

\* Decide: once every participant has voted and the coordinator is alive,
\* it decides commit iff all voted yes (uniform agreement), otherwise abort.
Decide ==
    /\ coord = waiting
    /\ \A p \in participants : sent[p]
    /\ \A p \in participants : alive[p]
    /\ coord' = IF \A p \in participants : pstate[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, forwarded >>

\* Broadcast: the coordinator (if alive) sends its decision to a participant.
Broadcast(p) ==
    /\ coord # waiting
    /\ alive[p]
    /\ forwarded[coord][<<coord, p>>] = notsent
    /\ forwarded' = [forwarded EXCEPT ![coord][<<coord, p>>] = coord]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coord >>

\* PreDecide: a participant stores the pre-decision the coordinator sent it.
PreDecide(p) ==
    /\ alive[p]
    /\ forwarded[p][<<coord, p>>] \in {commit, abort}
    /\ forwarded[p][<<p, p>>] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][<<p, p>>] = forwarded[p][<<coord, p>>]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coord >>

\* PreDecideFwd: a participant stores the pre-decision another participant
\* forwarded to it.
PreDecideFwd(p) ==
    /\ alive[p]
    /\ forwarded[p][<<p, p>>] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ forwarded[q][<<q, p>>] \in {commit, abort}
         /\ forwarded' = [forwarded EXCEPT ![p][<<p, p>>] = forwarded[q][<<q, p>>]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coord >>

\* Forward: a participant that holds a pre-decision forwards it to another
\* participant that has not yet received it.
Forward(p, q) ==
    /\ p # q
    /\ alive[p]
    /\ forwarded[p][<<p, p>>] \in {commit, abort}
    /\ forwarded[p][<<p, q>>] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][<<p, q>>] = forwarded[p][<<p, p>>]]
    /\ UNCHANGED << pstate, alive, decision, faulty, sent, coord >>

\* DecideP: once a participant has forwarded its pre-decision to everyone,
\* it finalizes that decision locally (irreversible).
DecideP(p) ==
    /\ alive[p]
    /\ forwarded[p][<<p, p>>] \in {commit, abort}
    /\ \A q \in participants : forwarded[p][<<p, q>>] = forwarded[p][<<p, p>>]
    /\ decision[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = forwarded[p][<<p, p>>]]
    /\ UNCHANGED << pstate, alive, sent, faulty, coord, forwarded >>

\* AbortT: an undecided participant aborts when the coordinator has died
\* and no one (alive or faulty) has propagated a pre-decision to it.
AbortT(p) ==
    /\ decision[p] = waiting
    /\ ~alive[coord]
    /\ \A q \in participants : forwarded[q][<<coord, p>>] = notsent
    /\ \A q \in participants : ~(\A r \in participants : forwarded[q][<<r, p>>] # notsent)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << pstate, alive, sent, faulty, coord, forwarded >>

Next ==
    \/ Request \/ Decide
    \/ \E p \in participants :
         \/ Vote(p) \/ Crash(p) \/ Broadcast(p) \/ PreDecide(p)
         \/ PreDecideFwd(p) \/ DecideP(p) \/ AbortT(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Request) /\ WF_vars(Decide)
    /\ \A p \in participants :
         /\ WF_vars(\E q \in participants : Forward(p, q))
         /\ WF_vars(PreDecide(p)) /\ WF_vars(PreDecideFwd(p))
         /\ WF_vars(DecideP(p)) /\ WF_vars(AbortT(p))

(* No two participants ever reach different decisions.                         *)
Agree ==
    \A p1, p2 \in participants :
        (decision[p1] = commit /\ decision[p2] = abort) => FALSE

(* A commit requires a unanimous yes vote from all participants.               *)
CommitValid ==
    (\E p \in participants : decision[p] = commit) =>
        (\A p \in participants : pstate[p] = yes)

(* An abort is only possible if a no vote, a faulty participant, or a faulty   *)
(* coordinator was actually present.                                           *)
AbortValid ==
    (\E p \in participants : decision[p] = abort) =>
        (\E p \in participants : pstate[p] = no) \/ (faulty # {}) \/ (~alive[coord])

Decided == \A p \in participants : decision[p] # waiting

(* A participant's decision is final: once decided it never changes again.     *)
DecideStays ==
    \A p \in participants :
        (decision[p] \in {commit, abort}) ~> (decision[p] = decision[p])

(* Every non-faulty participant eventually reaches a decision (commit or abort).*)
Terminating ==
    \A p \in participants :
        (p \notin faulty) ~> (decision[p] \in {commit, abort})

(* Strongly fair action set: either everybody decides or a fault surfaces.    *)
DecideOrCrash == Decided \/ (faulty # {})

Props == Agree /\ CommitValid /\ AbortValid

TypeInvNB == TypeInv

====