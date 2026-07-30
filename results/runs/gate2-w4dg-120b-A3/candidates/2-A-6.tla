---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {}
ASSUME yes # no
ASSUME commit # abort
ASSUME notsent # yes

ASSUME waiting #yes

VARIABLES pstate, vote, alive, decision, faulty, voteSent, forwarded

TypeInvNB ==
    /\ pstate \in [participants -> {waiting, yes, no}]
    /\ vote \in {yes, no, undecided}
    /\ alive \in [participants \cup {"coordinator"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \subseteq participants \cup {"coordinator"}
    /\ voteSent \subseteq participants
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [p \in participants |-> waiting]
    /\ vote = undecided
    /\ alive = [p \in participants \cup {"coordinator"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ voteSent = {}
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ "coordinator" \notin faulty
    /\ pstate' = [p \in participants |-> IF pstate[p] = waiting THEN yes ELSE pstate[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarded>>

GetVote ==
    /\ "coordinator" \notin faulty
    /\ vote = undecided
    /\ \E p \in participants : p \in voteSent /\ pstate[p] # waiting /\ vote' = pstate[p]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, forwarded>>

DetectCoordFault ==
    /\ "coordinator" \notin faulty
    /\ vote = undecided
    /\ \E p \in participants \ voteSent : pstate[p] = waiting
    /\ faulty' = {"coordinator"}
    /\ UNCHANGED <<pstate, vote, alive, decision, voteSent, forwarded>>

\* All other broadcast actions are unchanged from ACP-SB, so they are
\* paraphrased here without comment rather than re-explained in full detail.

MakeDecision ==
    /\ "coordinator" \notin faulty
    /\ vote \in {yes, no}
    /\ \E d \in {commit, abort} : decision' = [p \in participants |-> d]
    /\ UNCHANGED <<pstate, vote, alive, faulty, voteSent, forwarded>>

Broadcast ==
    /\ "coordinator" \notin faulty
    /\ \E d \in {commit, abort} : decision' = [p \in participants |-> d]
    /\ UNCHANGED <<pstate, vote, alive, faulty, voteSent, forwarded>>

\* The new participant actions: pre-decision from coordinator, pre-decision
\* from forwarding, forwarding, non-blocking decide, abort on timeout.

PreDecideFromCoord ==
    /\ "coordinator" \notin faulty
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ decision[p] \in {commit, abort}
         /\ forwarded[p][p] = notsent
         /\ forwarded' = [forwarded EXCEPT ![p][p] = decision[p]]
    /\ UNCHANGED <<pstate, vote, alive, decision, faulty, voteSent>>

PreDecideFromForward ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ \E q \in participants :
              /\ q # p
              /\ forwarded[q][p] # notsent
              /\ forwarded[p][p] = notsent
              /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
    /\ UNCHANGED <<pstate, vote, alive, decision, faulty, voteSent>>

Forward ==
    /\ \E p, q \in participants :
         /\ alive[p]
         /\ forwarded[p][p] # notsent
         /\ forwarded[p][q] = notsent
         /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<pstate, vote, alive, decision, faulty, voteSent>>

Decide ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ \A q \in participants : forwarded[p][q] # notsent
         /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<pstate, vote, alive, faulty, voteSent, forwarded>>

AbortOnTimeout ==
    /\ "coordinator" \in faulty
    /\ \E p \in participants :
         /\ alive[p]
         /\ decision[p] = undecided
         /\ (\A q \in participants : forwarded[q][p] = notsent)
         /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pstate, vote, alive, faulty, voteSent, forwarded>>

Die ==
    /\ \E p \in participants \cup {"coordinator"} :
         /\ p # "coordinator" \/ vote = undecided
         /\ p \notin faulty
         /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<pstate, vote, alive, decision, voteSent, forwarded>>

SendVote ==
    /\ \E p \in participants :
         /\ alive[p]
         /\ pstate[p] \in {yes, no}
         /\ p \notin voteSent
         /\ voteSent' = voteSent \cup {p}
    /\ UNCHANGED <<pstate, vote, alive, decision, faulty, forwarded>>

CoordAbort ==
    /\ "coordinator" \notin faulty
    /\ vote = undecided
    /\ \A p \in participants : p \notin voteSent
    /\ decision' = [p \in participants |-> abort]
    /\ UNCHANGED <<pstate, vote, alive, faulty, voteSent, forwarded>>

CoordDie ==
    /\ "coordinator" \notin faulty
    /\ faulty' = faulty \cup {"coordinator"}
    /\ UNCHANGED <<pstate, vote, alive, decision, voteSent, forwarded>>

Next ==
    \/ SendRequest \/ GetVote \/ DetectCoordFault \/ MakeDecision \/ Broadcast
    \/ PreDecideFromCoord \/ PreDecideFromForward \/ Forward \/ Decide
    \/ AbortOnTimeout \/ Die \/ SendVote \/ CoordAbort \/ CoordDie

SpecNB == Init /\ [][Next]_<<pstate, vote, alive, decision, faulty, voteSent, forwarded>>

\* Safety: no two participants disagree on the outcome.
Agreement == \A p, q \in participants : (p # q /\ decision[p] # undecided /\ decision[q] # undecided) => decision[p] = decision[q]

CommitValidity ==
    \E p \in participants : decision[p] = commit => \A q \in participants : pstate[q] = yes

AbortValidity ==
    \E p \in participants : decision[p] = abort =>
        \/ \E q \in participants : pstate[q] = no
        \/ \E q \in participants : q \in faulty
        \/ "coordinator" \in faulty

Irrevocable ==
    \A p \in participants : decision[p] # undecided => (\A d \in {commit, abort} : (decision[p] = d) ~> (decision[p] = d))

\* Liveness: every non-faulty participant eventually decides.
EventualDecision == \A p \in participants : (p \notin faulty) ~> (decision[p] # undecided)

====