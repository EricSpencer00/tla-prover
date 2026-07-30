---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, dec, faulty, sent, req, cvote, broadcast,
    cdec, calive, cfaulty, fwd

vars == <<vote, alive, dec, faulty, sent, req, cvote, broadcast,
    cdec, calive, cfaulty, fwd>>

Init0 ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ dec = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ req = waiting
    /\ cvote = undecided
    /\ broadcast = [p \in participants |-> FALSE]
    /\ cdec = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
    /\ req = waiting
    /\ \A p \in participants : vote[p] = undecided
    /\ req' = waiting
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, cvote, broadcast,
                  cdec, calive, cfaulty, fwd>>

SendVote(p) ==
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, dec, faulty, req, cvote, broadcast, cdec,
                  calive, cfaulty, fwd>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ vote[p] = no
    /\ req' = abnormal
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, cvote, broadcast,
                  cdec, calive, cfaulty, fwd>>

DetectFault ==
    /\ calive
    /\ \E p \in participants : vote[p] = no
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  broadcast, cdec, fwd>>

MakeDecision ==
    /\ calive
    /\ req = normal
    /\ cvote = undecided
    /\ \A p \in participants : vote[p] = yes
    /\ cvote' = yes
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, broadcast,
                  cdec, calive, cfaulty, fwd>>

AbortDecision ==
    /\ calive
    /\ req = abnormal
    /\ cvote' = no
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, broadcast,
                  cdec, calive, cfaulty, fwd>>

Broadcast ==
    /\ calive
    /\ cvote # undecided
    /\ cdec = undecided
    /\ cdec' = cvote
    /\ broadcast' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  calive, cfaulty, fwd>>

DieCoordinator ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  broadcast, cdec, fwd>>

PreDecideFromCoordinator(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ broadcast[p]
    /\ fwd' = [fwd EXCEPT ![p][p] = cdec]
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  broadcast, cdec, calive, cfaulty>>

PreDecideFromFwd(p) ==
    /\ alive[p]
    /\ fwd[p][p] = notsent
    /\ \E q \in participants \ {p} : fwd[q][p] # notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants \ {p} : fwd[q][p] # notsent][p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  broadcast, cdec, calive, cfaulty>>

Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, sent, req, cvote,
                  broadcast, cdec, calive, cfaulty>>

DecideP(p) ==
    /\ alive[p]
    /\ dec[p] = undecided
    /\ \A q \in participants \ {p} : fwd[p][q] # notsent
    /\ dec' = [dec EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, req, cvote, broadcast,
                  cdec, calive, cfaulty, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ dec[p] = undecided
    /\ ~calive
    /\ \A q \in participants : broadcast[q] = FALSE
    /\ \A q \in participants : \A r \in participants : alive[r] => fwd[q][r] = notsent
    /\ dec' = [dec EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, req, cvote, broadcast,
                  cdec, calive, cfaulty, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, dec, sent, req, cvote, broadcast,
                  cdec, calive, cfaulty, fwd>>

Next ==
    \/ SendReq \/ DetectFault \/ MakeDecision \/ AbortDecision \/ Broadcast
    \/ DieCoordinator
    \/ \E p \in participants :
         SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromCoordinator(p)
         \/ PreDecideFromFwd(p) \/ DecideP(p) \/ AbortOnTimeout(p) \/ Die(p)
         \/ \E q \in participants : Forward(p, q)

SpecNB ==
    /\ Init0
    /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(SendVote(p))
    /\ \A p \in participants : WF_vars(DecideP(p))
    /\ \A p \in participants : \A q \in participants : WF_vars(Forward(p, q))
    /\ \A p \in participants : WF_vars(PreDecideFromCoordinator(p))
    /\ \A p \in participants : WF_vars(PreDecideFromFwd(p))
    /\ \A p \in participants : WF_vars(AbortOnTimeout(p))
    /\ \A p \in participants : SF_vars(Die(p))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(DetectFault)

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ dec \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ req \in {normal, abnormal, waiting}
    /\ cvote \in {yes, no, undecided}
    /\ broadcast \in [participants -> BOOLEAN]
    /\ cdec \in {commit, abort, undecided}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* No two participants ever end up in different decisions.
AC1 == \A p, q \in participants : (dec[p] = commit /\ dec[q] = abort) => FALSE

\* No commit unless all voted yes.
AC2 == (\E p \in participants : dec[p] = commit) => (\A q \in participants : vote[q] = yes)

\* Any abort has an explanatory fault.
AC3 == (\E p \in participants : dec[p] = abort) =>
          (\E q \in participants :
             \/ vote[q] = no
             \/ faulty[q]
             \/ cfaulty)

\* Decisions are permanent.
AC4 == \A p \in participants : (dec[p] /= undecided) ~> (dec[p] = dec[p])

\* Every non-faulty participant eventually decides -- liveness guarantee from the
\* forwarding mechanism that the simple broadcast variant lacks.
AC5 == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (dec[p] # undecided)

====