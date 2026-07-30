---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, dec, faulty, voted, req, rv, bc, d, fwd

vars == <<vote, alive, dec, faulty, voted, req, rv, bc, d, fwd>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ dec \in {undecided, commit, abort}
    /\ faulty \in BOOLEAN
    /\ voted \in [participants -> BOOLEAN]
    /\ req \in {waiting, yes, no}
    /\ rv \in [participants -> {yes, no, undecided}]
    /\ bc \in [participants \cup {"coord"} -> {waiting, commit, abort}]
    /\ d \in [participants -> {undecided, commit, abort}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ dec = undecided
    /\ faulty = FALSE
    /\ voted = [p \in participants |-> FALSE]
    /\ req = waiting
    /\ rv = [p \in participants |-> undecided]
    /\ bc = [p \in participants \cup {"coord"} |-> waiting]
    /\ d = [p \in participants |-> undecided]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
    /\ alive["coord"] /\ req = waiting /\ req' = yes
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, rv, bc, d, fwd>>

GetVote(p) ==
    /\ alive["coord"] /\ alive[p] /\ req \in {yes, no}
    /\ ~ voted[p] /\ vote' = [vote EXCEPT ![p] = req]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, dec, faulty, req, rv, bc, d, fwd>>

VoteAbort(p) ==
    /\ alive[p] /\ vote[p] = no /\ dec = undecided
    /\ dec' = abort
    /\ UNCHANGED <<vote, alive, faulty, voted, req, rv, bc, d, fwd>>

Detect ==
    /\ alive["coord"] /\ ~ alive["coord"] /\ dec = undecided
    /\ bc' = [bc EXCEPT !["coord"] = abort]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, d, fwd>>

MakeDecision ==
    /\ alive["coord"] /\ dec = undecided
    /\ \A p \in participants : vote[p] = yes
    /\ dec' = commit
    /\ UNCHANGED <<vote, alive, faulty, voted, req, rv, bc, d, fwd>>

Broadcast ==
    /\ alive["coord"] /\ dec \in {commit, abort}
    /\ \A p \in participants : bc[p] = waiting
    /\ bc' = [p \in participants |-> dec]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, d, fwd>>

Die ==
    /\ alive["coord"] /\ ~ faulty /\ faulty' = TRUE
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ UNCHANGED <<vote, dec, voted, req, rv, bc, d, fwd>>

PreDecideCoord(p) ==
    /\ alive[p] /\ d[p] = undecided
    /\ bc[p] = commit /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = commit]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, bc, d>>

PreDecideFwd(p) ==
    /\ alive[p] /\ d[p] = undecided
    /\ \E q \in participants : fwd[q][p] \in {commit, abort} /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants : fwd[q][p] \in {commit, abort}][p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, bc, d>>

Forward(p) ==
    /\ alive[p] /\ fwd[p][p] \in {commit, abort}
    /\ \E q \in participants :
         /\ q # p
         /\ alive[q]
         /\ fwd[p][q] = notsent
         /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, bc, d>>

Decide(p) ==
    /\ alive[p] /\ d[p] = undecided
    /\ \A q \in participants : fwd[p][q] = fwd[p][p]
    /\ d' = [d EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, bc, fwd>>

DecideAbort ==
    /\ ~ alive["coord"] /\ ~ faulty
    /\ \A p \in participants : bc[p] = waiting
    /\ \A q \in participants : alive[q] => \A p \in participants : fwd[p][q] = notsent
    /\ \E p \in participants : alive[p] /\ d[p] = undecided
    /\ d' = [p \in participants |->
                IF alive[p] /\ d[p] = undecided THEN abort ELSE d[p]]
    /\ UNCHANGED <<vote, alive, dec, faulty, voted, req, rv, bc, fwd>>

DieP(p) ==
    /\ alive[p] /\ ~ faulty
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, dec, faulty, voted, req, rv, bc, d, fwd>>

NextNB ==
    \/ SendReq \/ Detect \/ MakeDecision \/ Broadcast \/ Die
    \/ \E p \in participants : GetVote(p) \/ VoteAbort(p) \/ PreDecideCoord(p)
                            \/ PreDecideFwd(p) \/ Forward(p) \/ Decide(p) \/ DieP(p)
    \/ DecideAbort

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(\E p \in participants : GetVote(p))
    /\ WF_vars(\E p \in participants : PreDecideCoord(p) \/ PreDecideFwd(p))
    /\ WF_vars(\E p \in participants : Forward(p))

AC1 == \A p, q \in participants : ~(d[p] = commit /\ d[q] = abort)
AC2 == commit \in {d[p] : p \in participants} => (\A p \in participants : vote[p] = yes)
AC3 == abort \in {d[p] : p \in participants} =>
          \/ \E p \in participants : vote[p] = no
          \/ \E p \in participants : ~ alive[p]
          \/ faulty
AC4 == \A p \in participants : (d[p] = commit \/ d[p] = abort) ~> (d[p] = commit \/ d[p] = abort)
AC3Live == <>(\A p \in participants : d[p] # undecided \/ faulty \/ ~ alive["coord"])
AC5 == \A p \in participants : (alive[p] /\ d[p] = undecided) ~> (d[p] # undecided)

====