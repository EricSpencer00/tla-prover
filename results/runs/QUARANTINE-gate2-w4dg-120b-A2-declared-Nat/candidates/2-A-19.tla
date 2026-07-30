---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec, fwd

vars == <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec, fwd>>

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordReq \in BOOLEAN
    /\ coordVote \in {yes, no, undecided}
    /\ coordBc \in BOOLEAN
    /\ coordDec \in {commit, abort}
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

CoordAlive ==
    /\ \A p \in participants : alive[p]
    /\ ~faulty[CHOOSE p \in participants : TRUE]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordReq = FALSE
    /\ coordVote = undecided
    /\ coordBc = FALSE
    /\ coordDec = commit
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendReq(p) ==
    /\ alive[p]
    /\ ~voteSent[p]
    /\ coordReq = FALSE
    /\ coordReq' = TRUE
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, alive, faulty, coordReq, coordVote, coordBc, coordDec, fwd>>

GetVote(p) ==
    /\ coordReq = TRUE
    /\ coordVote = undecided
    /\ vote[p] /= undecided
    /\ coordVote' = vote[p]
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordBc, coordDec, fwd>>

CoordFault ==
    /\ coordReq = TRUE
    /\ coordVote = undecided
    /\ CoordAlive
    /\ faulty' = [faulty EXCEPT ![CHOOSE p \in participants : TRUE] = TRUE]
    /\ alive' = [p \in participants |-> ~faulty[p]]
    /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote, coordBc, coordDec, fwd>>

MakeDecision ==
    /\ coordReq = TRUE
    /\ coordBc = FALSE
    /\ coordVote # undecided
    /\ coordDec' = coordVote
    /\ coordBc' = TRUE
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, fwd>>

Broadcast(p) ==
    /\ coordBc = TRUE
    /\ alive[p]
    /\ coordDec' = IF coordDec = commit THEN commit ELSE abort
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, fwd>>

SendVote(p) ==
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<decision, alive, faulty, coordReq, coordVote, coordBc, coordDec, fwd>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, coordReq, coordVote, coordBc, coordDec, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A r \in participants : ~coordBc \/ ~alive[r]
    /\ \A r \in participants : ~faulty[r] => \A q \in participants : fwd[r][q] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, coordReq, coordVote, coordBc, coordDec, fwd>>

PreDecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBc = TRUE
    /\ fwd[p][p] = notsent
    /\ fwd' = [fwd EXCEPT ![p][p] = coordDec]
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec>>

PreDecideFwd(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E r \in participants :
         /\ r # p
         /\ fwd[r][p] # notsent
         /\ fwd[p][p] = notsent
         /\ fwd' = [fwd EXCEPT ![p][p] = fwd[r][p]]
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec>>

Forward(p, q) ==
    /\ alive[p]
    /\ fwd[p][p] # notsent
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
    /\ UNCHANGED <<vote, decision, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote, coordBc, coordDec, fwd>>

Die(p) ==
    /\ alive[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote, coordBc, coordDec, fwd>>

NextNB ==
    \/ \E p \in participants : SendReq(p) \/ GetVote(p) \/ Broadcast(p)
                             \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
                             \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ Die(p)
    \/ CoordFault
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ MakeDecision

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ \A p \in participants : WF_vars(SendReq(p))
    /\ \A p \in participants : SF_vars(SendVote(p))
    /\ \A p \in participants : SF_vars(PreDecideCoord(p))
    /\ \A p \in participants : SF_vars(PreDecideFwd(p))
    /\ \A p \in participants : SF_vars(Decide(p))

PropNB1 ==
    \A p \in participants :
        \/ decision[p] = commit
        \/ decision[p] = abort
        \/ decision[p] = undecided

PropNB2 ==
    \A p \in participants :
        decision[p] = commit => (\A q \in participants : vote[q] = yes)

PropNB3 ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faulty[q]
            \/ ~alive[CHOOSE q \in participants : TRUE]

PropNB4 ==
    \A p \in participants :
        decision[p] = commit => decision[p] = commit
        decision[p] = abort  => decision[p] = abort

PropNB5 ==
    \A p \in participants :
        (alive[p] /\ decision[p] = undecided) ~> (decision[p] = commit \/ decision[p] = abort)

====