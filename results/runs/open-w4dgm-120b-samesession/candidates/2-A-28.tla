---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, as, req, v, bc, pdecided, fwd

vars == <<pstate, alive, decision, faulty, voteSent, as, req, v, bc, pdecided, fwd>>

TypeInvNB ==
    /\ pstate \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {commit, abort, waiting}
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ as \in {yes, no, undecided}
    /\ req \in BOOLEAN
    /\ v \in {yes, no, undecided}
    /\ bc \in BOOLEAN
    /\ pdecided \in [participants -> {commit, abort, waiting}]
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pstate = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = waiting
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ as = undecided
    /\ req = FALSE
    /\ v = undecided
    /\ bc = FALSE
    /\ pdecided = [p \in participants |-> waiting]
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorInit ==
    /\ ~req
    /\ req' = TRUE
    /\ v' = undecided
    /\ decision' = waiting
    /\ bc' = FALSE
    /\ UNCHANGED <<pstate, alive, faulty, voteSent, as, pdecided, fwd>>

SendVote(p) ==
    /\ req
    /\ alive[p]
    /\ ~faulty[p]
    /\ ~voteSent[p]
    /\ pstate' = [pstate EXCEPT ![p] = as]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, as, req, v, bc, pdecided, fwd>>

Decide ==
    /\ req
    /\ v = undecided
    /\ v' = as
    /\ decision' = (IF as = yes THEN commit ELSE abort)
    /\ bc' = TRUE
    /\ UNCHANGED <<pstate, alive, faulty, voteSent, as, req, pdecided, fwd>>

BroadcastDecide(p, q) ==
    /\ bc
    /\ alive[p]
    /\ alive[q]
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = decision]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, as, req, v, bc, pdecided>>

PreDecideCoord(p) ==
    /\ alive[p]
    /\ pdecided[p] = waiting
    /\ bc
    /\ pdecided' = [pdecided EXCEPT ![p] = decision]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, as, req, v, bc, fwd>>

PreDecideFwd(p) ==
    /\ alive[p]
    /\ pdecided[p] = waiting
    /\ \E q \in participants : alive[q] /\ fwd[q][p] # notsent
    /\ pdecided' = [pdecided EXCEPT ![p] = CHOOSE d \in {commit, abort} : \E q \in participants : fwd[q][p] = d]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, as, req, v, bc, fwd>>

DecideNB(p) ==
    /\ alive[p]
    /\ pdecided[p] # waiting
    /\ \A q \in participants : q = p \/ alive[q] => fwd[p][q] # notsent
    /\ pstate' = [pstate EXCEPT ![p] = pdecided[p]]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, as, req, v, bc, pdecided, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ pstate[p] = undecided
    /\ ~alive[CHOOSE q \in participants : TRUE]
    /\ (\A q \in participants : ~alive[q] => fwd[q][p] = notsent)
    /\ v = undecided
    /\ decision = waiting
    /\ pstate' = [pstate EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, decision, faulty, voteSent, as, req, v, bc, pdecided, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, decision, voteSent, as, req, v, bc, pdecided, fwd>>

Next ==
    \/ CoordinatorInit
    \/ Decide
    \/ \E p \in participants : SendVote(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ DecideNB(p) \/ AbortOnTimeout(p) \/ Die(p)
    \/ \E p, q \in participants : BroadcastDecide(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(DecideNB(p))

AC1 ==
    \A p1, p2 \in participants : (pstate[p1] = commit /\ pstate[p2] = abort) => FALSE

AC2 ==
    \A p \in participants : pstate[p] = commit => \A q \in participants : pstate[q] # undecided

AC3 ==
    \A p \in participants :
        pstate[p] = abort =>
            (\E q \in participants : pstate[q] = no) \/ (\E q \in participants : faulty[q]) \/ ~alive[CHOOSE q \in participants : TRUE]

AC4 ==
    \A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) ~> (pstate[p] = commit \/ pstate[p] = abort)

AC5 ==
    \A p \in participants :
        (alive[p] /\ pstate[p] = undecided) ~> (pstate[p] = commit \/ pstate[p] = abort)

====