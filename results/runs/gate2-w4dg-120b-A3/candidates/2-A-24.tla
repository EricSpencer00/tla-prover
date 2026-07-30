---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME no == "no"
ASSUME yes == "yes"
ASSUME commit == "commit"
ASSUME abort == "abort"
ASSUME notsent == "not-sent"

VARIABLES participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable

vars == << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

TypeInvNB ==
    /\ participantVote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {yes, no, undecided}
    /\ coordDec \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ participantVote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordReq = waiting
    /\ coordVote = undecided
    /\ coordDec = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

SendReq ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = yes
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

GetVote(p) ==
    /\ coordAlive
    /\ coordReq # waiting
    /\ decision[p] = undecided
    /\ participantVote[p] = undecided
    /\ coordVote' = IF coordVote = undecided THEN participantVote[p] ELSE coordVote
    /\ participantVote' = [participantVote EXCEPT ![p] = coordReq]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << alive, decision, faulty, coordReq, coordDec, coordAlive, coordFaulty, forwardTable >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordVote = no
    /\ participantVote[p] = undecided
    /\ coordVote' = no
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordDec, coordAlive, coordFaulty, forwardTable >>

MakeDecision ==
    /\ coordAlive
    /\ coordVote # undecided
    /\ coordDec = undecided
    /\ coordDec' = IF coordVote = no THEN abort ELSE commit
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordAlive, coordFaulty, forwardTable >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = coordDec]
    /\ UNCHANGED << participantVote, alive, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

Die ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, forwardTable >>

PreDecideCoord(p) ==
    /\ coordAlive
    /\ decision[p] = undecided
    /\ forwardTable[p][p] = notsent
    /\ decision[p] # undecided
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = decision[p]]
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty >>

PreDecideForward(p, q) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forwardTable[p][p] = notsent
    /\ forwardTable[q][p] # notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = forwardTable[q][p]]
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty >>

Forward(p, q) ==
    /\ alive[p]
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED << participantVote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty >>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : forwardTable[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = forwardTable[p][p]]
    /\ UNCHANGED << participantVote, alive, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : decision[q] = undecided
    /\ \A q \in participants : \A r \in participants : forwardTable[r][q] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << participantVote, alive, faulty, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

DiePart(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << participantVote, decision, voteSent, coordReq, coordVote, coordDec, coordAlive, coordFaulty, forwardTable >>

Next ==
    \/ SendReq \/ Die \/ MakeDecision \/ Broadcast("p")
    \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ PreDecideCoord(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ DiePart(p)
    \/ \E p \in participants, q \in participants : PreDecideForward(p, q) \/ Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ TRUE

Coherent ==
    /\ \A p \in participants : decision[p] \in {undecided, commit, abort}
    /\ \A p \in participants : decision[p] = commit => participantVote[p] = yes
    /\ (\E p \in participants : decision[p] = commit) => \A q \in participants : participantVote[q] = yes
    /\ (\E p \in participants : decision[p] = abort) => (\E q \in participants : participantVote[q] = no \/ faulty[q]) \/ coordFaulty

AC3Hold == Coherent

AC5 == \A p \in participants : (decision[p] = undecided) ~> (decision[p] \in {commit, abort})

====