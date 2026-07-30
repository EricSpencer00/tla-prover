---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, votesent, prep, bradied, bradvice
          , mdecision, mbroadcast, mdead, mforwarded

vars == <<vote, alive, decision, faulty, votesent, prep, bradied, bradvice
           , mdecision, mbroadcast, mdead, mforwarded>>

\* The forwarding table maps every destination participant to the declared decision
\* (or notsent). It records both the pre-decision a participant has assimilated and
\* what it has forwarded on to others.
FwdTable == [participants -> {notsent, commit, abort}]

TypeOK ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ votesent \in [participants -> BOOLEAN]
    /\ prep \in [participants -> BOOLEAN]
    /\ bradied \in BOOLEAN
    /\ bradvice \in {commit, abort}
    /\ mdecision \in {undecided, commit, abort}
    /\ mbroadcast \in [participants -> {undecided, commit, abort}]
    /\ mdead \in BOOLEAN
    /\ mforwarded \in [participants -> FwdTable]

Init ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ votesent = [p \in participants |-> FALSE]
    /\ prep = [p \in participants |-> FALSE]
    /\ bradied = FALSE
    /\ bradvice = commit
    /\ mdecision = undecided
    /\ mbroadcast = [p \in participants |-> undecided]
    /\ mdead = FALSE
    /\ mforwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator's voting/broadcasting actions are inherited from the base
\* simple broadcast protocol; they are unmodified here.
SendRequest(p) ==
    /\ alive[p] /\ vote[p] = undecided /\ ~votesent[p]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, prep, bradied, bradvice
                   , mdecision, mbroadcast, mdead, mforwarded>>

GetVote(p, v) ==
    /\ alive[p] /\ vote[p] = undecided /\ votesent[p]
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<alive, decision, faulty, votesent, prep, bradied, bradvice
                   , mdecision, mbroadcast, mdead, mforwarded>>

DetectFault ==
    /\ ~mdead
    /\ \E p \in participants : alive[p] /\ vote[p] = undecided /\ ~votesent[p]
    /\ mdead' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, prep, bradied
                   , bradvice, mdecision, mbroadcast, mforwarded>>

MakeDecision ==
    /\ ~mdead
    /\ \A p \in participants : vote[p] # undecided
    /\ mdecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, prep, bradied
                   , bradvice, mbroadcast, mdead, mforwarded>>

Broadcast(p) ==
    /\ ~mdead /\ alive[p]
    /\ mdecision # undecided
    /\ mbroadcast[p] = undecided
    /\ mbroadcast' = [mbroadcast EXCEPT ![p] = mdecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, prep, bradied
                   , bradvice, mdecision, mdead, mforwarded>>

Die(p) ==
    /\ alive[p] /\ ~faulty[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, votesent, prep, bradied, bradvice
                   , mdecision, mbroadcast, mdead, mforwarded>>

\* A decision may reach a participant either directly from the coordinator or
\* via peer forwarding; either path writes the participant's own forwarding entry.
PreDecideFromCoord(p) ==
    /\ alive[p] /\ decision[p] = undecided /\ mbroadcast[p] # undecided
    /\ decision' = [decision EXCEPT ![p] = mbroadcast[p]]
    /\ mforwarded' = [mforwarded EXCEPT ![p][p] = mbroadcast[p]]
    /\ prep' = [prep EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, votesent, bradied, bradvice
                   , mdecision, mbroadcast, mdead>>

PreDecideFromFwd(p, q) ==
    /\ alive[p] /\ decision[p] = undecided
    /\ mforwarded[q][p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = mforwarded[q][p]]
    /\ mforwarded' = [mforwarded EXCEPT ![p][p] = mforwarded[q][p]]
    /\ prep' = [prep EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, votesent, bradied, bradvice
                   , mdecision, mbroadcast, mdead>>

\* Forwarding happens one destination at a time, and only after a pre-decision
\* has been recorded locally.
Forward(p, q) ==
    /\ alive[p] /\ p # q
    /\ mforwarded[p][p] \in {commit, abort}
    /\ mforwarded[p][q] = notsent
    /\ mforwarded' = [mforwarded EXCEPT ![p][q] = mforwarded[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, prep, bradied
                   , bradvice, mdecision, mbroadcast, mdead>>

\* A participant finalizes only once it has forwarded its pre-decision to everyone.
Decide(p) ==
    /\ alive[p] /\ ~decision[p] # undecided
    /\ \A q \in participants : mforwarded[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = mforwarded[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, votesent, prep, bradied, bradvice
                   , mdecision, mbroadcast, mdead, mforwarded>>

AbortOnCoordTimeout(p) ==
    /\ alive[p] /\ decision[p] = undecided
    /\ mdead
    /\ \A q \in participants : alive[q] => mbroadcast[q] = undecided
    /\ \A q \in participants : faulty[q] => \A r \in participants : mforwarded[q][r] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent, prep, bradied, bradvice
                   , mdecision, mbroadcast, mdead, mforwarded>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants, v \in {yes, no} : GetVote(p, v)
    \/ DetectFault
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ \E p \in participants : Die(p)
    \/ \E p \in participants : PreDecideFromCoord(p)
    \/ \E p \in participants, q \in participants : PreDecideFromFwd(p, q)
    \/ \E p \in participants, q \in participants : Forward(p, q)
    \/ \E p \in participants : Decide(p)
    \/ \E p \in participants : AbortOnCoordTimeout(p)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
    /\ \A p \in participants :
         /\ WF_vars(\E q \in participants : PreDecideFromFwd(p, q))
         /\ WF_vars(\E q \in participants : Forward(p, q))
         /\ WF_vars(Decide(p))
    /\ WF_vars(\E p \in participants : AbortOnCoordTimeout(p))

\* Safety properties.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)
AC3 == \A p \in participants : decision[p] = abort =>
           (\E q \in participants : vote[q] = no \/ faulty[q] \/ bradied)
AC4 == \A p \in participants : decision[p] # undecided => decision[p] = decision[p]

\* Liveness: every non-faulty participant eventually decides, which the simple
\* broadcast variant cannot guarantee.
AC5 == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> decision[p] # undecided

TypeInvNB == TypeOK
Properties == AC5

====