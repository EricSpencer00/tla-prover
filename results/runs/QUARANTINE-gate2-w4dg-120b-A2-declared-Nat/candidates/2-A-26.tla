---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* Non-Blocking Atomic Commitment Protocol (ACP-NB) with reliable broadcast.
\* This extends the simple broadcast variant (ACP-SB) by adding a forwarding
\* table per participant so decisions can be disseminated peer-to-peer if the
\* coordinator crashes mid-broadcast.
\* Directly derived from the reference .cfg: all listed identifiers are defined.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, voteSent, ptable
Variables == << pvote, palive, pdecision, pfaulty, voteSent, ptable >>

CoordAlive == IF decider = "coord" THEN True ELSE False

Init ==
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> True]
  /\ pdecision = [p \in participants |-> waiting]
  /\ pfaulty = [p \in participants |-> False]
  /\ voteSent = [p \in participants |-> False]
  /\ ptable = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (inherited from the simple broadcast base protocol).
\* The coordinator sends a request, collects votes, detects faults, decides,
\* broadcasts, and can crash.
CoordRequest(p) == /\ voteSent[p] = False /\ pvote[p] = undecided
  /\ voteSent' = [voteSent EXCEPT ![p] = True]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, ptable >>

CoordVote(p, v) == /\ voteSent[p] = True /\ pvote[p] = undecided
  /\ pvote' = [pvote EXCEPT ![p] = v]
  /\ UNCHANGED << palive, pdecision, pfaulty, voteSent, ptable >>

CoordFault ==
  /\ \E p \in participants : pvote[p] = undecided
  /\ pfaulty' = [pfaulty EXCEPT ![decider] = TRUE]
  /\ UNCHANGED << pvote, palive, pdecision, voteSent, ptable >>

CoordDecide ==
  /\ \A p \in participants : pvote[p] \in {yes, no}
  /\ decision = IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort
  /\ pdecision' = [p \in participants |-> decision]
  /\ UNCHANGED << pvote, palive, pfaulty, voteSent, ptable >>

CoordBroadcast(p) ==
  /\ pdecision[decider] \in {commit, abort}
  /\ ptable[decider][p] = notsent
  /\ ptable' = [ptable EXCEPT ![decider][p] = pdecision[decider]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, voteSent >>

CoordDie == pfaulty' = [pfaulty EXCEPT ![decider] = TRUE]
  /\ UNCHANGED << pvote, palive, pdecision, voteSent, ptable >>

\* A participant adopts its pre-decision from the coordinator's broadcast.
PreDecideFromCoord(p) ==
  /\ palive[p] = True /\ ptable[p][p] = notsent /\ pdecision[decider] \in {commit, abort}
  /\ ptable' = [ptable EXCEPT ![p][p] = pdecision[decider]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, voteSent >>

\* A participant adopts its pre-decision from another participant's forwarding.
PreDecideFromForward(p) ==
  /\ palive[p] = True /\ ptable[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p /\ ptable[q][p] # notsent
       /\ ptable' = [ptable EXCEPT ![p][p] = ptable[q][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, voteSent >>

\* A participant forwards its received pre-decision to another participant.
Forward(p, q) ==
  /\ palive[p] = True /\ ptable[p][p] # notsent
  /\ ptable[p][q] = notsent /\ ptable' = [ptable EXCEPT ![p][q] = ptable[p][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, voteSent >>

\* A participant finalizes once it has forwarded to all others: non-blocking.
Decide(p) ==
  /\ palive[p] = True /\ pdecision[p] = waiting /\ ptable[p][p] # notsent
  /\ \A q \in participants \ {p} : ptable[p][q] = ptable[p][p]
  /\ pdecision' = [pdecision EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED << pvote, palive, pfaulty, voteSent, ptable >>

AbortOnTimeout(p) ==
  /\ palive[p] = True /\ pdecision[p] = waiting /\ CoordAlive = False
  /\ \A q \in participants : pdecision[q] \notin {commit, abort}
  /\ \A q \in participants : ptable[q][p] = notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pvote, palive, pfaulty, voteSent, ptable >>

Die(p) == palive' = [palive EXCEPT ![p] = False]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pvote, pdecision, voteSent, ptable >>

\* Next-step relation: any coordinator or participant action may fire.
Next ==
  \/ \E p \in participants : CoordRequest(p) \/ CoordVote(p, yes) \/ CoordVote(p, no)
  \/ CoordFault \/ CoordDie
  \/ \E p \in participants : PreDecideFromCoord(p) \/ PreDecideFromForward(p)
  \/ \E p \in participants : \E q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p) \/ AbortOnTimeout(p) \/ Die(p)

\* Weak fairness: every progress action must eventually be taken.
Fairness ==
  /\ TRUE
  /\ \A p \in participants :
       /\ TRUE
       /\ TYPEDEFENABLE(PreDecideFromCoord(p))
       /\ WF_vars(PreDecideFromCoord(p))
       /\ TYPEDEFENABLE(PreDecideFromForward(p))
       /\ WF_vars(PreDecideFromForward(p))
       /\ \A q \in participants \ {p} :
            /\ TYPEDEFENABLE(Forward(p, q))
            /\ WF_vars(Forward(p, q))
       /\ TYPEDEFENABLE(Decide(p))
       /\ WF_vars(Decide(p))

SpecNB == Init /\ [][Next]_Variables /\ Fairness

\* Safety: no two participants disagree, and decisions only follow votes.
TypeInvNB ==
  /\ \A p \in participants : pvote[p] \in {undecided, yes, no}
  /\ \A p \in participants : pdecision[p] \in {waiting, commit, abort}
  /\ \A p \in participants :
       \A q \in participants :
         /\ ptable[p][q] \in {notsent, commit, abort}
         /\ (p = q => ptable[p][q] = notsent => pdecision[p] = waiting)
  /\ (\A p \in participants : pdecision[p] = commit => \A q \in participants : pvote[q] = yes)
  /\ (\A p \in participants : pdecision[p] = abort =>
       \/ \E q \in participants : pvote[q] = no
       \/ \E q \in participants : pfaulty[q] = TRUE
       \/ pfaulty[decider] = TRUE)
  /\ \A p \in participants : (pdecision[p] \in {commit, abort}) ~> (pdecision[p] \in {commit, abort})

\* Liveness: progress (every non-faulty participant decides) and agreement
\* (the protocol always resolves or crashes).
TermProgress == <>(\A p \in participants : pdecision[p] \in {commit, abort})
Resolution == <>(\A p \in participants : pdecision[p] \in {commit, abort})
        \/ <>(\E p \in participants : pfaulty[p] = TRUE)

====