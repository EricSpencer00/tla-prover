---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, dec, coordDec, coordVotes, coordAlive, coordFaulty
VARIABLES forwarding, pDecide, pDecFrom

vars == <<vote, dec, coordDec, coordVotes, coordAlive, coordFaulty,
          forwarding, pDecide, pDecFrom>>

TypeOKNB ==
  /\ vote \in [participants -> {no, yes, undecided}]
  /\ dec \in [participants -> {commit, abort, undecided}]
  /\ coordDec \in {commit, abort, undecided}
  /\ coordVotes \in 0..Cardinality(participants)
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ pDecide \in [participants -> {notsent, commit, abort}]
  /\ pDecFrom \in [participants -> {notsent, commit, abort}]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ dec = [p \in participants |-> undecided]
  /\ coordDec = undecided
  /\ coordVotes = 0
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
  /\ pDecide = [p \in participants |-> notsent]
  /\ pDecFrom = [p \in participants |-> notsent]

Alive(p) == coordAlive /\ vote[p] # undecided

\* Forwarding is the twist: a participant first stores the pre-decision it
\* receives from the coordinator, then redistributes that pre-decision to
\* every other participant, and only finalizes once all have been distributed.
DecidePreDecNB(p) ==
  /\ coordAlive
  /\ coordDec # undecided
  /\ forwarding[p][p] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDec]
  /\ pDecide' = [pDecide EXCEPT ![p] = coordDec]
  /\ UNCHANGED <<vote, dec, coordDec, coordVotes, coordAlive, coordFaulty,
                 pDecFrom>>

DecideFromForwardNB(p) ==
  /\ \E q \in participants :
       /\ forwarding[q][p] # notsent
       /\ forwarding[p][p] = notsent
       /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
       /\ pDecide' = [pDecide EXCEPT ![p] = forwarding[q][p]]
  /\ UNCHANGED <<vote, dec, coordDec, coordVotes, coordAlive, coordFaulty,
                 pDecFrom>>

ForwardDecisionNB(p, q) ==
  /\ p # q
  /\ forwarding[p][p] # notsent
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<vote, dec, coordDec, coordVotes, coordAlive, coordFaulty,
                 pDecide, pDecFrom>>

DecideNB(p) ==
  /\ forwarding[p][p] # notsent
  /\ \A q \in participants : q # p => forwarding[p][q] # notsent
  /\ dec[p] = undecided
  /\ dec' = [dec EXCEPT ![p] = pDecide[p]]
  /\ UNCHANGED <<vote, coordDec, coordVotes, coordAlive, coordFaulty,
                 forwarding, pDecide, pDecFrom>>

AbortNB(p) ==
  /\ dec[p] = undecided
  /\ ((dec[p] = undecided /\ ~Alive(p)) \/ coordFaulty)
  /\ \A q \in participants : forwarding[q][p] = notsent
  /\ dec' = [dec EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, coordDec, coordVotes, coordAlive, coordFaulty,
                 forwarding, pDecide, pDecFrom>>

DieNB(p) ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordVotes' = 0
  /\ coordFaulty' = TRUE
  /\ dec' = [q \in participants |-> IF q = p THEN abort ELSE dec[q]]
  /\ UNCHANGED <<vote, coordDec, forwarding, pDecide, pDecFrom>>

\* The base actions from the simple-broadcast protocol are retained verbatim;
\* they are still available to the coordinator.
SendCoordRequestNB(p) ==
  /\ coordAlive
  /\ coordDec = undecided
  /\ coordVotes = 0
  /\ vote[p] = undecided
  /\ coordVotes' = (coordVotes + 1) % (Cardinality(participants) + 1)
  /\ UNCHANGED <<vote, dec, coordDec, coordAlive, coordFaulty,
                 forwarding, pDecide, pDecFrom>>

SendVoteNB(p) ==
  /\ coordAlive
  /\ coordVotes > 0
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ pDecFrom' = [pDecFrom EXCEPT ![p] = IF v = yes THEN commit ELSE abort]
  /\ UNCHANGED <<dec, coordDec, coordVotes, coordAlive, coordFaulty,
                 forwarding, pDecide>>

GetCoordVoteNB(p) ==
  /\ coordAlive
  /\ coordVotes > 0
  /\ vote[p] # undecided
  /\ coordVotes' = (coordVotes + 1) % (Cardinality(participants) + 1)
  /\ UNCHANGED <<vote, dec, coordDec, coordAlive, coordFaulty,
                 forwarding, pDecide, pDecFrom>>

CoordMakeDecisionNB ==
  /\ coordAlive
  /\ coordVotes = 0
  /\ \A p \in participants : vote[p] = yes
  /\ coordDec' = commit
  /\ UNCHANGED <<vote, dec, coordVotes, coordAlive, coordFaulty,
                 forwarding, pDecide, pDecFrom>>

CoordBroadcastNB(p) ==
  /\ coordAlive
  /\ coordDec # undecided
  /\ forwarding[p][p] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDec]
  /\ UNCHANGED <<vote, dec, coordDec, coordVotes, coordAlive, coordFaulty,
                 pDecide, pDecFrom>>

CoordAbortNB(p) ==
  /\ coordAlive
  /\ coordDec = undecided
  /\ vote[p] = no
  /\ coordFaulty' = TRUE
  /\ dec' = [q \in participants |-> IF q = p THEN abort ELSE dec[q]]
  /\ UNCHANGED <<vote, coordDec, coordVotes, coordAlive,
                 forwarding, pDecide, pDecFrom>>

NextNB ==
  \/ \E p \in participants : DecidePreDecNB(p) \/ DecideFromForwardNB(p)
  \/ \E p \in participants, q \in participants : ForwardDecisionNB(p, q)
  \/ \E p \in participants : DecideNB(p) \/ AbortNB(p) \/ DieNB(p)
  \/ \E p \in participants : SendCoordRequestNB(p) \/ SendVoteNB(p)
  \/ \E p \in participants : GetCoordVoteNB(p) \/ CoordBroadcastNB(p)
  \/ CoordMakeDecisionNB \/ \E p \in participants : CoordAbortNB(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : DecidePreDecNB(p))
  /\ WF_vars(\E p \in participants : DecideFromForwardNB(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : ForwardDecisionNB(p, q))
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : SendVoteNB(p))
  /\ WF_vars(\E p \in participants : GetCoordVoteNB(p))
  /\ WF_vars(\E p \in participants : CoordBroadcastNB(p))

\* A committed decision is only possible when everybody voted yes.
CommitValidNB == \A p \in participants : dec[p] = commit => \A q \in participants : vote[q] = yes

AbortValidNB ==
  \A p \in participants :
    dec[p] = abort => (coordFaulty \/ vote[p] = no \/ coordDec # undecided)

IrreversibleNB == \A p \in participants : (dec[p] # undecided) ~> (dec[p] # undecided)

DecideSomeNB == \E p \in participants : dec[p] # undecided

\* Every non-faulty participant eventually decides; this is what liveness
\* fails for in the simple-broadcast variant.
TerminateNB == \A p \in participants : (dec[p] = undecided /\ coordAlive) ~> (dec[p] # undecided)

TypeInvNB == TypeOKNB /\ CommitValidNB /\ AbortValidNB /\ IrreversibleNB

====