---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coord, coordAlive, coordFaulty, vote, alive, decision, dphase, gphase, fwd

Vars == <<coord, coordAlive, coordFaulty, vote, alive, decision,
          dphase, gphase, fwd>>

TypeInvNB ==
    /\ coord \in {yes, no, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ dphase \in [participants -> {waiting, commit, abort}]
    /\ gphase \in {waiting, yes, no}
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitCoord ==
    /\ coord = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

InitAll ==
    /\ InitCoord
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ dphase = [p \in participants |-> waiting]
    /\ gphase = waiting
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

PartDecide(p) == decision[p] # undecided

CoordSendReq ==
    /\ coordAlive
    /\ coord = undecided
    /\ coord' = no
    /\ UNCHANGED <<coordAlive, coordFaulty, vote, alive, decision,
                  dphase, gphase, fwd>>

CoordRecvVote(p) ==
    /\ coordAlive
    /\ coord = no
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, alive, decision,
                  dphase, gphase, fwd>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coord = no
    /\ vote[p] = no
    /\ coord' = no
    /\ UNCHANGED <<coordAlive, coordFaulty, vote, alive, decision,
                  dphase, gphase, fwd>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coord = no
    /\ \A p \in participants : vote[p] = yes
    /\ coord' = yes
    /\ UNCHANGED <<coordAlive, coordFaulty, vote, alive, decision,
                  dphase, gphase, fwd>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coord = yes
    /\ gphase = waiting
    /\ fwd[coord][p] = notsent
    /\ fwd' = [fwd EXCEPT ![coord][p] = commit]
    /\ gphase' = yes
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, decision,
                  dphase>>

CoordAbort(p) ==
    /\ coordAlive
    /\ coord = no
    /\ gphase = waiting
    /\ fwd' = [fwd EXCEPT ![coord][p] = abort]
    /\ gphase' = no
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, decision,
                  dphase>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coord, vote, alive, decision, dphase, gphase, fwd>>

PartSendVote(p) ==
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, alive, decision,
                  dphase, gphase, fwd>>

PartPreDecideCoord(p) ==
    /\ alive[p]
    /\ dphase[p] = waiting
    /\ fwd[coord][p] # notsent
    /\ dphase' = [dphase EXCEPT ![p] = fwd[coord][p]]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, decision,
                  gphase, fwd>>

PartPreDecideFwd(q, p) ==
    /\ alive[p]
    /\ dphase[p] = waiting
    /\ fwd[q][p] # notsent
    /\ dphase' = [dphase EXCEPT ![p] = fwd[q][p]]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, decision,
                  gphase, fwd>>

PartForward(p, q) ==
    /\ alive[p]
    /\ dphase[p] # waiting
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = dphase[p]]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, decision,
                  dphase, gphase>>

PartDecide(p) ==
    /\ alive[p]
    /\ dphase[p] # waiting
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = dphase[p]]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, dphase,
                  gphase, fwd>>

PartAbortTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants : fwd[coord][q] = notsent
    /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, alive, dphase,
                  gphase, fwd>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ dphase' = [dphase EXCEPT ![p] = abort]
    /\ UNCHANGED <<coord, coordAlive, coordFaulty, vote, gphase, fwd>>

Next ==
    \/ CoordSendReq
    \/ CoordBroadcast(NEXT(p \in participants))
    \/ CoordAbort(NEXT(p \in participants))
    \/ CoordDetectFault(NEXT(p \in participants))
    \/ CoordMakeDecision
    \/ CoordDie
    \/ PartSendVote(NEXT(p \in participants))
    \/ PartPreDecideCoord(NEXT(p \in participants))
    \/ PartPreDecideFwd(NEXT(q \in participants), NEXT(p \in participants))
    \/ PartDecide(NEXT(p \in participants))
    \/ PartAbortTimeout(NEXT(p \in participants))

SpecNB ==
    /\ InitAll
    /\ [][Next]_Vars
    /\ WF_Vars(PartPreDecideCoord(NEXT(p \in participants)))
    /\ WF_Vars(PartPreDecideFwd(NEXT(q \in participants), NEXT(p \in participants)))
    /\ WF_Vars(PartDecide(NEXT(p \in participants)))

DecisionBound ==
    \A p \in participants : decision[p] # undecided

CoordAliveOrFaulty == coordAlive \/ coordFaulty

PartDecidedOrFaulty ==
    \E p \in participants : decision[p] # undecided \/ ~alive[p]

Properties ==
    /\ DecisionBound \/ CoordAliveOrFaulty
    /\ PartDecidedOrFaulty

TerminatingParticipants ==
    \A p \in participants : PartPreDecideCoord(p) \/ PartPreDecideFwd(q, p)
                            \/ PartDecide(p) \/ PartAbortTimeout(p)

====