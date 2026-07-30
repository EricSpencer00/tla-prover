---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* For readability only; these are the values in the writer's forwarding table.
Received == {notsent, commit, abort}

VARIABLES pstate, alive, decision, faulty, voteSent, coordState

CoordStates == [req: {waiting, yes, no}, phase: {idle, collecting, decided},
                dec: {none, commit, abort}, alive: BOOLEAN, faulty: BOOLEAN]

Vars == <<pstate, alive, decision, faulty, voteSent, coordState>>

TypeOKNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in CoordStates

InitNB ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = [req |-> waiting, phase |-> idle, dec |-> none,
                   alive |-> TRUE, faulty |-> FALSE]

\* The coordinator decides and broadcasts like in the base protocol.
DecideBroadcast ==
  /\ coordState.alive
  /\ ~coordState.faulty
  /\ coordState.phase = collecting
  /\ \A p \in participants : voteSent[p]
  /\ coordState.dec' = IF \A p \in participants : pstate[p] = yes
                        THEN commit ELSE abort
  /\ coordState.phase' = decided
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState.phase = decided
  /\ decision' = [decision EXCEPT ![p] = coordState.dec]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState>>

PreDecideFromPeer(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision[q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[q]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState>>

Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ decision[p] # notsent
  /\ decision[q] = notsent
  /\ decision' = [decision EXCEPT ![q] = decision[p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants : decision[q] = decision[p]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordState>>

AbortOnCoordinatorCrash(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordState.alive
  /\ coordState.faulty
  /\ \A q \in participants : decision[q] \in {notsent, undecided}
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, coordState>>

NextNB ==
  \/ DecideBroadcast
  \/ \E p \in participants :
       \/ PreDecideFromCoord(p)
       \/ AbortOnCoordinatorCrash(p)
       \/ Decide(p)
       \/ Die(p)
       \/ \E q \in participants : PreDecideFromPeer(p, q) \/ Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_Vars
  /\ WF_Vars([p \in participants |-> PreDecideFromCoord(p)])
  /\ WF_Vars([p \in participants |-> \E q \in participants : PreDecideFromPeer(p, q)])
  /\ WF_Vars([p \in participants |-> \E q \in participants : Forward(p, q)])
  /\ WF_Vars([p \in participants |-> Decide(p)])
  /\ WF_Vars([p \in participants |-> AbortOnCoordinatorCrash(p)])

\* Mutual exclusion: once a participant commits no other can abort, and vice versa.
AgreementNB == ~( \E p, q \in participants :
                    /\ decision[p] = commit /\ decision[q] = abort)

CommitValidity == (\E p \in participants : decision[p] = commit) =>
                  (\A p \in participants : pstate[p] = yes)

AbortValidity == (\E p \in participants : decision[p] = abort) =>
                 ( \E p \in participants : pstate[p] = no \/ faulty[p] \/ coordState.faulty )

IrreversibilityNB == \A p \in participants :
      /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
      /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])
      /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordState>>

TypeInvNB == TypeOKNB /\ AgreementNB /\ CommitValidity /\ AbortValidity /\ IrreversibilityNB

AllDecided == \A p \in participants : decision[p] # undecided

DecideOrCrash ==
  (AllDecided \/ (\E p \in participants : faulty[p])) \/ coordState.faulty

DecideEventually ==
  \A p \in participants :
    (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====