---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, psentVote,
         coordSentReq, coordVote, coordSentDecision,
         coordDecision, coordAlive, coordFaulty

vars == <<pvote, palive, pdecision, pfaulty, psentVote,
          coordSentReq, coordVote, coordSentDecision,
          coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecision \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ psentVote \in [participants -> BOOLEAN]
    /\ coordSentReq \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSentDecision \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecision = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ psentVote = [p \in participants |-> FALSE]
    /\ coordSentReq = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordSentReq[p]
    /\ coordSentReq' = [coordSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordVote, coordSentDecision, coordDecision, coordFaulty>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ /\A q \in participants: coordSentReq[q]
       /\ coordVote[p] = waiting
       /\ psentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordSentReq, coordSentDecision, coordDecision, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ /\A q \in participants: coordSentReq[q]
       /\ coordVote[p] = waiting
       /\ ~palive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ /\A p \in participants: coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants: coordVote[p] = yes
                          THEN commit ELSE abort
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordSentReq, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision, coordDecision>>

SendVote(p) ==
    /\ palive[p]
    /\ coordSentReq[p]
    /\ ~psentVote[p]
    /\ psentVote' = [psentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, palive, pdecision, pfaulty,
                  coordSentReq, coordVote, coordSentDecision,
                  coordDecision, coordAlive, coordFaulty>>

AbortOnNoVote(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ psentVote[p]
    /\ pvote[p] = no
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision,
                  coordDecision, coordAlive, coordFaulty>>

AbortOnRequestTimeout(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ ~coordSentReq[p]
    /\ ~coordAlive
    /\ pdecision' = [pdecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision,
                  coordDecision, coordAlive, coordFaulty>>

DecideFromBroadcast(p) ==
    /\ palive[p]
    /\ pdecision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ pdecision' = [pdecision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED <<pvote, palive, pfaulty, psentVote,
                  coordSentReq, coordVote, coordSentDecision,
                  coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pvote, pdecision, psentVote,
                  coordSentReq, coordVote, coordSentDecision,
                  coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ MakeDecision
    \/ CoordDie
    \/ \E p \in participants:
        \/ SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p)
        \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnNoVote(p)
        \/ AbortOnRequestTimeout(p) \/ DecideFromBroadcast(p)
        \/ ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(MakeDecision)
        /\ WF_vars(CoordDie)
        /\ \A p \in participants: WF_vars(SendVote(p))
        /\ \A p \in participants: WF_vars(DecideFromBroadcast(p))

Agreement == \A p1, p2 \in participants:
                 (pdecision[p1] = commit) => (pdecision[p2] # abort)

CommitValid == \A p \in participants: pdecision[p] = commit => \A q \in participants: pvote[q] = yes

AbortValid == \A p \in participants: pdecision[p] = abort =>
                  (\E q \in participants: pvote[q] = no \/ pfaulty[q] \/ coordFaulty)

Irreversible == \A p \in participants:
                    /\ (pdecision[p] = commit) ~> (pdecision[p] = abort)
                    /\ (pdecision[p] = abort) ~> (pdecision[p] = commit)

DecideOrFault ==
    <>(\A p \in participants: pdecision[p] # undecided \/ pfaulty[p]) \/ <>coordFaulty

====