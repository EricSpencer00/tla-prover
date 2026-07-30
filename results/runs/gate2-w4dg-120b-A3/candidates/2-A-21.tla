---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBrd, coordDec, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

\* Forwarding table: entry (p, q) records what participant p has forwarded to q:
\* notsent, or the pre-decision p received and is propagating.
Fwd(p) == [q \in participants |-> fwd[p][q]]

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in BOOLEAN
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in BOOLEAN
  /\ coordBrd \in [participants -> BOOLEAN]
  /\ coordDec \in {none, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = TRUE
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = FALSE
  /\ coordBrd = [p \in participants |-> FALSE]
  /\ coordDec = none
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions (same as in ACP-SB):
SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote, coordBrd,
                coordDec, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ coordVote = FALSE
  /\ vote[p] = yes
  /\ voteSent[p] = FALSE
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ coordVote' = coordVote \/ TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordBrd,
                coordDec, coordAlive, coordFaulty, fwd>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordVote = FALSE
  /\ vote[p] = no
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ coordVote' = coordVote \/ TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordBrd,
                coordDec, coordAlive, coordFaulty, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordVote
  /\ coordDec = none
  /\ coordDec' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBrd, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDec # none
  /\ ~coordBrd[p]
  /\ coordBrd' = [coordBrd EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordDec, coordAlive, coordFaulty, fwd>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBrd, coordDec, fwd>>

\* Participant actions: the new reliable-broadcast actions are the last four.
SendVote(p) ==
  /\ alive
  /\ ~voteSent[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordReq, coordVote,
                coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~\E q \in participants : coordBrd[q]
  /\ ~\E d \in participants, q \in participants :
        (~faulty[d]) /\ fwd[d][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

\* A participant that is still alive stores the coordinator's broadcast as its
\* own pre-decision in its forwarding table.
PreDecideCoord(p) ==
  /\ alive
  /\ Fwd(p)[p] = notsent
  /\ coordBrd[p]
  /\ Fwd' = [Fwd EXCEPT ![p][p] = coordDec]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

\* A participant that is still alive stores a forwarded pre-decision from another
\* participant into its own forwarding table.
PreDecideForward(p) ==
  /\ alive
  /\ Fwd(p)[p] = notsent
  /\ \E d \in participants : Fwd(d)[p] # notsent
  /\ \E d \in participants : Fwd' = [Fwd EXCEPT ![p][p] = Fwd(d)[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

\* Forward the pre-decision this participant just received to another one.
Forward(p, q) ==
  /\ alive
  /\ Fwd(p)[p] # notsent
  /\ p # q
  /\ Fwd(p)[q] = notsent
  /\ Fwd' = [Fwd EXCEPT ![p][q] = Fwd(p)[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

Decide(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ \A q \in participants : Fwd(p)[q] # notsent
  /\ decision' = [decision EXCEPT ![p] = Fwd(p)[p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive
  /\ alive' = FALSE
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote,
                coordBrd, coordDec, coordAlive, coordFaulty, fwd>>

Next ==
  \/ SendRequest \/ MakeDecision \/ CoordDie
  \/ \E p \in participants :
       SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ PreDecideCoord(p)
       \/ PreDecideForward(p) \/ Decide(p) \/ Die(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ Broadcast(p)

\* Forwarding is a participant's own local bookkeeping and can never be undone,
\* so even if a participant crashes it never reverts its forwarded entries.
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p) \/ PreDecideCoord(p)
                                \/ PreDecideForward(p) \/ Forward(p, CHOOSE d \in participants : TRUE))
  /\ WF_vars(\E p \in participants : Broadcast(p) \/ Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p) \/ Die(p))

\* Agreement: no two participants can commit and abort at once.
AC1 == ~(\E p \in participants, q \in participants :
            decision[p] = commit /\ decision[q] = abort)

\* Commit validity: a commit can only happen on a unanimous yes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* Abort validity: an abort traces to a no vote or a crash.
AC3 == (\E p \in participants : decision[p] = abort) =>
         (\E p \in participants : vote[p] = no \/ faulty[p]) \/ coordFaulty

\* Irreversibility: commit and abort are final once taken.
AC4 == \A p \in participants : \A d \in {commit, abort} :
         (decision[p] = d) ~> (decision[p] = d)

\* Termination: everybody decides or someone crashes.
AC3Liveness == <>(\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ coordFaulty

\* Every non-faulty participant eventually decides, enabled by reliable forwarding.
AC5 == \A p \in participants : (alive /\ ~faulty[p]) ~> (decision[p] # undecided)

PROPERTIES == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3Liveness /\ AC5

====