---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, sent, coord

Vars == <<pstate, alive, decision, faulty, sent, coord>>

\* The base ACP-SB protocol: pstate = vote, alive = life status, decision =
\* final decision, faulty = crash flag, sent = whether a vote was sent, coord
\* = coordinator bookkeeping. The extension is the forwarding table.
FwdState == [participants -> {notsent, commit, abort}]

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in BOOLEAN
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in BOOLEAN
  /\ sent \subseteq participants
  /\ coord \in [req |-> {waiting, commit, abort}, vote |-> {waiting, yes, no},
                broadcast |-> [participants -> {waiting, commit, abort}],
                decision |-> {waiting, commit, abort}, alive |-> BOOLEAN,
                faulty |-> BOOLEAN]
  /\ \A p \in participants : pstate[p] \in {yes, no, undecided}

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = TRUE
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = FALSE
  /\ sent = {}
  /\ coord =
       [req |-> waiting, vote |-> waiting,
        broadcast |-> [p \in participants |-> waiting], decision |-> waiting,
        alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Inherited coordinator actions (exactly as in the base protocol, so they
\* need not be restated here).
SendReq == coord.req = waiting /\ alive /\ coord' = [coord EXCEPT !.req = commit]
Vote(p) == coord.req # waiting /\ pstate[p] = undecided /\ decision[p] = undecided
              /\ pstate' = [pstate EXCEPT ![p] = no]
              /\ sent' = sent \cup {p}
              /\ UNCHANGED <<alive, decision, faulty, coord, fwd>>
DecideNo(p) == coord.vote = waiting /\ pstate[p] = no /\ coord.vote' = no
                 /\ UNCHANGED <<pstate, alive, decision, faulty, sent, coord, fwd>>
CoordAbort == coord.alive /\ decision = [p \in participants |-> undecided]
                /\ \E p \in participants : pstate[p] = no
                /\ coord' = [coord EXCEPT !.decision = abort]
                /\ UNCHANGED <<pstate, alive, decision, faulty, sent, fwd>>
CoordCommit == coord.alive /\ decision = [p \in participants |-> undecided]
                 /\ \A p \in participants : pstate[p] = yes
                 /\ coord' = [coord EXCEPT !.decision = commit]
                 /\ UNCHANGED <<pstate, alive, decision, faulty, sent, fwd>>
Broadcast(p) == coord.alive /\ coord.decision # waiting
                   /\ coord.broadcast[p] = waiting
                   /\ coord' = [coord EXCEPT !.broadcast[p] = coord.decision]
                   /\ UNCHANGED <<pstate, alive, decision, faulty, sent, fwd>>
CoordDies == coord.alive /\ coord' = [coord EXCEPT !.alive = FALSE]
               /\ UNCHANGED <<pstate, alive, decision, faulty, sent, fwd>>

\* Extension: a participant stores a pre-decision from the coordinator.
PredecideFromCoord(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ coord.broadcast[p] # waiting
  /\ decision' = [decision EXCEPT ![p] = coord.broadcast[p]]
  /\ UNCHANGED <<pstate, alive, faulty, sent, coord, fwd>>

\* Extension: a participant stores a pre-decision forwarded by another participant.
PredecideFromFwd(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ decision' = [decision EXCEPT ![p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, faulty, sent, coord, fwd>>

\* Extension: forward a received pre-decision to another participant.
Forward(p, q) ==
  /\ alive
  /\ decision[p] # undecided
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sent, coord>>

\* Extension: commit locally only once every other participant has been forwarded
\* the pre-decision (the non-blocking guarantee).
Decide(p) ==
  /\ alive
  /\ decision[p] # undecided
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, faulty, sent, coord, fwd>>

AbortTimeout(p) ==
  /\ alive
  /\ decision[p] = undecided
  /\ ~coord.alive
  /\ \A q \in participants : coord.broadcast[q] = waiting
  /\ \A q \in participants : \A r \in participants :
       (q # r /\ ~alive) => fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, sent, coord, fwd>>

\* A participant can crash; its forwarded decisions remain in flight (reliable
\* broadcast), which is what keeps non-faulty participants from blocking.
Die(p) == decision[p] = undecided /\ alive /\ alive' = FALSE
            /\ faulty' = TRUE
            /\ UNCHANGED <<pstate, decision, sent, coord, fwd>>

Next ==
  \/ SendReq \/ CoordAbort \/ CoordCommit \/ CoordDies
  \/ \E p \in participants :
       Vote(p) \/ DecideNo(p) \/ Broadcast(p) \/ PredecideFromCoord(p)
       \/ PredecideFromFwd(p) \/ Decide(p) \/ AbortTimeout(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_Vars
    /\ WF_Vars(\E p \in participants : PredecideFromCoord(p))
    /\ WF_Vars(\E p \in participants : PredecideFromFwd(p))
    /\ WF_Vars(\E p \in participants : Decides(p))

\* No two participants commit and abort against each other.
AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit is backed by a unanimous yes.
AC2 ==
  \A p \in participants : decision[p] = commit => \A q \in participants : pstate[q] = yes

\* An abort has a proper cause: a no vote, a faulty participant, or a faulty coordinator.
AC3 ==
  \A p \in participants : decision[p] = abort => (\E q \in participants : pstate[q] = no)
                                      \/ faulty \/ coord.faulty

\* A decision is final once made.
AC4 ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort)
       => (pstate[p] # undecided)

\* Every non-faulty participant eventually reaches a decision (non-blocking).
AC5 ==
  \A p \in participants : (alive /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC5

====