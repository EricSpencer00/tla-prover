---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote, alive, decision, faulty, sentVote,
  req, vreq, broadcast, dcision, dcoord, fwd

vars == <<vote, alive, decision, faulty, sentVote,
          req, vreq, broadcast, dcision, dcoord, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \subseteq participants
  /\ req \in BOOLEAN
  /\ vreq \in BOOLEAN
  /\ broadcast \in BOOLEAN
  /\ dcision \in {undecided, commit, abort}
  /\ dcoord \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = {}
  /\ req = FALSE
  /\ vreq = FALSE
  /\ broadcast = FALSE
  /\ dcision = undecided
  /\ dcoord = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Inherited coordinator actions (base ACP-SB protocol logic):
SendRequest ==
  /\ \A p \in participants : ~sentVote[p]
  /\ req = FALSE
  /\ req' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, vreq,
                broadcast, dcision, dcoord, fwd>>

GetVote(p) ==
  /\ req = TRUE
  /\ alive[p] = TRUE
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ vreq' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, req,
                broadcast, dcision, dcoord, fwd>>

Detect ==
  /\ vreq = TRUE
  /\ vreq' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, req,
                broadcast, dcision, dcoord, fwd>>

DecideCoord(v) ==
  /\ req = TRUE
  /\ broadcast = FALSE
  /\ \A p \in participants : alive[p]
  /\ dcision' = v
  /\ broadcast' = TRUE
  /\ dcoord' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                req, vreq, fwd>>

\* Inherited participant vote messages:
SendVote(p) ==
  /\ \A q \in participants : ~sentVote[q]
  /\ alive[p] = TRUE
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, req,
                vreq, broadcast, dcision, dcoord, fwd>>

AbortByVote(p) ==
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord, fwd>>

\* New or modified participant actions (non-blocking forwarding):
PreDecideCoord(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] = notsent
  /\ broadcast = TRUE
  /\ fwd' = [fwd EXCEPT ![p][p] = dcision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord>>

PreDecideFwd(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ fwd[q][p] # notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord>>

Forward(p) ==
  /\ alive[p] = TRUE
  /\ fwd[p][p] # notsent
  /\ \E q \in participants :
        /\ p # q
        /\ fwd[p][q] = notsent
        /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord>>

Decide(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord, fwd>>

AbortTimeout(p) ==
  /\ alive[p] = TRUE
  /\ decision[p] = undecided
  /\ broadcast = FALSE
  /\ dcoord = TRUE
  /\ \A q \in participants : alive[q]
  /\ \A q \in participants :
        \A r \in participants : fwd[q][r] # notsent => ~alive[r]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                req, vreq, broadcast, dcision, dcoord, fwd>>

Die(p) ==
  /\ alive[p] = TRUE
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote,
                req, vreq, broadcast, dcision, dcoord, fwd>>

Next ==
  \/ SendRequest \/ Detect
  \/ \E p \in participants : SendVote(p) \/ AbortByVote(p)
  \/ \E v \in {commit, abort} : DecideCoord(v)
  \/ \E p \in participants :
        PreDecideCoord(p) \/ PreDecideFwd(p) \/ Forward(p) \/ Decide(p)
        \/ AbortTimeout(p) \/ Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E v \in {commit, abort} : DecideCoord(v))
  /\ \A p \in participants :
        /\ WF_vars(\E q \in participants : PreDecideCoord(p) \/ PreDecideFwd(p))
        /\ WF_vars(\E q \in participants : Forward(p))
        /\ SF_vars(Decide(p))

\* Safety: no two participants end up in different decisions.
Agreement ==
  ~\E p, q \in participants :
      /\ decision[p] = commit
      /\ decision[q] = abort

\* Safety: a commit requires unanimity; an abort means a no vote or a crash.
CommitValidity ==
  ( \E p \in participants : decision[p] = commit )
    => (\A p \in participants : vote[p] = yes)

AbortValidity ==
  ( \E p \in participants : decision[p] = abort )
    => ( (\E p \in participants : vote[p] = no)
           \/ (\E p \in participants : faulty[p])
           \/ dcoord )

Irreversibility ==
  \A p \in participants :
      (decision[p] = undecided) U (decision[p] # undecided)

\* Liveness: everyone decides or some crash is observed.
EventuallyDecide ==
  <>( \A p \in participants : decision[p] # undecided )
    \/ (\E p \in participants : faulty[p])
    \/ dcoord

\* Liveness: non-blocking termination -- every non-faulty participant decides.
EventualDecision ==
  \A p \in participants : (alive[p] => <>( decision[p] # undecided ))
====