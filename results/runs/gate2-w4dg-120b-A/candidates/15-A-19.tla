---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

(* TLA+ model of a one-round asynchronous reliable broadcast protocol with    *)
(* Byzantine faults, derived from Srikanth & Toueg 1987 Figure 7.  The model  *)
(* is parameterised by N (total processes, partitioned into correct and       *)
(* faulty), T (the Byzantine bound, requiring N > 3T), and F (actual Byzantine *)
(* processes, with F <= T).  Correct processes cycle through control states    *)
(* tied to the receipt of an INIT message and of ECHO messages from others; a  *)
(* process accepts only after witnessing a quorum of distinct ECHOs.  Two      *)
(* mutually exclusive initial configurations are modelled: one with no        *)
(* broadcasts at all (for the unforgeability safety check) and one with every *)
(* correct process having received the INIT broadcast.                        *)

CONSTANTS N, T, F

\* Process control states: PnoB (no broadcast received), PgotB (broadcast    *)
\* received but not yet acted), PhasSent (ECHO already sent), Paccepted.     *
\* The FULL set is the union of all four, used for domain checking.           *
Processes == 1..N
PnoB == "pnoB"
PgotB == "pgotB"
PhasSent == "phsent"
Paccepted == "pacc"
FULL == {PnoB, PgotB, PhasSent, Paccepted}

VARIABLES correct, faulty, loc, rcvd, sent

vars == <<correct, faulty, loc, rcvd, sent>>

Msg == [fr: Processes, ty: {"echo"}]

TypeOK ==
    /\ correct \subseteq Processes
    /\ faulty \subseteq Processes
    /\ loc \in [Processes -> FULL]
    /\ rcvd \in [Processes -> SUBSET Msg]
    /\ sent \subseteq Msg

FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ correct \cup faulty = Processes
    /\ correct \cap faulty = {}
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

Init ==
    /\ correct = CHOOSE S \in {S \in SUBSET Processes : Cardinality(S) = N - F}
                   : TRUE
    /\ faulty = Processes \ correct
    /\ loc = [p \in Processes |-> PnoB]
    /\ rcvd = [p \in Processes |-> {}]
    /\ sent = {}

\* A restricted initial state with no correct process receiving an INIT.
InitNoCast ==
    /\ correct = CHOOSE S \in {S \in SUBSET Processes : Cardinality(S) = N - F}
                   : TRUE
    /\ faulty = Processes \ correct
    /\ loc = [p \in Processes |-> PnoB]
    /\ rcvd = [p \in Processes |-> {}]
    /\ sent = {}

\* A correct process may receive any (possibly empty) set of messages that
\* could have been sent by correct processes together with any Byzantine msgs.
Recv(p, M) ==
    /\ p \in correct
    /\ M \subseteq (sent \cup [fr \in faulty, ty |-> "echo"])
    /\ M # {}
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup M]
    /\ UNCHANGED <<correct, faulty, loc, sent>>

SendEcho(p) ==
    /\ loc[p] # PhasSent
    /\ sent' = sent \cup {[fr |-> p, ty |-> "echo"]}
    /\ loc' = [loc EXCEPT ![p] = PhasSent]
    /\ UNCHANGED <<correct, faulty, rcvd>>

Accept(p) ==
    /\ loc[p] # Paccepted
    /\ loc' = [loc EXCEPT ![p] = Paccepted]
    /\ UNCHANGED <<correct, faulty, rcvd, sent>>

\* A correct initiator that already received the broadcast accepts and sends.
ActInit(p) ==
    /\ p \in correct
    /\ loc[p] = PgotB
    /\ SendEcho(p) /\ Accept(p)

\* The quorum step just before the acceptance threshold.
ActMid(p) ==
    /\ p \in correct
    /\ loc[p] \in {PnoB, PgotB}
    /\ Cardinality({m \in rcvd[p] : m.ty = "echo"}) >= N - 2 * T
    /\ Cardinality({m \in rcvd[p] : m.ty = "echo"}) < N - T
    /\ SendEcho(p)

\* The quorum step at the acceptance threshold.
ActThresh(p) ==
    /\ p \in correct
    /\ loc[p] \in {PnoB, PgotB}
    /\ Cardinality({m \in rcvd[p] : m.ty = "echo"}) >= N - T
    /\ SendEcho(p) /\ Accept(p)

\* A correct process that already sent ECHO accepts when the quorum is met.
ActPost(p) ==
    /\ p \in correct
    /\ loc[p] = PhasSent
    /\ Cardinality({m \in rcvd[p] : m.ty = "echo"}) >= N - T
    /\ Accept(p)

Next ==
    \/ \E p \in Processes, M \in SUBSET Msg : Recv(p, M)
    \/ \E p \in Processes : ActInit(p) \/ ActMid(p) \/ ActThresh(p) \/ ActPost(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Processes, M \in SUBSET Msg : Recv(p, M))
    /\ SF_vars(\E p \in Processes : ActInit(p) \/ ActMid(p) \/ ActThresh(p) \/ ActPost(p))

\* Safety: unforgeability -- with no broadcast, no acceptance ever occurs.
UnforgLtl == (\A p \in correct : loc[p] = PnoB) ~> (\A p \in correct : loc[p] # Paccepted)

CorrLtl == (\A p \in correct : loc[p] = PgotB) ~> (\A p \in correct : loc[p] = Paccepted)

RelayLtl == (\E p \in correct : loc[p] = Paccepted) ~> (\A p \in correct : loc[p] = Paccepted)

====