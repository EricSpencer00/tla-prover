---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The 1987 Srikanth & Toueg reliable broadcast protocol: a single broadcast
\* message must be delivered to every correct participant even with up to T
\* Byzantine participants.  Instead of a dedicated broadcaster we model the
\* broadcast as an initial value: a process begins either having "heard"
\* the INIT broadcast or not, and the safety property hinges on that.
\* Each correct process sends at most one ECHO message; "sent" records only
\* the correct processes' sends, so a Byzantine process can send a message
\* for every correct participant without ever being recorded as a sender.

VARIABLES correct, faulty, loc, recvd, sent

vars == << correct, faulty, loc, recvd, sent >>

Members == 0..(N - 1)

Msgs == [ snd : Members, kind : {"ECHO"} ]

TypeOK ==
  /\ correct \subseteq Members
  /\ faulty = Members \ correct
  /\ loc \in [Members -> {"no_tx","rx","echoed","accept"}]
  /\ recvd \in [Members -> SUBSET Msgs]
  /\ sent \subseteq (Members \times {"ECHO"})

Cardinals ==
  /\ Cardinality(correct) = N - F
  /\ F =< T
  /\ T >= 1
  /\ N > 3 * T
  /\ F >= 0

Init ==
  /\ correct = {0, 1, 2}
  /\ loc = [m \in Members |-> IF m < 3 THEN "rx" ELSE "no_tx"]
  /\ recvd = [m \in Members |-> {}]
  /\ sent = {}

SilentInit ==
  /\ correct = {0, 1, 2}
  /\ loc = [m \in Members |-> "no_tx"]
  /\ recvd = [m \in Members |-> {}]
  /\ sent = {}

\* A correct process receives any subset of all existing correct ECHO
\* messages and any subset of Byzantine ECHO messages (the latter are not
\* recorded in `sent`).
ReceiveMsgs(m) ==
  /\ m \in correct /\ loc[m] # "accept"
  /\ \E c \in (sent \cup (Members \times {"ECHO"})):
       recvd' = [recvd EXCEPT ![m] = @ \cup c]
  /\ UNCHANGED << correct, faulty, loc, sent >>

\* Receiving the broadcast (INIT) and sending ECHO happens in one step here,
\* since sending is unguarded for a process that has already heard the
\* broadcast and would otherwise spin forever sending the same ECHO.
SendEcho(m) ==
  /\ m \in correct /\ loc[m] = "rx"
  /\ loc' = [loc EXCEPT ![m] = "echoed"]
  /\ sent' = sent \cup {<< m, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvd >>

\fbox{IMPLY} (n \in Nat) == n = 0 \/ \E k \in Nat : n = k + 1

\* A process with enough ECHOs (a majority) but below the acceptance
\* threshold decides to send ECHO without yet committing to acceptance.
ActEcho(m) ==
  /\ m \in correct /\ loc[m] = "no_tx"
  /\ (Cardinality({x \in recvd[m] : x.kind = "ECHO"}) = 0 \/ \E n \in Nat : n = Cardinality({x \in recvd[m] : x.kind = "ECHO"}) /\ n < N - 2 * T)
  /\ loc' = [loc EXCEPT ![m] = "echoed"]
  /\ sent' = sent \cup {<< m, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvd >>

AcceptEcho(m) ==
  /\ m \in correct /\ loc[m] = "no_tx"
  /\ Cardinality({x \in recvd[m] : x.kind = "ECHO"}) >= N - T
  /\ loc' = [loc EXCEPT ![m] = "accept"]
  /\ sent' = sent \cup {<< m, "ECHO" >>}
  /\ UNCHANGED << correct, faulty, recvd >>

\* A process that has already ECHO'ed may still be lagging on accept
\* while waiting for enough distinct ECHO messages from peers.
AcceptLater(m) ==
  /\ m \in correct /\ loc[m] = "echoed"
  /\ Cardinality({x \in recvd[m] : x.kind = "ECHO"}) >= N - T
  /\ loc' = [loc EXCEPT ![m] = "accept"]
  /\ UNCHANGED << correct, faulty, recvd, sent >>

Next ==
  \/ \E m \in Members : ReceiveMsgs(m) \/ SendEcho(m) \/ ActEcho(m) \/ AcceptEcho(m) \/ AcceptLater(m)

Spec ==
  /\ Cardinals
  /\ Init
  /\ [][Next]_vars
  /\ \A m \in correct : WF_vars(SendEcho(m))
  /\ \A m \in correct : WF_vars(AcceptEcho(m))

SilentSpec ==
  /\ Cardinals
  /\ SilentInit
  /\ [][Next]_vars

\* Unforgeability: if no correct process broadcast at all, none ever accepts.
UnforgLtl ==
  /\ Cardinals
  /\ SilentInit
  /\ \A m \in correct : ~loc[m] = "accept"

CorrLtl == <>(\A m \in correct : loc[m] = "accept")

RelayLtl == (\E m \in correct : loc[m] = "accept") ~> (\A m \in correct : loc[m] = "accept")

FCConstraints ==
  /\ Cardinality({m \in correct : loc[m] = "accept"}) =< N
  /\ Cardinality({m \in correct : loc[m] = "rx"}) =< N
====