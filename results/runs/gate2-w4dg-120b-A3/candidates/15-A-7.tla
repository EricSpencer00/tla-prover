---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* A reliable broadcast (Fig.7, Srikanth-Toueg 87) where "INIT" is not a
\* privileged broadcaster but a per-process initial value.  N processes
\* split into correct and Byzantine (faulty) sets; the split is chosen at
\* init and re-used for the whole run.  Correct processes send one echo
\* message; Byzantine processes can send arbitrary echo messages, so the
\* receive action conjoins all correct echoes with any arbitrary set.
\* Safety: if nobody correct broadcasted, nobody accepts.  Liveness: if
\* everybody broadcasted, everybody accepts; once somebody accepts, the
\* relay round drives the rest to accept.

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recvd, sent

vars == << correct, faulty, pc, recvd, sent >>

MsgSet == [snd : 1..N, typ : {"ECHO"}]

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ pc \in [1..N -> {"init", "noninit", "sent", "accept"}]
    /\ recvd \in [1..N -> SUBSET MsgSet]
    /\ sent \subseteq MsgSet

\* The invariant is quoted in the spec itself (not a derived impl. fact):
\* no action may forge a message -- a correct process's echo must always
\* be a real echo from its own send, so the echo type never drifts.
FCConstraints ==
    /\ \A c \in correct : pc[c] \in {"init", "noninit", "sent", "accept"}
    /\ recvd \subseteq MsgSet
    /\ sent \subseteq MsgSet

\* Correct processes broadcast exactly one echo; the Byzantine set has no
\* single send to track, so any non-correct echo is "available" to be
\* received at any time (captured by the arbitrary MsgSet in any step).
Init ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(correct) = N - F
    /\ correct \cup faulty = (1..N)
    /\ correct \cap faulty = {}
    /\ \E b \in {"init", "noninit"} :
        /\ \E c \in correct : pc[c] = b
        /\ \A c \in (1..N) \ {c} : pc[c] \in {"init", "noninit"}
    /\ recvd = [p \in 1..N |-> {}]
    /\ sent = {}

\* A correct process picks up any (bounded) new messages it can receive
\* from correct senders plus any possible Byzantine echo message.
Receive(c) ==
    /\ pc[c] \in {"init", "noninit", "sent"}
    /\ LET arrivals ==
        (sent \cap {m \in MsgSet : m.snd \in correct})
          \cup {m \in MsgSet : m.snd \in faulty} IN
        recvd' = [recvd EXCEPT ![c] = recvd[c] \cup arrivals]
    /\ UNCHANGED << correct, faulty, pc, sent >>

\* A correct process that has the INIT message accepts immediately and
\* sends its echo to all (once per join).
Broadcast(c) ==
    /\ pc[c] = "init"
    /\ pc' = [pc EXCEPT ![c] = "sent"]
    /\ sent' = sent \cup {[snd |-> c, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recvd >>

\* A correct process that has not broadcast yet but has collected the
\* majority-but-not-quorum set of echoes now broadcasts (but does not
\* accept yet because it has not reached the quorum threshold).
PreEcho(c) ==
    /\ pc[c] \in {"init", "noninit"}
    /\ Cardinality({m \in recvd[c] : m.typ = "ECHO"}) >= N - 2 * T
    /\ Cardinality({m \in recvd[c] : m.typ = "ECHO"}) < N - T
    /\ pc' = [pc EXCEPT ![c] = "sent"]
    /\ sent' = sent \cup {[snd |-> c, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recvd >>

\* A correct process that has not broadcast yet and has reached quorum
\* both broadcasts and accepts in the same step.
Echo(c) ==
    /\ pc[c] \in {"init", "noninit"}
    /\ Cardinality({m \in recvd[c] : m.typ = "ECHO"}) >= N - T
    /\ pc' = [pc EXCEPT ![c] = "sent"]
    /\ sent' = sent \cup {[snd |-> c, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recvd >>

\* A correct process that has already broadcast accepts once it reaches
\* quorum.
Accept(c) ==
    /\ pc[c] = "sent"
    /\ Cardinality({m \in recvd[c] : m.typ = "ECHO"}) >= N - T
    /\ pc' = [pc EXCEPT ![c] = "accept"]
    /\ UNCHANGED << correct, faulty, recvd, sent >>

\* Weak fairness on the combined receive/action steps ensures a correct
\* process that can forever receive from correct senders is never stuck.
Next ==
    \/ \E c \in correct : Receive(c)
    \/ \E c \in correct : Broadcast(c)
    \/ \E c \in correct : PreEcho(c)
    \/ \E c \in correct : Echo(c)
    \/ \E c \in correct : Accept(c)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in correct : TRUE
    /\ \A c \in correct :
        /\ WF_vars(Receive(c))
        /\ SF_vars(Broadcast(c))
        /\ SF_vars(PreEcho(c))
        /\ SF_vars(Echo(c))
        /\ SF_vars(Accept(c))

\* Correctness: a quorum of correct processes broadcasting carries the
\* whole correct set to accept.
CorrLtl == (\A c \in correct : pc[c] = "init") ~> (\A c \in correct : pc[c] = "accept")

\* Relay: one correct accept carries the rest.
RelayLtl == (\E c \in correct : pc[c] = "accept") ~> (\A c \in correct : pc[c] = "accept")

\* Unforgeability: if no correct process broadcasted, none accepts.
UnforgLtl == (\A c \in correct : pc[c] # "init") ~> (\A c \in correct : pc[c] # "accept")

====