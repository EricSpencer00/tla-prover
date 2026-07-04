---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* ----------------------------------------------------------------------
\* NOTE:  The original specification defined ``TraceN`` as
\*   TraceN == JsonLog[1].N
\* which caused TLC to complain that the constant ``N`` (substituted
\*   with ``TraceN`` in the *.cfg file) was not a constant expression.
\* The JSON deserialization routine in the ``Json`` module uses an
\*   unbounded CHOOSE, which is not permitted for constant substitution.
\*
\* To keep the original intent (the number of nodes is taken from the
\*   first line of the log) while satisfying TLC’s requirement that a
\*   substituted constant be a *syntactic* constant, we introduce a new
\*   constant ``TraceNConst`` that will be substituted for ``N`` by the
\*   configuration file (as before).  The value of ``TraceNConst`` is a
\*   *syntactic* constant (a literal number).  We then add an explicit
\*   top‑level assumption that the value read from the JSON log matches
\*   that constant.  This preserves the semantics of the original model:
\*   a run where the log’s node count does not agree with the constant
\*   will simply violate the assumption and be discarded by TLC.
\*
\* The JSON log itself is kept as a *variable* (``JsonLog``) so that its
\*   construction does not occur in a constant context.
\* ----------------------------------------------------------------------

CONSTANT TraceNConst        \* This constant is substituted for ``N`` by the
                           \* configuration file (``N <- TraceN``).  It must
                           \* be a literal number; the model‑checking
                           \* run supplies the appropriate value.

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES JsonLog, active, color, inbox, counter

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ JsonLog' = ndJsonDeserialize(
                     IF "JSON" \in DOMAIN IOEnv
                     THEN IOEnv.JSON
                     ELSE "specifications/ewd998/EWD998ChanTrace.ndjson")
    /\ Init!1
    /\ Init!2
    /\ active \in [Node -> {TRUE}]
    /\ color  \in [Node -> {"white"}]
    /\ counter = [n \in Node |-> 0]
    /\ inbox   = [n \in Node |-> << >>]   \* initially empty inboxes
    /\ UNCHANGED <<vars>>   \* ``vars`` is the tuple of all state variables
                              \* defined in the extended module ``EWD998Chan``

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
TraceN == JsonLog[1].N                \* Number of nodes as read from the log
TraceLog ==
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    IN CausalOrder(suffix,
                    LAMBDA l : l.pkt.vc,
                    LAMBDA l : ToString(l.node),
                    LAMBDA vc : DOMAIN vc)

\* ----------------------------------------------------------------------
\* Consistency assumption
\* ----------------------------------------------------------------------
\* The constant supplied by the configuration file must agree with the
\* value obtained from the JSON log.  If it does not, the whole
\* specification is discarded (the assumption is false in the initial
\* state).
ASSUME TraceNConst = TraceN

\* ----------------------------------------------------------------------
\* Trace specification (unchanged apart from the use of the new
\*   ``Init`` definition above)
\* ----------------------------------------------------------------------
TraceInit ==
    /\ Init!1
    /\ Init!2
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]

TraceSpec ==
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

\* ----------------------------------------------------------------------
\* Message predicates
\* ----------------------------------------------------------------------
PayloadPred(msg) == msg.type = "pl"

\* ----------------------------------------------------------------------
\* Action recognizers (unchanged)
\* ----------------------------------------------------------------------
IsInitiateToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    /\ l.pkt.rcv = TraceN - 1
    /\ l.pkt.snd = 0
    /\ <<InitiateProbe>>_vars

IsPassToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    LET snd == l.pkt.snd IN
        /\ snd > 0
        /\ <<PassToken(snd)>>_vars

IsRecvToken(l) ==
    /\ l.event = "<"
    LET msg == l.pkt.msg
        rcv == l.pkt.rcv IN
        /\ msg.type = "tok"
        /\ \A n \in Node:
               SelectSeq(inbox[n], PayloadPred) = SelectSeq(inbox'[n], PayloadPred)
        /\ \E idx \in DOMAIN inbox'[rcv]:
              /\ inbox'[rcv][idx].type = "tok"
              /\ inbox'[rcv][idx].q = msg.q
              /\ inbox'[rcv][idx].color = msg.color
        /\ UNCHANGED <<active, counter, color>>

IsSendMsg(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "pl"
    /\ <<SendMsg(l.pkt.snd)>>_vars
    LET rcv == l.pkt.rcv IN
        Len(SelectSeq(inbox[rcv], PayloadPred))
           < Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==
    /\ l.event = "<"
    /\ l.pkt.msg.type = "pl"
    /\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==
    /\ l.event = "d"
    /\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==
    /\ l.event \in {"<", ">"}
    /\ l.pkt.msg.type = "trm"
    /\ \A n \in Node: ~active[n]
    /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Trace constraints (unchanged)
\* ----------------------------------------------------------------------
TraceNextConstraint ==
    LET i == TLCGet("level")
    IN /\ i <= Len(TraceLog)
       LET logline == TraceLog[i] IN
           BP::
           /\ \/ IsInitiateToken(logline)
              \/ IsPassToken(logline)
              \/ IsRecvToken(logline)
              \/ IsSendMsg(logline)
              \/ IsRecvMsg(logline)
              \/ IsDeactivate(logline)
              \/ IsTrm(logline)
           /\ "failure" \notin DOMAIN logline

TraceInv ==
    LET l == TraceLog[TLCGet("level")] IN
    /\ "failure" \notin DOMAIN l
    /\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm") => \A n \in Node: ~active[n]

\* ----------------------------------------------------------------------
\* View and post‑condition (unchanged)
\* ----------------------------------------------------------------------
TraceView ==
    <<vars, TLCGet("level")>>

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:",
                 TraceLog[d],
                 "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>,
               FALSE)

TraceAlias ==
    [
        log     |-> <<TLCGet("level"), TraceLog[TLCGet("level") - 1]>>,
        active  |-> active,
        color   |-> color,
        counter |-> counter,
        inbox   |-> inbox,
        term    |-> <<EWD998!terminationDetected, "=>", EWD998!Termination>>,
        enabled |-> [
            InitToken  |-> ENABLED InitiateProbe,
            PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
            SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
            RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
            Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
        ]
    ]
=============================================================================