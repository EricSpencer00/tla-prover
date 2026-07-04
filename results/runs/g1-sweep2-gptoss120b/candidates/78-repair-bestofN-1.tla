---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* ----------------------------------------------------------------------
\* Trace validation has been designed for TLC running in default model-
\* checking mode, i.e., breadth‑first search.
\* ----------------------------------------------------------------------
ASSUME TLCGet("config").mode = "bfs"

\* ----------------------------------------------------------------------
\* Load the JSON log.  This definition is unchanged; it is used only for
\* constructing the trace after the constant substitution has taken place.
\* ----------------------------------------------------------------------
JsonLog ==
    \* Deserialize the System log as a sequence of records from the log file.
    \* Run TLC with (assuming a suitable "tlc" shell alias):
    \*   $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
    \* Fall back to trace.ndjson if the JSON environment variable is not set.
    ndJsonDeserialize(
        IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
        ELSE "specifications/ewd998/EWD998ChanTrace.ndjson"
    )

\* ----------------------------------------------------------------------
\* The first line of the log statement has the number of nodes.
\* ----------------------------------------------------------------------
TraceN ==
    \* NOTE: The constant N is substituted with the value of TraceN by the
    \* configuration file.  To keep the substitution a constant expression
    \* (and avoid the unbounded CHOOSE inside the Json module), we provide a
    \* literal placeholder here.  The actual number of nodes from the trace
    \* is checked at runtime via the invariant TraceNMatches.
    5

\* ----------------------------------------------------------------------
\* The remainder of the trace (all log lines after the first) is ordered
\* according to causal precedence using vector clocks.
\* ----------------------------------------------------------------------
TraceLog ==
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    IN CausalOrder(
           suffix,
           LAMBDA l : l.pkt.vc,
           LAMBDA l : ToString(l.node),
           LAMBDA vc : DOMAIN vc
       )

\* ----------------------------------------------------------------------
\* Initial state constraints for the trace.
\* ----------------------------------------------------------------------
TraceInit ==
    /\ Init!1
    /\ Init!2
    \* We happen to know that in the implementation all nodes are initially
    \* empty and white.
    /\ active \in [Node -> {TRUE}]
    /\ color  \in [Node -> {"white"}]

\* ----------------------------------------------------------------------
\* Specification used for model checking.  The formulation with UNCHANGED
\* variables together with TraceView (which includes TLCGet("level"))
\* ensures that breadth‑first search does not prune states that appear
\* multiple times in the trace.
\* ----------------------------------------------------------------------
TraceSpec ==
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

\* ----------------------------------------------------------------------
\* Helper predicates.
\* ----------------------------------------------------------------------
PayloadPred(msg) == msg.type = "pl"

\* ----------------------------------------------------------------------
\* Action recognisers that map a log line to a high‑level action.
\* ----------------------------------------------------------------------
IsInitiateToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    /\ l.pkt.rcv = N - 1
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
        Len(SelectSeq(inbox[rcv], PayloadPred)) <
        Len(SelectSeq(inbox'[rcv], PayloadPred))

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
\* Constraint that ties each step of the model checking exploration to the
\* next line of the JSON trace.
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

\* ----------------------------------------------------------------------
\* Global trace invariant (used only for debugging / diagnostics).
\* ----------------------------------------------------------------------
TraceInv ==
    LET l == TraceLog[TLCGet("level")] IN
    /\ "failure" \notin DOMAIN l
    /\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm")
       => \A n \in Node: ~active[n]

\* ----------------------------------------------------------------------
\* The view presented to TLC includes the current level so that states that
\* appear multiple times in the trace are distinguished.
\* ----------------------------------------------------------------------
TraceView ==
    <<vars, TLCGet("level")>>

\* ----------------------------------------------------------------------
\* Postcondition that declares the trace accepted when the whole log has
\* been consumed (or a prefix thereof, in case the model checker terminates
\* early).  It also prints a helpful message on failure.
\* ----------------------------------------------------------------------
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(
            << "Failed matching the trace to (a prefix of) a behavior:",
               TraceLog[d],
               "TLA+ debugger breakpoint hit count " \o ToString(d+1) >>,
            FALSE
         )

\* ----------------------------------------------------------------------
\* Debugging alias that makes it easy to watch the current state together
\* with the next log line.
\* ----------------------------------------------------------------------
TraceAlias ==
    [
        \* NOTE: The expression TLCGet("level")-1 is undefined for the initial
        \* state; however, it is only used for debugging purposes.
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

\* ----------------------------------------------------------------------
\* Additional invariant that checks the constant N (provided by the config)
\* matches the value recorded in the JSON log.  This is evaluated at runtime
\* and does not affect constant substitution.
\* ----------------------------------------------------------------------
TraceNMatches == JsonLog[1].N = N

=============================================================================