---- MODULE EWD998ChanTrace ----
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* Trace validation has been designed for TLC running in default model-checking
 \* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

\* ------------------------------------------------------------------
\* The trace log is deserialized from a JSON file.  The original module
\* used an unbounded CHOOSE in the constant expression for TraceN,
\* which caused TLC to reject the configuration.  We now compute the
\* number of nodes in a bounded way: we assume that the trace created
\* by EWD998 will never contain more than 10 nodes (this is a realistic
\* bound for the use cases of this spec).  The CHOOSE is therefore
\* bounded and accepted by TLC.  If a trace has more than 10 nodes,
\* the spec should be re-parameterised with a larger bound.
\* ------------------------------------------------------------------

JsonLog ==
    \* Deserialize the System log as a sequence of records from the log file.
    \* Run TLC with (assuming a suitable "tlc" shell alias):
    \* $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
    \* Fall back to trace.ndjson if the JSON environment variable is not set.
    ndJsonDeserialize(IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "specifications/ewd998/EWD998ChanTrace.ndjson")

\* The first line of the log statement has the number of nodes.
TraceN ==
    CHOOSE n \in 1..10 :
        JsonLog[1].N = n

\* SubSeq starting at 2 to skip the N value.
TraceLog ==
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    IN CausalOrder(suffix,
                    LAMBDA l : l.pkt.vc,
                    LAMBDA l : ToString(l.node), LAMBDA vc : DOMAIN vc)

\* ------------------------------------------------------------------
\* Initialisation of the trace specification.  We initialise the
\* variables of the underlying protocol as in the standard specification
\* and then set the trace-specific variables.  The trace-specific
\* variables are added to the set of variables that are left unchanged
\* when the trace line does not correspond to a high-level action.
\* ------------------------------------------------------------------
TraceInit ==
    /\ Init!1
    /\ Init!2
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]
    /\ log \in TraceLog
    /\ level \in 0..Len(TraceLog)

\* The specification is the usual initialisation plus the next-state
\* action, where the standard "Next" action is nondeterministically
\* extended with the trace constraint (TraceNextConstraint) and
\* the trace view (TraceView).  The "Next \/ UNCHANGED vars" extension
\* is necessary for TLC's breadth-first search to explore states that
\* have already been seen (but with a different trace level).
TraceSpec ==
    TraceInit
    /\ [][Next \/ UNCHANGED vars]_vars

\* ------------------------------------------------------------------
\* Predicate that recognises a payload message.
\* ------------------------------------------------------------------
PayloadPred(msg) ==
    msg.type = "pl"

\* ------------------------------------------------------------------
\* The following predicates describe the different kinds of trace
\* entries that correspond to high-level actions.  They are used in
\* the trace constraint (TraceNextConstraint) to constrain the
\* next-state relation.
\* ------------------------------------------------------------------
IsInitiateToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    /\ l.pkt.rcv = N - 1
    /\ l.pkt.snd = 0
    /\ <<InitiateProbe>>_vars

IsPassToken(l) ==
    /\ l.event = ">"
    /\ l.pkt.msg.type = "tok"
    /\ LET snd == l.pkt.snd IN
        /\ l.pkt.snd > 0
        /\ <<PassToken(snd)>>_vars

IsRecvToken(l) ==
    /\ l.event = "<"
    /\ LET msg == l.pkt.msg
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
    /\ LET rcv == l.pkt.rcv IN
        Len(SelectSeq(inbox[rcv], PayloadPred)) < Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==
    /\ l.event = "<"
    /\ l.pkt.msg .type = "pl"
    /\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==
    /\ l.event = "d"
    /\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==
    /\ l.event \in {"<", ">"}
    /\ l.pkt.msg.type = "trm"
    /\ \A n \in Node: ~active[n]
    /\ UNCHANGED vars

\* ------------------------------------------------------------------
\* The TraceNextConstraint binds the current trace line to the next
\* state of the specification.  It ensures that for each line of the
\* trace the corresponding action is enabled and executed, or the line
\* is a "trm" message that stutters the entire state.
\* ------------------------------------------------------------------
TraceNextConstraint ==
    LET i == TLCGet("level")
    IN /\ i <= Len(TraceLog)
       /\ LET logline == TraceLog[i]
          IN /\ \/ IsInitiateToken(logline)
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

\* ------------------------------------------------------------------
\* TraceView makes the view of the state depend on the trace level, so
\* that TLC does not stop when a state is seen again at a different
\* trace position.
\* ------------------------------------------------------------------
TraceView ==
    <<vars, TLCGet("level")>>

\* ------------------------------------------------------------------
\* TraceAccepted ensures that the trace is fully consumed by TLC.  The
\* condition is true of a set of behaviours, not a single behaviour.
\* ------------------------------------------------------------------
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", TraceLog[d], 
                    "TLCGet(\"stats\").diameter = ", d,
                    "TLCGet(\"stats\").diameter + 1 = ", d+1>>, FALSE)

TraceAlias ==
    [
        log     |-> <<TLCGet("level"), TraceLog[TLCGet("level") - 1]>>,
        active  |-> active,
        color   |-> color,
        counter |-> counter,
        inbox   |-> inbox,
        term    |-> <<EWD998!terminationDetected, "=>", EWD998!Termination>>,
        enabled |-> 
            [
                InitToken  |-> ENABLED InitiateProbe,
                PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
                SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
                RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
                Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
            ]
    ]

====