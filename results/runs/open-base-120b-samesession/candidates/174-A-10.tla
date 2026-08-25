---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Node, 
    SlushLoopProcess, 
    SlushQueryProcess, 
    HostMapping, 
    SlushIterationCount, 
    SampleSetSize, 
    PickFlipThreshold, 
    NoColor, 
    NoMessage

\* ----------------------------------------------------------------------
\* Colors used by the protocol
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Shape of messages exchanged in the system
\* ----------------------------------------------------------------------
Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}),
            col  : (Color \cup {NoColor})]

\* ----------------------------------------------------------------------
\* PlusCal algorithm describing Slush
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables
    color  = [n \in Node |-> NoColor],
    msgs   = {},
    sample = [lp \in SlushLoopProcess |-> {}],
    iter   = [lp \in SlushLoopProcess |-> 0];

define
    HostNode(p) ==
        IF p \in SlushLoopProcess THEN
            CHOOSE n \in Node : <<n, p, _>> \in HostMapping
        ELSE IF p \in SlushQueryProcess THEN
            CHOOSE n \in Node : <<n, _, p>> \in HostMapping
        ELSE NoColor
end define;

process (client = "client")
{
    while TRUE do
        with n \in Node :
            \E m \in Node : color[m] = NoColor /\ n = m
        do
            with c \in Color do
                color := [color EXCEPT ![n] = c];
            end with;
        end with;
    end while;
}

process (lp \in SlushLoopProcess)
{
    await (\E n \in Node : <<n, lp, _>> \in HostMapping /\ color[n] # NoColor);
    while iter[lp] < SlushIterationCount do
        with S \in SUBSET { q \in SlushQueryProcess : q # lp } :
                Cardinality(S) = SampleSetSize
        do
            sample := [sample EXCEPT ![lp] = S];
        end with;
        with peers == sample[lp] do
            with c == color[HostNode(lp)] do
                msgs := msgs \cup { [type |-> "query",
                                     src  |-> lp,
                                     dst  |-> q,
                                     col  |-> c] : q \in peers };
            end with;
        end with;
        await (\A q \in sample[lp] :
                \E m \in msgs :
                    m.type = "reply" /\ m.src = q /\ m.dst = lp);
        let reds  == Cardinality({ m \in msgs :
                                    m.type = "reply" /\ m.dst = lp /\ m.col = "Red" });
            blues == Cardinality({ m \in msgs :
                                    m.type = "reply" /\ m.dst = lp /\ m.col = "Blue" })
        in
            if reds >= PickFlipThreshold then
                color := [color EXCEPT ![HostNode(lp)] = "Red"];
            elsif blues >= PickFlipThreshold then
                color := [color EXCEPT ![HostNode(lp)] = "Blue"];
            else
                skip;
            end if;
        end let;
        msgs := { m \in msgs :
                  ~(m.type = "query" /\ m.dst \in SlushQueryProcess) };
        iter := [iter EXCEPT ![lp] = @ + 1];
    end while;
    msgs := msgs \cup { [type |-> "term",
                         src  |-> lp,
                         dst  |-> "all",
                         col  |-> NoColor] };
}

process (qp \in SlushQueryProcess)
{
    while TRUE do
        await (\E m \in msgs : m.type = "query" /\ m.dst = qp);
        with m \in msgs : m.type = "query" /\ m.dst = qp do
            if color[HostNode(qp)] = NoColor then
                color := [color EXCEPT ![HostNode(qp)] = m.col];
            end if;
            msgs := msgs \cup { [type |-> "reply",
                                 src  |-> qp,
                                 dst  |-> m.src,
                                 col  |-> color[HostNode(qp)]] };
            msgs := msgs \ { m };
        end with;
    end while;
}
*)

\* ----------------------------------------------------------------------
\* Specification, invariants and properties
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ color \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message

====