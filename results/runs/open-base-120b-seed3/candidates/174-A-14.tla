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

(* --algorithm SlushAlg
variables
    color \in [Node -> (Colors \cup {NoColor})],
    msgs   \in SUBSET Message,
    sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess],
    iter   \in [SlushLoopProcess -> Nat];

define
    Colors  == {"Red", "Blue"};
    Message == [type : {"query", "reply", "term"},
                src  : (SlushLoopProcess \cup SlushQueryProcess),
                dst  : (SlushLoopProcess \cup SlushQueryProcess),
                col  : (Colors \cup {NoColor})];
    NodeOfLoop(l)  == CHOOSE n \in Node :
                        \E q \in SlushQueryProcess : (n, l, q) \in HostMapping;
    NodeOfQuery(q) == CHOOSE n \in Node :
                        \E l \in SlushLoopProcess : (n, l, q) \in HostMapping;
end define;

process (client = "client")
begin
    while TRUE do
        await \E n \in Node : color[n] = NoColor;
        with n \in { n \in Node : color[n] = NoColor } do
            with col \in Colors do
                color := [color EXCEPT ![n] = col];
            end with;
        end with;
    end while;
end process;

process (Loop(p \in SlushLoopProcess))
variables
    hostNode;
begin
    hostNode := NodeOfLoop(p);
    await color[hostNode] # NoColor;
    iter[p] := 0;
    while iter[p] < SlushIterationCount do
        (* choose a sample of distinct query processes *)
        with s \in SUBSET SlushQueryProcess :
                Cardinality(s) = SampleSetSize
        do
            sample[p] := s;
        end with;

        (* send query messages to the sampled peers *)
        with q \in sample[p] do
            msgs := msgs \cup {
                [type |-> "query",
                 src  |-> p,
                 dst  |-> q,
                 col  |-> color[hostNode]]
            };
        end with;

        (* wait for replies from all sampled peers *)
        await \A q \in sample[p] :
                 \E m \in msgs :
                     /\ m.type = "reply"
                     /\ m.dst  = p
                     /\ m.src  = q;

        (* tally the replies *)
        let redCount  == Cardinality(
                            { m \in msgs :
                                /\ m.type = "reply"
                                /\ m.dst = p
                                /\ m.col = "Red" })
            blueCount == Cardinality(
                            { m \in msgs :
                                /\ m.type = "reply"
                                /\ m.dst = p
                                /\ m.col = "Blue" })
        in
            if redCount >= PickFlipThreshold then
                color := [color EXCEPT ![hostNode] = "Red"];
            elsif blueCount >= PickFlipThreshold then
                color := [color EXCEPT ![hostNode] = "Blue"];
            end if;
        end let;

        (* remove the processed replies and clear the sample *)
        msgs   := { m \in msgs : ~ (m.type = "reply" /\ m.dst = p) };
        sample[p] := {};
        iter[p] := iter[p] + 1;
    end while;

    (* broadcast termination to all loop processes *)
    with lp \in SlushLoopProcess do
        msgs := msgs \cup {
            [type |-> "term",
             src  |-> p,
             dst  |-> lp,
             col  |-> NoColor]
        };
    end with;
end process;

process (Query(q \in SlushQueryProcess))
variables
    hostNode;
begin
    hostNode := NodeOfQuery(q);
    while TRUE do
        await \E m \in msgs :
                 /\ m.type = "query"
                 /\ m.dst  = q;

        with m \in msgs :
                 /\ m.type = "query"
                 /\ m.dst  = q
        do
            (* adopt the queried color if currently uncolored *)
            if color[hostNode] = NoColor then
                color := [color EXCEPT ![hostNode] = m.col];
            end if;

            (* send reply back to the loop process *)
            msgs := msgs \cup {
                [type |-> "reply",
                 src  |-> q,
                 dst  |-> m.src,
                 col  |-> color[hostNode]]
            };
            (* discard the processed query message *)
            msgs := msgs \ { m };
        end with;

        (* check whether termination messages from all loop processes have arrived *)
        if \A lp \in SlushLoopProcess :
               \E tm \in msgs :
                   /\ tm.type = "term"
                   /\ tm.dst  = q
                   /\ tm.src  = lp
        then
            (* consume termination messages and exit *)
            msgs := msgs \ { tm \in msgs :
                               /\ tm.type = "term"
                               /\ tm.dst = q };
            break;
        end if;
    end while;
end process;
end algorithm *)

vars == <<color, msgs, sample, iter>>

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs   \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter   \in [SlushLoopProcess -> Nat]

====