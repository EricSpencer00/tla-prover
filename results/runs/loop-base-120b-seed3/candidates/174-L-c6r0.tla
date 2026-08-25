---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,\* set of node identifiers
    SlushLoopProcess,\* set of loop process identifiers (one per node)
    SlushQueryProcess,\* set of query process identifiers (one per node)
    HostMapping,\* a set of records [loop: SlushLoopProcess, query: SlushQueryProcess, node: Node]
    SlushIterationCount,\* number of iterations each loop process must perform
    SampleSetSize,\* size of the peer sample taken each iteration
    PickFlipThreshold,\* threshold for flipping the node's color
    NoColor,\* special value meaning “uncolored”
    NoMessage \* unused sentinel (required by the .cfg)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            col  : (Colors \cup {NoColor})]

LoopNode(l) == CHOOSE h \in HostMapping : h.loop = l
QueryNode(q) == CHOOSE h \in HostMapping : h.query = q
NodeOfLoop(l) == LoopNode(l).node
NodeOfQuery(q) == QueryNode(q).node

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
--algorithm SlushAlg
variables
    color = [n \in Node |-> NoColor],
    msgs  = {},
    sample = [l \in SlushLoopProcess |-> {}],
    iter  = [l \in SlushLoopProcess |-> 0];
process (client = "client")
begin
    while \E n \in Node : color[n] = NoColor do
        with n \in Node do
            assume color[n] = NoColor;
            either
                color := [color EXCEPT ![n] = "Red"]
            or
                color := [color EXCEPT ![n] = "Blue"]
            end either;
        end with;
    end while;
end process;

process (loop = SlushLoopProcess)
variables myNode;
begin
    myNode := NodeOfLoop(self);
    await color[myNode] # NoColor;
    while iter[self] < SlushIterationCount do
        \* ---- pick a random sample of peers ---------------------------------
        sample := [sample EXCEPT ![self] = 
                     choose s \subseteq (Node \ {myNode}) :
                         Cardinality(s) = SampleSetSize];
        \* ---- send a query to each sampled peer -----------------------------
        with n \in sample[self] do
            with q = (CHOOSE h \in HostMapping : h.node = n).query do
                msgs := msgs \cup {[type |-> "query",
                                    src  |-> self,
                                    dst  |-> q,
                                    col  |-> color[myNode]]};
            end with;
        end with;
        \* ---- wait for all replies -----------------------------------------
        await \A n \in sample[self] :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst  = self
                    /\ m.src  = (CHOOSE h \in HostMapping : h.node = n).query;
        \* ---- tally the replies --------------------------------------------
        let reds  == Cardinality({ m \in msgs :
                                   /\ m.type = "reply"
                                   /\ m.dst  = self
                                   /\ m.col  = "Red" });
            blues == Cardinality({ m \in msgs :
                                   /\ m.type = "reply"
                                   /\ m.dst  = self
                                   /\ m.col  = "Blue" })
        in
            if reds >= PickFlipThreshold then
                color := [color EXCEPT ![myNode] = "Red"];
            elsif blues >= PickFlipThreshold then
                color := [color EXCEPT ![myNode] = "Blue"];
            end if;
        \* ---- clean up replies and prepare for next round -------------------
        msgs   := { m \in msgs : ~(m.type = "reply" /\ m.dst = self) };
        sample := [sample EXCEPT ![self] = {}];
        iter   := [iter EXCEPT ![self] = @ + 1];
    end while;
    \* ---- broadcast termination -------------------------------------------
    with q \in SlushQueryProcess do
        msgs := msgs \cup {[type |-> "term",
                            src  |-> self,
                            dst  |-> q,
                            col  |-> NoColor]};
    end with;
end process;

process (query = SlushQueryProcess)
variables myNode;
begin
    myNode := NodeOfQuery(self);
    while TRUE do
        with m \in msgs do
            assume m.type = "query" /\ m.dst = self;
            \* adopt the queried color if still uncolored
            if color[myNode] = NoColor then
                color := [color EXCEPT ![myNode] = m.col];
            end if;
            \* reply to the sender
            msgs := (msgs \ {m}) \cup {[type |-> "reply",
                                        src  |-> self,
                                        dst  |-> m.src,
                                        col  |-> color[myNode]]};
        end with;
    end while;
end process;
end algorithm;

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs  \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]
    /\ \A l \in SlushLoopProcess :
          Cardinality(sample[l]) <= SampleSetSize
    /\ \A l \in SlushLoopProcess :
          iter[l] <= SlushIterationCount

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_(<<color, msgs, sample, iter>>)

====