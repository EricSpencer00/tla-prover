---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers
    SlushQueryProcess,   \* set of query process identifiers
    HostMapping,         \* set of records [node : Node, loop : SlushLoopProcess, query : SlushQueryProcess]
    SlushIterationCount, \* number of iterations each loop process must perform
    SampleSetSize,       \* size of the sample taken each round
    PickFlipThreshold,   \* threshold for flipping color
    NoColor,             \* special value meaning "uncolored"
    NoMessage             \* special dummy message (unused but required)

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
ColorSet == {"Red", "Blue", NoColor}

MessageType == {"query", "reply", "term"}

AllProcs == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Msg == [type : MessageType, src : AllProcs, dst : AllProcs, color : ColorSet]

MessageSet == { [type |-> t, src |-> s, dst |-> d, color |-> c] :
                t \in MessageType,
                s \in AllProcs,
                d \in AllProcs,
                c \in ColorSet }

\* Mapping helpers based on HostMapping
NodeOfLoop(p) == 
    CHOOSE hm \in HostMapping : hm.loop = p

QueryOfNode(n) ==
    CHOOSE hm \in HostMapping : hm.node = n

QueryOfLoop(p) == QueryOfNode(NodeOfLoop(p))

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,   \* [Node -> ColorSet]
    msgs,     \* set of Msg
    sample,   \* [SlushLoopProcess -> SUBSET Node]   (current sample set)
    iter      \* [SlushLoopProcess -> Nat]           (iterations completed)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
--algorithm SlushAlg
variables colors = [n \in Node |-> NoColor],
          msgs   = {},
          sample = [p \in SlushLoopProcess |-> {}],
          iter   = [p \in SlushLoopProcess |-> 0];

begin
  client: while TRUE do
    if \E n \in Node : colors[n] = NoColor then
      with n \in { n \in Node : colors[n] = NoColor } do
        with c \in {"Red", "Blue"} do
          colors := [colors EXCEPT ![n] = c];
        end with;
      end with;
    else
      skip; \* all nodes already colored
    end if;
  end while;

  loop(p \in SlushLoopProcess): while iter[p] < SlushIterationCount do
    await colors[NodeOfLoop(p)] # NoColor;

    \* --- select a random sample of distinct peers (excluding self) ---
    with sampleSet \in SUBSET (Node \ {NodeOfLoop(p)}) do
      /\ Cardinality(sampleSet) = SampleSetSize
      do
        sample := [sample EXCEPT ![p] = sampleSet];
        \* send query to each sampled peer's query process
        with peers == { QueryOfNode(n) : n \in sampleSet } do
          msgs := msgs \cup {
                    [type |-> "query",
                     src  |-> p,
                     dst  |-> q,
                     color|-> colors[NodeOfLoop(p)]]
                    : q \in peers
                  };
        end with;
      end with;

    \* --- wait for all replies ---
    await \A n \in sample[p] :
            \E m \in msgs :
               /\ m.type = "reply"
               /\ m.dst  = p
               /\ m.src  = QueryOfNode(n);

    \* --- tally replies ---
    let reds  == Cardinality({
                 m \in msgs :
                    m.type = "reply" /\ m.dst = p /\ 
                    m.src \in { QueryOfNode(n) : n \in sample[p] } /\ m.color = "Red"
               });
        blues == Cardinality({
                 m \in msgs :
                    m.type = "reply" /\ m.dst = p /\ 
                    m.src \in { QueryOfNode(n) : n \in sample[p] } /\ m.color = "Blue"
               })
    in
      if reds >= PickFlipThreshold then
        colors := [colors EXCEPT ![NodeOfLoop(p)] = "Red"];
      elsif blues >= PickFlipThreshold then
        colors := [colors EXCEPT ![NodeOfLoop(p)] = "Blue"];
      else
        skip;
      end if;
    end let;

    \* clean up replies for this round
    msgs := { m \in msgs :
               ~(m.type = "reply" /\ m.dst = p) };

    \* prepare for next iteration
    sample := [sample EXCEPT ![p] = {}];
    iter   := [iter EXCEPT ![p] = @ + 1];
  end while;

  \* --- after completing all iterations, broadcast termination ---
  with termPeers == { QueryOfNode(n) : n \in Node } do
    msgs := msgs \cup {
               [type |-> "term",
                src  |-> p,
                dst  |-> q,
                color|-> NoColor]
               : q \in termPeers
            };
  end with;

  query(q \in SlushQueryProcess): while TRUE do
    if \E m \in msgs : m.type = "query" /\ m.dst = q then
      with m \in { m \in msgs : m.type = "query" /\ m.dst = q } do
        \* determine the node that hosts this query process
        with n == CHOOSE hm \in HostMapping : hm.query = q do
          if colors[n] = NoColor then
            colors := [colors EXCEPT ![n] = m.color];
          end if;
          msgs := (msgs \ {m}) \cup {
                    [type |-> "reply",
                     src  |-> q,
                     dst  |-> m.src,
                     color|-> colors[n]]
                 };
        end with;
      end with;
    elsif \E t \in msgs : t.type = "term" /\ t.dst = q then
      \* termination received – exit the query loop
      break;
    else
      skip;
    end if;
  end while;
end algorithm;
\* ----------------------------------------------------------------------
\* Next-state relation (generated by PlusCal)
\* ----------------------------------------------------------------------
Next == SlushAlg!Next

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> ColorSet]
    /\ msgs \subseteq MessageSet
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ \A hm \in HostMapping :
          /\ hm.node \in Node
          /\ hm.loop \in SlushLoopProcess
          /\ hm.query \in SlushQueryProcess
    /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
    /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

====