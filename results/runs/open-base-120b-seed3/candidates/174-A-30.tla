---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  CONSTANTS required by the .cfg file
--------------------------------------------------------------------*)
CONSTANTS
  Node,                  \* set of node identifiers
  SlushLoopProcess,      \* set of loop process identifiers
  SlushQueryProcess,     \* set of query process identifiers
  HostMapping,           \* set of triples <<node, loop, query>>
  SlushIterationCount,   \* number of iterations each loop performs
  SampleSetSize,         \* size of the random peer sample
  PickFlipThreshold,     \* threshold to flip to a color
  NoColor,               \* sentinel for an uncolored node
  NoMessage              \* sentinel for fields not used in a message

(*--------------------------------------------------------------------
  Simple auxiliary definitions
--------------------------------------------------------------------*)
Colors == {"Red", "Blue"}

Message == [type  : {"query", "reply", "term"},
            from  : (SlushLoopProcess \cup SlushQueryProcess),
            to    : (SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage}),
            color : (Colors \cup {NoColor, NoMessage})]

(*--------------------------------------------------------------------
  Helper functions extracting the host mapping
--------------------------------------------------------------------*)
NodeOfLoop(l) == CHOOSE n \in Node :
                  \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

QueryOfLoop(l) == CHOOSE q \in SlushQueryProcess :
                    <<NodeOfLoop(l), l, q>> \in HostMapping

NodeOfQuery(q) == CHOOSE n \in Node :
                    \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

(*--------------------------------------------------------------------
  PlusCal algorithm describing the behavior
--------------------------------------------------------------------*)
(* --algorithm SlushAlg
variables
  color     = [n \in Node |-> NoColor],
  msgs      = {},
  iter      = [p \in SlushLoopProcess |-> 0],
  sample    = [p \in SlushLoopProcess |-> {}],
  termCount = 0;

process (client = "client")
begin
  while \E n \in Node : color[n] = NoColor do
    with n \in Node do
      assume color[n] = NoColor;
    end with;
    with c \in Colors do
      skip;
    end with;
    color := [color EXCEPT ![n] = c];
  end while;
end process;

process (Loop(p \in SlushLoopProcess))
variables
  myNode, myQuery;
begin
  myNode  := NodeOfLoop(p);
  myQuery := QueryOfLoop(p);
  await color[myNode] # NoColor;
  while iter[p] < SlushIterationCount do
    (* choose a random sample of peers *)
    sample[p] := CHOOSE S \in SUBSET SlushQueryProcess :
                   Cardinality(S) = SampleSetSize /\ myQuery \notin S;
    (* send query messages to the sampled peers *)
    with q \in sample[p] do
      msgs := msgs \cup {
                [type |-> "query",
                 from |-> p,
                 to   |-> q,
                 color|-> color[myNode]]
              };
    end with;
    (* wait until a reply from each sampled peer has arrived *)
    await \A q \in sample[p] :
            \E m \in msgs :
               m.type = "reply" /\ m.from = q /\ m.to = p;
    (* tally the replies *)
    let reds  == Cardinality({ q \in sample[p] :
                                 \E m \in msgs :
                                   m.type = "reply" /\ m.from = q /\ m.to = p /\ m.color = "Red" }),
        blues == Cardinality({ q \in sample[p] :
                                 \E m \in msgs :
                                   m.type = "reply" /\ m.from = q /\ m.to = p /\ m.color = "Blue" })
    in
      if reds >= PickFlipThreshold then
        color := [color EXCEPT ![myNode] = "Red"];
      elsif blues >= PickFlipThreshold then
        color := [color EXCEPT ![myNode] = "Blue"];
      else
        skip;
      end if;
    end let;
    (* prepare for the next iteration *)
    sample[p] := {};
    iter[p]   := iter[p] + 1;
  end while;
  (* broadcast termination *)
  msgs := msgs \cup {
            [type  |-> "term",
             from  |-> p,
             to    |-> NoMessage,
             color |-> NoMessage]
          };
  termCount := termCount + 1;
end process;

process (Query(q \in SlushQueryProcess))
variables
  myNode;
begin
  myNode := NodeOfQuery(q);
  while termCount < Cardinality(SlushLoopProcess) do
    await \E m \in msgs :
            m.type = "query" /\ m.to = q;
    with m \in msgs do
      assume m.type = "query" /\ m.to = q;
    end with;
    (* adopt the queried color if still uncolored *)
    if color[myNode] = NoColor then
      color := [color EXCEPT ![myNode] = m.color];
    end if;
    (* reply to the sender *)
    msgs := msgs \cup {
              [type  |-> "reply",
               from  |-> q,
               to    |-> m.from,
               color |-> color[myNode]]
            };
    (* remove the processed query message *)
    msgs := msgs \ { m };
  end while;
end process;

end algorithm *)

(*--------------------------------------------------------------------
  TLA+ level definitions derived from the PlusCal translation
--------------------------------------------------------------------*)
Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs  = {}
  /\ iter  = [p \in SlushLoopProcess |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ termCount = 0

Next == SlushAlg!Next

Vars == <<color, msgs, iter, sample, termCount>>

Spec == Init /\ [][Next]_Vars

(*--------------------------------------------------------------------
  Type invariant required by the .cfg file
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ color \in [Node -> (Colors \cup {NoColor})]
  /\ msgs \subseteq Message
  /\ \A m \in msgs :
        (m.type = "query" =>
           /\ m.from \in SlushLoopProcess
           /\ m.to   \in SlushQueryProcess
           /\ m.color \in Colors)
     /\ (m.type = "reply" =>
           /\ m.from \in SlushQueryProcess
           /\ m.to   \in SlushLoopProcess
           /\ m.color \in Colors)
     /\ (m.type = "term" =>
           /\ m.from \in SlushLoopProcess
           /\ m.to   = NoMessage
           /\ m.color = NoMessage)

====