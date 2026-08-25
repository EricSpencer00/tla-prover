---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                      \* set of node identifiers
    SlushLoopProcess,          \* set of loop‑process identifiers (one per node)
    SlushQueryProcess,         \* set of query‑process identifiers (one per node)
    HostMapping,               \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,       \* number of iterations each loop process performs
    SampleSetSize,             \* size of the peer sample chosen each round
    PickFlipThreshold,         \* number of equal replies required to flip colour
    NoColor,                   \* special value meaning “uncoloured”
    NoMessage                  \* special value for “no message” (unused but required)

\* ----------------------------------------------------------------------
\* Helper functions derived from the constant HostMapping
\* ----------------------------------------------------------------------
LoopHost == [l \in SlushLoopProcess |-> 
                CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n,l,q>> \in HostMapping]

QueryHost == [q \in SlushQueryProcess |-> 
                CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n,l,q>> \in HostMapping]

QueryProcOfNode == [n \in Node |-> 
                CHOOSE q \in SlushQueryProcess : <<n, l, q>> \in HostMapping]

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(* --algorithm SlushAlg
variables
    color = [n \in Node |-> NoColor],
    msgs  = {},                                      \* set of messages
    pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "init"],
    sample = [l \in SlushLoopProcess |-> {}],        \* current sample set for each loop
    iter   = [l \in SlushLoopProcess |-> 0];         \* iteration counter for each loop

process (client = "client")
{
  while TRUE do
    if \E n \in Node : color[n] = NoColor then
      with n \in { n \in Node : color[n] = NoColor } do
        with c \in {"Red","Blue"} do
          color := [color EXCEPT ![n] = c];
        end with;
      end with;
    else
      pc := [pc EXCEPT !["client"] = "done"];
      break;
    end if;
  end while;
}

process (Loop = SlushLoopProcess)
{
  while TRUE do
    if color[LoopHost[self]] = NoColor then
      skip;                                   \* busy‑wait until the node gets a colour
    else
      if iter[self] < SlushIterationCount then
        \* ---- sample a peer set and send queries ---------------------------------
        with S \in SUBSET (Node \ {LoopHost[self]}) do
          /\ Cardinality(S) = SampleSetSize
          /\ sample  := [sample EXCEPT ![self] = S];
          /\ msgs    := msgs \cup
                        { << "query", self,
                           QueryProcOfNode[n],
                           color[LoopHost[self]] >> : n \in S };
        end with;

        \* ---- wait for all replies -----------------------------------------------
        await \A q \in { QueryProcOfNode[n] : n \in sample[self] } :
               \E m \in msgs : m[1] = "reply" /\ m[2] = q /\ m[3] = self;

        \* ---- tally replies and maybe flip colour --------------------------------
        let replies == { m \in msgs :
                           m[1] = "reply" /\ m[3] = self /\
                           m[2] \in { QueryProcOfNode[n] : n \in sample[self] } } in
          let cntRed  == Cardinality({ m \in replies : m[4] = "Red" }) in
          let cntBlue == Cardinality({ m \in replies : m[4] = "Blue" }) in
          if cntRed >= PickFlipThreshold then
            color := [color EXCEPT ![LoopHost[self]] = "Red"];
          elsif cntBlue >= PickFlipThreshold then
            color := [color EXCEPT ![LoopHost[self]] = "Blue"];
          else
            skip;
          end if;
        end let;

        \* ---- clean up for the next round ----------------------------------------
        sample := [sample EXCEPT ![self] = {}];
        iter   := [iter EXCEPT ![self] = @ + 1];
        msgs   := msgs \ { m \in msgs : m[1] = "reply" /\ m[3] = self };
      else
        \* ---- all iterations finished – broadcast termination --------------------
        msgs := msgs \cup { << "term", self, "all", NoColor >> };
        pc   := [pc EXCEPT ![self] = "done"];
        break;
      end if;
    end if;
  end while;
}

process (Query = SlushQueryProcess)
{
  while TRUE do
    \* ---- receive a query -------------------------------------------------------
    await \E m \in msgs : m[1] = "query" /\ m[3] = self;
    with m \in { m \in msgs : m[1] = "query" /\ m[3] = self } do
      \* possibly adopt the colour if still uncoloured
      let n == QueryHost[self] in
        if color[n] = NoColor then
          color := [color EXCEPT ![n] = m[4]];
        end if;
      \* send a reply back to the originating loop process
      msgs := msgs \cup { << "reply", self, m[2], color[n] >> };
      \* remove the processed query
      msgs := msgs \ { m };
    end with;

    \* ---- exit when every loop process has sent a termination message -----------
    if \A l \in SlushLoopProcess :
          \E t \in msgs : t[1] = "term" /\ t[2] = l then
      pc := [pc EXCEPT ![self] = "done"];
      break;
    end if;
  end while;
}
end algorithm; *)

\* ----------------------------------------------------------------------
\* Type invariant required by the configuration
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : color[n] \in {"Red","Blue", NoColor}
    /\ msgs \subseteq
        { <<t, s, d, c>> :
            t \in {"query","reply","term"} /\
            s \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) /\
            d \in (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}) /\
            c \in {"Red","Blue", NoColor} }

\* The PlusCal translation automatically defines Init, Next, and
\* the top‑level specification `Spec`.  We expose it under the required name.
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

====