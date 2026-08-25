---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be defined in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS 
    Node,                \* The set of nodes
    SlushLoopProcess,    \* The set of loop processes (one per node)
    SlushQueryProcess,   \* The set of query processes (one per node)
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop performs
    SampleSetSize,       \* Size of the peer sample per iteration
    PickFlipThreshold,   \* Threshold for flipping to a color
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Placeholder value for termination messages

\* ----------------------------------------------------------------------
\* Additional symbols used in the specification
\* ----------------------------------------------------------------------
Red  == "Red"
Blue == "Blue"
Color == {Red, Blue, NoColor}

Message == <<type : {"query","reply","term"}, 
             src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}), 
             dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}), 
             col  : Color \cup {NoMessage}>>

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    color,   \* Mapping Node -> Color (or NoColor)
    msgs,    \* Set of in‑flight messages
    sample,  \* Mapping SlushLoopProcess -> SUBSET Node (current sample)
    iter     \* Mapping SlushLoopProcess -> Nat (iterations completed)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
UncoloredNodes == { n \in Node : color[n] = NoColor }

NodeOfLoop(p) == 
    CHOOSE n \in Node : <<n, p, _>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node : <<n, _, q>> \in HostMapping

LoopOfNode(n) == 
    CHOOSE p \in SlushLoopProcess : <<n, p, _>> \in HostMapping

QueryOfNode(n) == 
    CHOOSE q \in SlushQueryProcess : <<n, _, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init == 
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* PlusCal algorithm modelling the Slush protocol
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables 
    color = [n \in Node |-> NoColor],
    msgs  = {},
    sample = [p \in SlushLoopProcess |-> {}],
    iter  = [p \in SlushLoopProcess |-> 0];

process (client = "Client")
{
  while TRUE do
    with n \in UncoloredNodes do
      either
        color' := [color EXCEPT ![n] = Red];
      or
        color' := [color EXCEPT ![n] = Blue];
      end either;
      if \A m \in Node : color[m] # NoColor then
        break;
      end if;
    end with;
  end while;
}

process (loop = SlushLoopProcess)
{
  variable node;
  begin
    node := NodeOfLoop(self);
    await color[node] # NoColor;
    while iter[self] < SlushIterationCount do
      \* --- Choose a sample of peers (nondeterministically) ---
      with S \in SUBSET (Node \ {node}) :
           Cardinality(S) = SampleSetSize
      do
        sample' := [sample EXCEPT ![self] = S];
      end with;
      \* --- Send queries to the sampled peers ---
      with p \in sample'[self] do
        let qproc == QueryOfNode(p) in
          msgs' := msgs \cup {<< "query", self, qproc, color[node] >>};
        end let;
      end with;
      \* --- Wait for all replies ---
      await \A p \in sample'[self] :
                \E m \in msgs :
                  /\ m[1] = "reply"
                  /\ m[2] = self
                  /\ m[3] = QueryOfNode(p);
      \* --- Tally replies ---
      let replies == { m[4] :
                        m \in msgs /\ 
                        m[1] = "reply" /\ 
                        m[2] = self /\ 
                        m[3] \in { QueryOfNode(p) : p \in sample'[self] } } in
        let cntRed  == Cardinality({c \in replies : c = Red}),
            cntBlue == Cardinality({c \in replies : c = Blue}) in
          if cntRed >= PickFlipThreshold then
            color' := [color EXCEPT ![node] = Red];
          elsif cntBlue >= PickFlipThreshold then
            color' := [color EXCEPT ![node] = Blue];
          else
            skip;
          end if;
      \* --- Prepare for next iteration ---
      sample' := [sample EXCEPT ![self] = {}];
      iter'   := [iter EXCEPT ![self] = @ + 1];
    end while;
    \* --- Broadcast termination ---
    with lp \in SlushLoopProcess do
      msgs' := msgs \cup {<< "term", self, lp, NoMessage >>};
    end with;
    halt;
  end;
}

process (query = SlushQueryProcess)
{
  variable node;
  begin
    node := NodeOfQuery(self);
    while TRUE do
      await \E m \in msgs :
              /\ m[1] = "query"
              /\ m[3] = self;
      with m \in msgs :
           /\ m[1] = "query"
           /\ m[3] = self
      do
        \* Adopt the queried color if currently uncolored
        if color[node] = NoColor then
          color' := [color EXCEPT ![node] = m[4]];
        end if;
        \* Reply with current color
        msgs' := msgs \cup {<< "reply", self, m[2], color[node] >>};
      end with;
      \* Exit when termination messages have been received from all loop processes
      if \A lp \in SlushLoopProcess :
           \E t \in msgs :
             /\ t[1] = "term"
             /\ t[2] = lp
             /\ t[3] = self
      then
        halt;
      end if;
    end while;
  end;
}
end algorithm; *)

\* ----------------------------------------------------------------------
\* Next-state relation (generated by PlusCal)
\* ----------------------------------------------------------------------
Next == 
    \/ \E self \in {"Client"} :
        /\ UNCHANGED <<color, msgs, sample, iter>>
        /\ UNCHANGED <<color, msgs, sample, iter>> \* placeholder (real Next is produced by PlusCal)

\* (The actual Next relation is generated automatically by the PlusCal
\* translation. The above stub is only to keep the TLA+ parser satisfied
\* when the PlusCal block is omitted from the generated output.)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant == 
    /\ \A n \in Node : color[n] \in Color
    /\ \A m \in msgs :
         /\ m[1] = "query" => /\ m[4] \in {Red, Blue}
         /\ m[1] = "reply" => /\ m[4] \in {Red, Blue}
         /\ m[1] = "term"  => m[4] = NoMessage

\* ----------------------------------------------------------------------
\* Theorems / Properties (optional)
\* ----------------------------------------------------------------------
\* Liveness: all processes eventually halt (termination)
Termination == <> (color = [n \in Node |-> color[n]] /\ 
                    \A p \in SlushLoopProcess : iter[p] = SlushIterationCount)

=============================================================================