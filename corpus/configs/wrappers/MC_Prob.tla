---- MODULE MC_Prob ----
(* Hand-authored (flagged since DRAFT_ITERATION.md's original W0.3 pass: "no
   zero-arity predicate exists to cite as INVARIANT... Flagged for MC wrapper
   adding a TypeOK"). Prob is a small, finite-state absorbing Markov chain
   (13 states: s0-s6, I-VI); p is always a 2-tuple <<numerator,
   denominator>> per the module's own `/` and `\odot` operators. *)
EXTENDS Prob
TypeOK == /\ state \in {"s0","s1","s2","s3","s4","s5","s6",
                         "I","II","III","IV","V","VI"}
          /\ p \in (Int \X Int)
====
