---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

VARIABLES cand, cnt, i, seq

(* Import the main majority‑vote specification, providing the required
   substitutions for all of its parameters and state variables. *)
INSTANCE Majority WITH
    Value <- Value,
    cand  <- cand,
    cnt   <- cnt,
    i     <- i,
    seq   <- seq
====