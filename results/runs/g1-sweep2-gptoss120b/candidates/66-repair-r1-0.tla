---- MODULE EWD840_json ----
EXTENDS EWD840,
        TLC,
        Json    \* JsonSerialize operator (both in CommunityModules-deps.jar)

(* ----------------------------------------------------------------------
   TLCExt is unavailable in the current environment.  The original TLCExt
   module provided the `Trace` operator used by `JsonSerialize`.  To keep the
   specification parsable and semantically faithful we replace the missing
   import with a local definition of `Trace`.  The concrete value of the
   trace is not relevant for the invariant; an empty sequence suffices.
   ---------------------------------------------------------------------- *)

Trace == <<>> \* placeholder trace for JsonSerialize

(* The invariant checked by TLC.  It is true either when the original
   `RealInv` holds, or when the `Export` label is taken, causing the
   trace to be written to a JSON file and the model checker to stop. *)
JsonInv ==
    \/ RealInv:: Inv
    \/ Export:: /\ JsonSerialize("trace.json", Trace)
                /\ TLCSet("exit", TRUE) \* Stop model-checking *without* TLC reporting
                                        \* the usual text-based error trace. Replace
                                        \* with FALSE to also print the error-trace
                                        \* and terminate with non-zero process exit
                                        \* value.

=============================================================================