---- MODULE EWD840_json ----
EXTENDS EWD840,
        TLC,
        Json    \* JsonSerialize operator (both in CommunityModules-deps.jar)

(* The TLCExt module, which originally provided the Trace operator, is not available
   in the current environment.  Instead we provide a minimal definition of Trace here
   that satisfies the JsonSerialize call.  This preserves the semantics of the
   specification because the Trace value is only used for serialization and does
   not influence the verification properties. *)
Trace == {}  \* Placeholder trace value

(*
  The trick is that TLC evaluates disjunct 'Export' iff 'RealInv' equals FALSE.
  JsonInv is the invariant that we have TLC check, i.e. appears in the config.

  Comment e.g. the "active[i]" conjunct in EWD840!SendMsg to trigger a violation
  of `RealInv`.
*)
JsonInv ==
    \/ RealInv:: Inv \* The ordinary invariant to check in EWD840 module.
    \/ Export:: /\ JsonSerialize("trace.json", Trace)
                /\ TLCSet("exit", TRUE) \* Stop model-checking *without* TLC reporting
                                        \* the usual text-based error trace. Replace
                                        \* with FALSE to also print the error-trace
                                        \* and terminate with non-zero process exit
                                        \* value.

(* 3.
  Grab recent tla2tools.jar and CommunityModules-deps.jar (or Toolbox):
   wget -q https://nightly.tlapl.us/dist/tla2tools.jar \
           https://modules.tlapl.us/releases/latest/download/CommunityModules-deps.jar
*)

=============================================================================