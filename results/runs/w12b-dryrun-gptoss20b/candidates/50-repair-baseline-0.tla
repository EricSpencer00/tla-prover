------------------------------- MODULE Synod -------------------------------

(* PATCHED (prove-TLA, corpus/configs/patches/50.tla) -- two fixes, both
   needed to make this checkable by TLC, full diagnosis in corpus/configs/PATCHES.md:
   (1) NotAnInput was `CHOOSE c : c \notin Inputs` (unbounded CHOOSE over the
       entire universe minus Inputs) -- TLC cannot evaluate this ("attempted
       to evaluate an unbounded CHOOSE"). Its exact identity is irrelevant to
       the algorithm (only used as a fresh sentinel distinct from all real
       Inputs values), so turned into a declared CONSTANT with an ASSUME,
       supplied a concrete model value via cfg (same idiom as the sibling
       DiskSynod/HDiskSynod family's own `NotAnInput = NotAnInput`).
   (2) Inner!IFail's `allInput = allInput \cup {ip}` was missing a prime on
       the LHS -- as written this is a vacuous boolean condition (true only
       when ip is already in allInput), not an assignment, leaving allInput'
       completely unconstrained whenever IFail is the disjunct taken ("TLC:
       Successor state is not completely specified... allInput"). Genuine
       corpus defect (byte-identical upstream, tla-examples never runs this
       through TLC either -- no .cfg ships with it there). Fixed to
       `allInput' = allInput \cup {ip}`.
   Both confirmed via live TLC error messages before fixing, not assumed. *)

EXTENDS Naturals

CONSTANTS N , Inputs, NotAnInput
ASSUME (N \in Nat) /\ (N > 0)
ASSUME NotAnInput \notin Inputs

Proc == 1..N

VARIABLES input, output

------------------------------- MODULE Inner -------------------------------

VARIABLES allInput, chosen

IInit == /\ input \in [Proc -> Inputs]
         /\ output = [p \in Proc |-> NotAnInput]
         /\ chosen = NotAnInput
         /\ allInput = {input[p] : p \in Proc}

IChoose(p) ==
  /\ output[p] = NotAnInput
  /\ IF chosen = NotAnInput
     THEN \E ip \in allInput : /\ chosen' = ip
                               /\ output' = [output EXCEPT ![p] = ip]
     ELSE /\ output' = [output EXCEPT ![p] = chosen]
          /\ UNCHANGED chosen
  /\ UNCHANGED <<input, allInput>>

IFail(p) ==
  /\ output' = [output EXCEPT ![p] = NotAnInput]
  /\ \E ip \in Inputs : /\ input' = [input EXCEPT ![p] = ip]
                        /\ allInput' = allInput \cup {ip}
  /\ UNCHANGED chosen

INext == \E p \in Proc : IChoose(p) \/ IFail (p)

ISpec == IInit /\ [][INext]_<<input, output, chosen, allInput>>

=============================================================================

IS(chosen, allInput) == INSTANCE Inner

SynodSpec == \EE chosen, allInput : IS(chosen, allInput)!ISpec



=============================================================================
\* ModIFication History
\* Last modIFied Sat Jan 26 14:27:38 CET 2019 by tthai
\* Created Sat Jan 26 14:17:53 CET 2019 by tthai
