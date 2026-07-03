------------------------------- MODULE Utils -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Functions, SequencesExt

\* IsSimpleCycle/SimpleCycle stripped for Apalache scratch copy -- unused by
\* EWD998Chan's Init/Next/TypeOK, and Apalache's parser rejects the nested
\* same-named RECURSIVE LET-binding (SanyParser: "two different declarations
\* with the same name [SimpleCycle]"). See APALACHE_FINDINGS.md spec 73 note.
=============================================================================
