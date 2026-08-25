---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

(* CONSTANTS *)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* State variables *)
VARIABLES pVote,               \* [participants -> {yes, no}]
          pAlive,              \* [participants -> BOOLEAN]
          pFaulty,             \* [participants -> BOOLEAN]
          pDecision,           \* [participants -> {undecided, commit, abort}]
          pSentVote,           \* [participants -> BOOLEAN]
          cAlive,              \* BOOLEAN
          cFaulty,             \* BOOLEAN
          cDecision,           \* {undecided, commit, abort}
          cRequested,          \* [participants -> BOOLEAN]
          cVoteRecv,           \* [participants -> {yes, no, waiting}]
          cBroadcastSent       \* [participants -> {notsent, commit, abort}]

vars == << pVote, pAlive, pFaulty, pDecision, pSentVote,
           cAlive, cFaulty, cDecision, cRequested, cVoteRecv, cBroadcastSent >>

(*=============================================================================
  Type invariant
=============================================================================