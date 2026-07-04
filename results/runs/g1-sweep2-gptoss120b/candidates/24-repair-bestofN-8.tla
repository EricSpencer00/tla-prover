---- MODULE BPConProof ----
(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

=============================================================================