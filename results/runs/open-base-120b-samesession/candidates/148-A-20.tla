---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock,
    PubOfPriv, NodePriv

(* Sentinel aliases *)
NoHash == NoHashVal
NoBlock == NoBlockVal

(* ----------------------------------------------------------------------
   Block definition (record)
   ---------------------------------------------------------------------- *)
Block == [type   : {"genesis","send","receive","open","change"},
          prev   : Hash,
          account: PublicKey,
          dest   : PublicKey,
          amount : Nat,
          sig    : Nat]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES
    lastHash, ledger, received

(* ----------------------------------------------------------------------
   Cryptographic helpers (abstract)
   ---------------------------------------------------------------------- *)
Sign(priv, blk) ==
    blk.amount + 1

VerifySig(pub, blk, sig) ==
    sig = blk.amount + 1

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(* ----------------------------------------------------------------------
   Action: create a block and broadcast it
   ---------------------------------------------------------------------- *)
CreateBlock(node, blk) ==
    LET h == CalculateHash[blk, lastHash] IN
    /\ blk.account = PubOfPriv[NodePriv[node]]
    /\ blk.prev    = lastHash
    /\ blk.sig     = Sign(NodePriv[node], blk)
    /\ lastHash'   = h
    /\ ledger'     = [n \in Node |-> ledger[n] EXCEPT ![h] = blk]
    /\ received'   = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED node

(* ----------------------------------------------------------------------
   Action: process a received block
   ---------------------------------------------------------------------- *)
ProcessBlock(node) ==
    /\ \E h \in received[node] :
          LET blk == ledger[node][h] IN
          /\ blk # NoBlock
          /\ VerifySig(blk.account, blk, blk.sig)
    /\ received' = [n \in Node |-> IF n = node THEN received[n] \ {h} ELSE received[n]]
    /\ UNCHANGED <<lastHash, ledger>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E n \in Node, b \in Block :
          CreateBlock(n, b)
    \/ \E n \in Node :
          ProcessBlock(n)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger   \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h] IN
            blk = NoBlock \/ VerifySig(blk.account, blk, blk.sig)

(* ----------------------------------------------------------------------
   Operator for substitution in the .cfg file
   ---------------------------------------------------------------------- *)
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====