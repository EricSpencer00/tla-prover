---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock,
    PrivToPub, NodeKey

(* ----------------------------------------------------------------------
   Types and helper definitions
   ---------------------------------------------------------------------- *)

NoHash == NoHashVal
NoBlock == NoBlockVal

Block ==
    [type   : {"genesis","send","open","receive","change"},
     account: PublicKey,
     prev   : Hash \/ {NoHash},
     dest   : PublicKey \/ {NoHash},
     amount : Nat,
     rep    : PublicKey \/ {NoHash},
     source : Hash \/ {NoHash},
     hash   : Hash,
     sig    : PrivateKey]

VARIABLES
    lastHash, ledger, received

(* ledger : Node -> (Hash -> (Block \/ NoBlock)) *)
LedgerInit == [n \in Node |-> [h \in Hash |-> NoBlock]]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ lastHash = NoHash
    /\ ledger   = LedgerInit
    /\ received = [n \in Node |-> {}]

(* ----------------------------------------------------------------------
   Abstract balance and signature checks
   ---------------------------------------------------------------------- *)

Balance(account, l) ==
    (* Abstract balance – left uninterpreted for model checking. *)
    CHOOSE b \in Nat : TRUE

CanSend(account, amt, l) ==
    amt <= Balance(account, l)

ValidSignature(blk) ==
    PrivToPub(blk.sig) = blk.account

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET pk  == PrivToPub(NodeKey[n])
            h   == CalculateHash(<< "genesis", pk, GenesisBalance>>, NoHash)
            blk == [type    |-> "genesis",
                    account |-> pk,
                    prev    |-> NoHash,
                    dest    |-> NoHash,
                    amount  |-> GenesisBalance,
                    rep     |-> NoHash,
                    source  |-> NoHash,
                    hash    |-> h,
                    sig     |-> NodeKey[n]]
        IN
          /\ h # NoHash
          /\ lastHash' = h
          /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
          /\ received' = [m \in Node |-> {}]
          /\ UNCHANGED << >>

CreateSend ==
    /\ \E n \in Node, destPk \in PublicKey, amt \in Nat :
        LET pk   == PrivToPub(NodeKey[n])
            prev == lastHash
            h    == CalculateHash(<< "send", pk, prev, destPk, amt>>, prev)
            blk  == [type    |-> "send",
                     account |-> pk,
                     prev    |-> prev,
                     dest    |-> destPk,
                     amount  |-> amt,
                     rep     |-> NoHash,
                     source  |-> NoHash,
                     hash    |-> h,
                     sig     |-> NodeKey[n]]
        IN
          /\ CanSend(pk, amt, ledger)
          /\ lastHash' = h
          /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \in Node, srcHash \in Hash :
        LET pk   == PrivToPub(NodeKey[n])
            h    == CalculateHash(<< "open", pk, srcHash>>, NoHash)
            blk  == [type    |-> "open",
                     account |-> pk,
                     prev    |-> NoHash,
                     dest    |-> NoHash,
                     amount  |-> 0,
                     rep     |-> NoHash,
                     source  |-> srcHash,
                     hash    |-> h,
                     sig     |-> NodeKey[n]]
        IN
          /\ \E m \in Node :
                LET b == ledger[m][srcHash]
                IN b.type = "send" /\ b.dest = pk
          /\ lastHash' = h
          /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

CreateReceive ==
    /\ \E n \in Node, srcHash \in Hash :
        LET pk   == PrivToPub(NodeKey[n])
            h    == CalculateHash(<< "receive", pk, lastHash, srcHash>>, lastHash)
            blk  == [type    |-> "receive",
                     account |-> pk,
                     prev    |-> lastHash,
                     dest    |-> NoHash,
                     amount  |-> 0,
                     rep     |-> NoHash,
                     source  |-> srcHash,
                     hash    |-> h,
                     sig     |-> NodeKey[n]]
        IN
          /\ \E m \in Node :
                LET b == ledger[m][srcHash]
                IN b.type = "send" /\ b.dest = pk
          /\ lastHash' = h
          /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

CreateChange ==
    /\ \E n \in Node, newRep \in PublicKey :
        LET pk   == PrivToPub(NodeKey[n])
            h    == CalculateHash(<< "change", pk, lastHash, newRep>>, lastHash)
            blk  == [type    |-> "change",
                     account |-> pk,
                     prev    |-> lastHash,
                     dest    |-> NoHash,
                     amount  |-> 0,
                     rep     |-> newRep,
                     source  |-> NoHash,
                     hash    |-> h,
                     sig     |-> NodeKey[n]]
        IN
          /\ lastHash' = h
          /\ ledger'   = [m \in Node |-> [hh \in Hash |-> IF hh = h THEN blk ELSE ledger[m][hh]]]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
        LET blk == ledger[n][h]
        IN
          /\ blk # NoBlock
          /\ ValidSignature(blk)
          /\ ledger'   = ledger
          /\ received' = [m \in Node |-> IF m = n THEN received[m] \setminus {h} ELSE received[m]]
          /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHash}
    /\ ledger   \in [Node -> [Hash -> (Block \/ NoBlock)]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h]
            IN blk # NoBlock => ValidSignature(blk)

(* ----------------------------------------------------------------------
   Stub implementation for CalculateHashImpl (will replace CalculateHash)
   ---------------------------------------------------------------------- *)

CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====