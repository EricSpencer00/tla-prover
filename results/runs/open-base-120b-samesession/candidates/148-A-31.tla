---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash,
    NoHash, NoBlock

(* Additional constants for key handling; values are supplied in the .cfg or left uninterpreted *)
CONSTANT PubKeyOf   \* [PrivateKey -> PublicKey]
CONSTANT OwnerKey   \* [Node -> PrivateKey]

(* ------------------------------------------------------------------------- *)
(* Block definition                                                          *)
(* ------------------------------------------------------------------------- *)
Block == [ type   : {"Genesis","Send","Receive","Open","Change"},
           prev   : Hash \cup {NoHash},
           acct   : PublicKey,
           dest   : PublicKey \cup {NoHash},
           amount : Nat,
           sig    : PrivateKey,
           rep    : PublicKey \cup {NoHash} ]

(* ------------------------------------------------------------------------- *)
(* Variables                                                                 *)
(* ------------------------------------------------------------------------- *)
VARIABLES
    lastHash,       \* the most recent block hash (or NoHashVal)
    ledger,         \* per‑node copy of the ledger:  ledger[n][h] = block or NoBlockVal
    received,       \* per‑node set of hashes awaiting validation
    Blocks          \* global map from hash to its block data

vars == << lastHash, ledger, received, Blocks >>

(* ------------------------------------------------------------------------- *)
(* Initialization                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ Blocks   = [h \in Hash |-> NoBlockVal]

(* ------------------------------------------------------------------------- *)
(* Abstract hash calculation (to be overridden in the .cfg)                 *)
(* ------------------------------------------------------------------------- *)
CalculateHashImpl(prev, data) == CHOOSE h \in Hash : TRUE
CalculateHash(prev, data) == CalculateHashImpl(prev, data)

(* ------------------------------------------------------------------------- *)
(* Block‑construction helpers                                                *)
(* ------------------------------------------------------------------------- *)
MakeGenesisBlock(key) ==
    [ type   |-> "Genesis",
      prev   |-> NoHash,
      acct   |-> PubKeyOf[key],
      dest   |-> NoHash,
      amount |-> GenesisBalance,
      sig    |-> key,
      rep    |-> NoHash ]

MakeSendBlock(key, destKey, amt, prev) ==
    [ type   |-> "Send",
      prev   |-> prev,
      acct   |-> PubKeyOf[key],
      dest   |-> PubKeyOf[destKey],
      amount |-> amt,
      sig    |-> key,
      rep    |-> NoHash ]

MakeOpenBlock(key, srcHash, prev) ==
    [ type   |-> "Open",
      prev   |-> prev,
      acct   |-> PubKeyOf[key],
      dest   |-> NoHash,
      amount |-> 0,
      sig    |-> key,
      rep    |-> NoHash ]

MakeReceiveBlock(key, srcHash, prev) ==
    [ type   |-> "Receive",
      prev   |-> prev,
      acct   |-> PubKeyOf[key],
      dest   |-> NoHash,
      amount |-> 0,
      sig    |-> key,
      rep    |-> NoHash ]

MakeChangeBlock(key, newRep, prev) ==
    [ type   |-> "Change",
      prev   |-> prev,
      acct   |-> PubKeyOf[key],
      dest   |-> NoHash,
      amount |-> 0,
      sig    |-> key,
      rep    |-> PubKeyOf[newRep] ]

(* ------------------------------------------------------------------------- *)
(* Validation predicates                                                    *)
(* ------------------------------------------------------------------------- *)
ValidSignature(b) == PubKeyOf[b.sig] = b.acct

ValidateBlock(node, h) ==
    LET b == Blocks[h] IN
        /\ b # NoBlockVal
        /\ ValidSignature(b)
        /\ (b.prev = NoHash \/ \E hp \in Hash : ledger[node][hp] # NoBlockVal /\ hp = b.prev)

(* ------------------------------------------------------------------------- *)
(* Actions                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Genesis block – can happen only once *)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E key \in PrivateKey :
        LET blk == MakeGenesisBlock(key) IN
        LET h   == CalculateHash(NoHash, blk) IN
            /\ h \in Hash
            /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
            /\ lastHash' = h
            /\ ledger'   = [n \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE ledger[n][h2]]]
            /\ received' = [n \in Node |-> received[n] \cup {h}]
            /\ UNCHANGED <<>>

(* Send block creation *)
CreateSend ==
    /\ \E node \in Node :
        LET key   == OwnerKey[node] IN
        LET acct  == PubKeyOf[key] IN
        \E amt \in Nat :
            /\ amt <= GenesisBalance    \* simplified balance check
            LET blk == MakeSendBlock(key, key, amt, lastHash) IN
            LET h   == CalculateHash(lastHash, blk) IN
                /\ h \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
                /\ lastHash' = h
                /\ received' = [n \in Node |-> received[n] \cup {h}]
                /\ UNCHANGED ledger

(* Open block creation *)
CreateOpen ==
    /\ \E node \in Node :
        LET key  == OwnerKey[node] IN
        LET acct == PubKeyOf[key] IN
        \E srcHash \in Hash :
            LET blk == MakeOpenBlock(key, srcHash, lastHash) IN
            LET h   == CalculateHash(lastHash, blk) IN
                /\ h \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
                /\ lastHash' = h
                /\ received' = [n \in Node |-> received[n] \cup {h}]
                /\ UNCHANGED ledger

(* Receive block creation *)
CreateReceive ==
    /\ \E node \in Node :
        LET key  == OwnerKey[node] IN
        LET acct == PubKeyOf[key] IN
        \E srcHash \in Hash :
            LET blk == MakeReceiveBlock(key, srcHash, lastHash) IN
            LET h   == CalculateHash(lastHash, blk) IN
                /\ h \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
                /\ lastHash' = h
                /\ received' = [n \in Node |-> received[n] \cup {h}]
                /\ UNCHANGED ledger

(* Change representative block creation *)
CreateChange ==
    /\ \E node \in Node :
        LET key == OwnerKey[node] IN
        \E newRep \in PrivateKey :
            LET blk == MakeChangeBlock(key, newRep, lastHash) IN
            LET h   == CalculateHash(lastHash, blk) IN
                /\ h \in Hash
                /\ Blocks'   = [Blocks EXCEPT ![h] = blk]
                /\ lastHash' = h
                /\ received' = [n \in Node |-> received[n] \cup {h}]
                /\ UNCHANGED ledger

(* Process a received block on a node *)
ProcessBlock ==
    /\ \E node \in Node :
        /\ \E h \in received[node] :
            /\ ValidateBlock(node, h)
            /\ ledger'   = [ledger EXCEPT ![node][h] = Blocks[h]]
            /\ received' = [received EXCEPT ![node] = received[node] \ {h}]
            /\ UNCHANGED << lastHash, Blocks >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

Spec == Init /\ [] [Next]_vars

(* ------------------------------------------------------------------------- *)
(* Invariants                                                                *)
(* ------------------------------------------------------------------------- *)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger   \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ Blocks   \in [Hash -> (Block \cup {NoBlockVal})]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal
            THEN PubKeyOf[ledger[n][h].sig] = ledger[n][h].acct
            ELSE TRUE

====