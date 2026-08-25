---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash, NoHash, NoBlock,
    PrivateKey, PublicKey,
    Node,
    GenesisBalance,
    NoHashVal, NoBlockVal,
    CalculateHash

VARIABLES lastHash, ledger, received

(* ------------------------------------------------------------------------ *)
(* Types and basic structures *)

BlockType == {"Genesis","Send","Open","Receive","Change"}

Block == [type      : BlockType,
          hash      : Hash,
          prev      : Hash,
          account   : PublicKey,
          dest      : PublicKey,
          amount    : Nat,
          signature : PrivateKey,
          rep       : PublicKey]

(* ------------------------------------------------------------------------ *)
(* Abstract hash calculation – to be overridden by the .cfg file *)

CalculateHashImpl(data, prev) == NoHash

(* Mapping from private to public keys – will be instantiated in a concrete model *)

ASSUME PrivateToPublic \in [PrivateKey -> PublicKey]

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)

SigValid(b) == PrivateToPublic[b.signature] = b.account

CreateBlock(node, sk, typ, amt, dst, rp) ==
    LET pk   == PrivateToPublic[sk] IN
    LET prev == lastHash IN
    LET h    == CalculateHash([typ, pk, amt, prev], prev) IN
    [type      |-> typ,
     hash      |-> h,
     prev      |-> prev,
     account   |-> pk,
     dest      |-> dst,
     amount    |-> amt,
     signature |-> sk,
     rep       |-> rp]

(* ------------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

(* ------------------------------------------------------------------------ *)
(* Actions *)

(* Genesis block – can be created only once *)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E sk \in PrivateKey :
          LET b == CreateBlock(Node, sk, "Genesis", GenesisBalance, NoHash, NoHash) IN
          /\ b.prev = NoHashVal
          /\ lastHash' = b.hash
          /\ ledger'   = [n \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]]
          /\ received' = received
          /\ UNCHANGED << >>

(* Broadcast a newly created block of any non‑genesis type *)
BroadcastBlock ==
    \E n \in Node, sk \in PrivateKey, typ \in BlockType \ {"Genesis"} :
        LET dst == IF typ = "Send" THEN CHOOSE pk \in PublicKey ELSE NoHash IN
        LET amt == IF typ \in {"Send","Receive"} THEN CHOOSE a \in Nat ELSE 0 IN
        LET rp  == IF typ = "Change" THEN CHOOSE pk \in PublicKey ELSE NoHash IN
        LET b   == CreateBlock(n, sk, typ, amt, dst, rp) IN
        /\ b.prev = lastHash
        /\ lastHash' = b.hash
        /\ ledger'   = ledger
        /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {b} ELSE received[m]]
        /\ UNCHANGED << >>

(* Process a received block that passes validation *)
ProcessBlock ==
    \E n \in Node, b \in received[n] :
        /\ SigValid(b)
        /\ (b.prev = NoHashVal) \/ \E h \in Hash :
               ledger[n][h] # NoBlockVal /\ ledger[n][h].hash = b.prev
        /\ ledger'   = [m \in Node |-> [h \in Hash |
                         IF h = b.hash THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> IF m = n THEN received[m] \ {b} ELSE received[m]]
        /\ UNCHANGED lastHash

Next == 
    \/ CreateGenesis
    \/ BroadcastBlock
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* ------------------------------------------------------------------------ *)
(* Invariants *)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger   \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Block]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET v == ledger[n][h] IN
            IF v # NoBlockVal THEN SigValid(v) ELSE TRUE

====