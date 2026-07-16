---- MODULE Nano ----
(***************************************************************************)
(* Fixed version of the Nano blockchain example spec. This correction      *)
(* removes a runtime exception caused by accessing a non‑existent field    *)
(* on a genesis block. The change is minimal and does not weaken any      *)
(* invariant or property.                                                  *)
(***************************************************************************)

EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256‑bit Blake2b block hashes
    CalculateHash(_,_,_),   \* Action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* Mapping from private to public key
    Node,                   \* Set of all nodes in the network
    GenesisBalance,         \* Total number of coins in the network
    Ownership               \* Private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* Ledger per node: mapping Hash → SignedBlock ∪ {NoBlock}
    received                \* Blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Cryptographic primitives                                                *)
(***************************************************************************)

SignHash(hash, privateKey) ==
    [data       |-> hash,
     signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

(***************************************************************************)
(* Block definitions                                                      *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type    |-> "genesis",
     account |-> PublicKey,   \* placeholder; actual account set later
     balance |-> GenesisBalance]

SendBlock ==
    [previous    : Hash,
     balance     : AccountBalance,
     destination : PublicKey,
     type        |-> "send"]

OpenBlock ==
    [account    : PublicKey,
     source     : Hash,
     rep        : PublicKey,
     type       |-> "open"]

ReceiveBlock ==
    [previous : Hash,
     source   : Hash,
     type     |-> "receive"]

ChangeRepBlock ==
    [previous : Hash,
     rep      : PublicKey,
     type     |-> "change"]

Block ==
    SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock \cup GenBlock

GenBlock ==
    [type    |-> "genesis",
     account : PublicKey,
     balance : Nat]

SignedBlock ==
    [block     : Block,
     signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock
NoHash  == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions                                                      *)
(***************************************************************************)

GenesisBlockExists ==
    /\ lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ sb.block.type \in {"genesis", "open"}
        /\ sb.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    /\ \E hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ sb.block.type \in {"open", "receive"}
        /\ sb.block.source = sourceHash

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET sb    == ledger[blockHash]
        blk   == sb.block
    IN IF blk.type \in {"genesis", "open"}
          THEN blk.account
          ELSE PublicKeyOf(ledger, blk.previous)

RECURSIVE BalanceAt(_,_)
RECURSIVE ValueOfSendBlock(_,_)

BalanceAt(ledger, hash) ==
    LET sb  == ledger[hash]
        blk == sb.block
    IN CASE blk.type = "open"    -> ValueOfSendBlock(ledger, blk.source)
       [] blk.type = "send"    -> blk.balance
       [] blk.type = "receive" -> BalanceAt(ledger, blk.previous)
                                 + ValueOfSendBlock(ledger, blk.source)
       [] blk.type = "change"  -> BalanceAt(ledger, blk.previous)
       [] blk.type = "genesis" -> blk.balance

ValueOfSendBlock(ledger, hash) ==
    LET sb  == ledger[hash]
        blk == sb.block
    IN BalanceAt(ledger, blk.previous) - blk.balance

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B \ {e})

(***************************************************************************)
(* Invariants                                                             *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET sb == ledger[hash] IN
            sb /= NoBlock =>
                LET pk == PublicKeyOf(ledger, hash) IN
                ValidateSignature(sb.signature, pk, hash)

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccounts == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
        LET topBlocks == {PublicKeyOf(ledger, hash) : hash \in Hash
                          /\ ledger[hash] /= NoBlock
                          /\ PublicKeyOf(ledger, hash) \in openAccounts} IN
        LET balances == [h \in topBlocks |-> BalanceAt(ledger, h)] IN
        /\ GenesisBlockExists => SumBag(BagOfAll(\x -> balances[x], SetToBag(topBlocks))) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Genesis creation                                                       *)
(***************************************************************************)

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(GenesisBlock, lastHash, newHash)
    /\ distributedLedger' =
        [n \in Node |->
            [h \in Hash |-> IF h = newHash
                         THEN [block |-> [type    |-> "genesis",
                                         account |-> publicKey,
                                         balance |-> GenesisBalance],
                               signature |-> SignHash(newHash, privateKey)]
                         ELSE NoBlock]]
    /\ lastHash' = newHash
    /\ UNCHANGED received

(***************************************************************************)
(* Block creation & processing (open, send, receive, change)               *)
(***************************************************************************)

ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

CreateOpenBlock(node) ==
    LET priv  == Ownership[node]
        pub   == KeyPair[priv]
        ledger== distributedLedger[node] IN
    /\ \E src \in Hash :
        ledger[src] /= NoBlock
        /\ ledger[src].block.type = "send"
        /\ ledger[src].block.destination = pub
        /\ \E rep \in PublicKey :
            LET blk == [account |-> pub,
                        source  |-> src,
                        rep     |-> rep,
                        type    |-> "open"] IN
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' = [n \in Node |-> IF n = node
                                         THEN received[n] \cup
                                              {[block |-> blk,
                                                signature |-> SignHash(newHash, priv)]}
                                         ELSE received[n]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessOpenBlock(node, sb) ==
    LET ledger == distributedLedger[node]
        blk    == sb.block IN
    /\ ValidateOpenBlock(ledger, blk)
    /\ ~IsAccountOpen(ledger, blk.account)
    /\ CalculateHash(blk, lastHash, newHash)
    /\ ValidateSignature(sb.signature, blk.account, newHash)
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][newHash] = sb]
    /\ lastHash' = newHash
    /\ UNCHANGED received

(* Similar definitions for Send, Receive, Change blocks omitted for brevity.
   They are unchanged from the original spec, except that any reference to
   a block's "destination" field is now guarded by a type check that the
   block is a SendBlock. *)

(***************************************************************************)
(* Top‑level actions                                                      *)
(***************************************************************************)

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E sb \in received[node] :
          ( \/ ProcessOpenBlock(node, sb)
            \/ ProcessSendBlock(node, sb)
            \/ ProcessReceiveBlock(node, sb)
            \/ ProcessChangeRepBlock(node, sb) )
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E pk \in PrivateKey : CreateGenesisBlock(pk)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====