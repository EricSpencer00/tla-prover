---- MODULE Nano ----
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures or anything else that records action    *)
(* history in an ordered way.                                              *)
(***************************************************************************)

EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

(***************************************************************************)
(* Assumptions about the external constants                                 *)
(***************************************************************************)

ASSUME
    /\ \A data, oldHash, newHash :
          CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(* against public key.                                                     *)
(***************************************************************************)

Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data       |-> hash,
     signedWith |-> privateKey]

ValidateSignature(sig, expectedPub, expectedHash) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = expectedPub
    /\ sig.data = expectedHash

(***************************************************************************)
(* Defines the set of protocol-conforming blocks.                          *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type   |-> "genesis",
     account|-> PublicKey,
     balance|-> GenesisBalance]

SendBlock ==
    [type       |-> "send",
     previous   |-> Hash,
     balance    |-> AccountBalance,
     destination|-> PublicKey]

OpenBlock ==
    [type    |-> "open",
     account |-> PublicKey,
     source  |-> Hash,
     rep     |-> PublicKey]

ReceiveBlock ==
    [type    |-> "receive",
     previous|-> Hash,
     source  |-> Hash]

ChangeRepBlock ==
    [type    |-> "change",
     previous|-> Hash,
     rep     |-> PublicKey]

Block ==
    GenesisBlock
    \cup SendBlock
    \cup OpenBlock
    \cup ReceiveBlock
    \cup ChangeRepBlock

SignedBlock ==
    [block     : Block,
     signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock

NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

GenesisBlockExists ==
    lastHash /= NoHash

IsAccountOpen(ledger, pubKey) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb /= NoBlock
        /\ sb.block.type \in {"genesis", "open"}
        /\ sb.block.account = pubKey

IsSendReceived(ledger, srcHash) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb /= NoBlock
        /\ sb.block.type \in {"open", "receive"}
        /\ sb.block.source = srcHash

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h]
        b  == sb.block
    IN
    IF b.type \in {"genesis", "open"}
       THEN b.account
       ELSE PublicKeyOf(ledger, b.previous)

TopBlock(ledger, pubKey) ==
    CHOOSE h \in Hash :
        LET sb == ledger[h] IN
        sb /= NoBlock
        /\ PublicKeyOf(ledger, h) = pubKey
        /\ ~\E other \in Hash :
              LET osb == ledger[other] IN
              osb /= NoBlock
              /\ osb.block.type \in {"send", "receive", "change"}
              /\ osb.block.previous = h

RECURSIVE BalanceAt(_,_)
RECURSIVE ValueOfSendBlock(_,_)

BalanceAt(ledger, h) ==
    LET sb == ledger[h]
        b  == sb.block
    IN
    CASE b.type = "open"    -> ValueOfSendBlock(ledger, b.source)
    []   b.type = "send"    -> b.balance
    []   b.type = "receive" -> BalanceAt(ledger, b.previous) + ValueOfSendBlock(ledger, b.source)
    []   b.type = "change"  -> BalanceAt(ledger, b.previous)
    []   b.type = "genesis" -> b.balance

ValueOfSendBlock(ledger, h) ==
    LET sb == ledger[h]
        b  == sb.block
    IN BalanceAt(ledger, b.previous) - b.balance

(***************************************************************************)
(* Invariants                                                             *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    \A n \in Node :
        LET ledger == distributedLedger[n] IN
        \A h \in Hash :
            LET sb == ledger[h] IN
            sb /= NoBlock =>
                LET pub == PublicKeyOf(ledger, h) IN
                ValidateSignature(sb.signature, pub, h)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B \ {e})

BalanceInvariant ==
    \A n \in Node :
        LET ledger == distributedLedger[n] IN
        LET openAccs == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
        LET tops == {TopBlock(ledger, pk) : pk \in openAccs} IN
        LET balBag == {BalanceAt(ledger, h) : h \in tops} IN
        /\ GenesisBlockExists
        => SumBag(balBag) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Genesis block creation                                                  *)
(***************************************************************************)

CreateGenesisBlock(privKey) ==
    LET pubKey == KeyPair[privKey] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(GenesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |-> [h \in Hash |-> NoBlock] EXCEPT ![lastHash'] = 
            [block |-> [type |-> "genesis",
                       account |-> pubKey,
                       balance |-> GenesisBalance],
             signature |-> SignHash(lastHash', privKey)]]
    /\ UNCHANGED << received, lastHash >>

(***************************************************************************)
(* Open block actions                                                      *)
(***************************************************************************)

ValidateOpenBlock(ledger, blk) ==
    /\ blk.type = "open"
    /\ ledger[blk.source] /= NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = blk.account

CreateOpenBlock(node) ==
    LET privKey == Ownership[node] IN
    LET pubKey  == KeyPair[privKey] IN
    LET ledger  == distributedLedger[node] IN
    /\ \E rep \in PublicKey :
          \E src \in Hash :
              LET newBlk == [type |-> "open",
                             account |-> pubKey,
                             source |-> src,
                             rep |-> rep] IN
              /\ ValidateOpenBlock(ledger, newBlk)
              /\ CalculateHash(newBlk, lastHash, lastHash')
              /\ received' = [received EXCEPT ![node] = @ \cup
                                 {[block |-> newBlk,
                                   signature |-> SignHash(lastHash', privKey)}]]
              /\ UNCHANGED << distributedLedger, lastHash >>

ProcessOpenBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk    == sb.block IN
    /\ ValidateOpenBlock(ledger, blk)
    /\ ~IsAccountOpen(ledger, blk.account)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature, blk.account, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED << received, lastHash >>

(***************************************************************************)
(* Send block actions                                                      *)
(***************************************************************************)

ValidateSendBlock(ledger, blk) ==
    /\ blk.type = "send"
    /\ ledger[blk.previous] /= NoBlock
    /\ blk.balance <= BalanceAt(ledger, blk.previous)

CreateSendBlock(node) ==
    LET privKey == Ownership[node] IN
    LET pubKey  == KeyPair[privKey] IN
    LET ledger  == distributedLedger[node] IN
    /\ \E prev \in Hash :
          ledger[prev] /= NoBlock
          /\ PublicKeyOf(ledger, prev) = pubKey
          /\ \E dest \in PublicKey :
                \E bal  \in AccountBalance :
                    LET newBlk == [type |-> "send",
                                   previous |-> prev,
                                   balance |-> bal,
                                   destination |-> dest] IN
                    /\ ValidateSendBlock(ledger, newBlk)
                    /\ CalculateHash(newBlk, lastHash, lastHash')
                    /\ received' = [received EXCEPT ![node] = @ \cup
                                       {[block |-> newBlk,
                                         signature |-> SignHash(lastHash', privKey)}]]
                    /\ UNCHANGED << distributedLedger, lastHash >>

ProcessSendBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk    == sb.block IN
    /\ ValidateSendBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED << received, lastHash >>

(***************************************************************************)
(* Receive block actions                                                   *)
(***************************************************************************)

ValidateReceiveBlock(ledger, blk) ==
    /\ blk.type = "receive"
    /\ ledger[blk.previous] /= NoBlock
    /\ ledger[blk.source]   /= NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination =
        PublicKeyOf(ledger, blk.previous)

CreateReceiveBlock(node) ==
    LET privKey == Ownership[node] IN
    LET pubKey  == KeyPair[privKey] IN
    LET ledger  == distributedLedger[node] IN
    /\ \E prev \in Hash :
          ledger[prev] /= NoBlock
          /\ PublicKeyOf(ledger, prev) = pubKey
          /\ \E src \in Hash :
                LET newBlk == [type |-> "receive",
                               previous |-> prev,
                               source |-> src] IN
                /\ ValidateReceiveBlock(ledger, newBlk)
                /\ CalculateHash(newBlk, lastHash, lastHash')
                /\ received' = [received EXCEPT ![node] = @ \cup
                                   {[block |-> newBlk,
                                     signature |-> SignHash(lastHash', privKey)}]]
                /\ UNCHANGED << distributedLedger, lastHash >>

ProcessReceiveBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk    == sb.block IN
    /\ ValidateReceiveBlock(ledger, blk)
    /\ ~IsSendReceived(ledger, blk.source)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED << received, lastHash >>

(***************************************************************************)
(* Change representative block actions                                      *)
(***************************************************************************)

ValidateChangeBlock(ledger, blk) ==
    /\ blk.type = "change"
    /\ ledger[blk.previous] /= NoBlock

CreateChangeRepBlock(node) ==
    LET privKey == Ownership[node] IN
    LET pubKey  == KeyPair[privKey] IN
    LET ledger  == distributedLedger[node] IN
    /\ \E prev \in Hash :
          ledger[prev] /= NoBlock
          /\ PublicKeyOf(ledger, prev) = pubKey
          /\ \E newRep \in PublicKey :
                LET newBlk == [type |-> "change",
                               previous |-> prev,
                               rep |-> newRep] IN
                /\ ValidateChangeBlock(ledger, newBlk)
                /\ CalculateHash(newBlk, lastHash, lastHash')
                /\ received' = [received EXCEPT ![node] = @ \cup
                                   {[block |-> newBlk,
                                     signature |-> SignHash(lastHash', privKey)}]]
                /\ UNCHANGED << distributedLedger, lastHash >>

ProcessChangeRepBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk    == sb.block IN
    /\ ValidateChangeBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ UNCHANGED << received, lastHash >>

(***************************************************************************)
(* Top‑level actions                                                       *)
(***************************************************************************)

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E sb \in received[node] :
          (ProcessOpenBlock(node, sb)
           \/ ProcessSendBlock(node, sb)
           \/ ProcessReceiveBlock(node, sb)
           \/ ProcessChangeRepBlock(node, sb))
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E pk \in PrivateKey : CreateGenesisBlock(pk)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec ==
    Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

=============================================================================