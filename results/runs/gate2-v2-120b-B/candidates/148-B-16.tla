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

(***************************************************************************)
(* Constants that must be provided in the .cfg file.                       *)
(***************************************************************************)

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An uninterpreted action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The mapping from private key to public key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

(***************************************************************************)
(* Variables.                                                              *)
(***************************************************************************)

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

(***************************************************************************)
(* Helper definitions.                                                    *)
(***************************************************************************)

TypeOK ==
    /\ lastHash \in Hash \cup {"NoHash"}
    /\ distributedLedger \in [Node -> [Hash -> SignedBlock]]
    /\ received \in [Node -> SUBSET SignedBlock]

NoHash == "NoHash"

(***************************************************************************)
(* Record definitions.                                                    *)
(***************************************************************************)

Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

SignedBlock ==
    [block     : [type : {"genesis","send","open","receive","change"}],
               \* fields are added in the block constructors below
     signature : Signature]

NoBlock == [block |-> [type |-> "noBlock"], signature |-> [data |-> NoHash, signedWith |-> "NoPriv"]]

(***************************************************************************)
(* Cryptographic primitives (abstract).                                   *)
(***************************************************************************)

SignHash(hash, privateKey) ==
    [data |-> hash,
     signedWith |-> privateKey]

ValidateSignature(sig, pubKey, hash) ==
    /\ KeyPair[sig.signedWith] = pubKey
    /\ sig.data = hash

(***************************************************************************)
(* Block constructors.                                                    *)
(***************************************************************************)

GenesisBlock(pub) ==
    [type    |-> "genesis",
     account |-> pub,
     balance |-> GenesisBalance]

SendBlock(prevHash, bal, dest) ==
    [type       |-> "send",
     previous   |-> prevHash,
     balance    |-> bal,
     destination|-> dest]

OpenBlock(pub, srcHash, rep) ==
    [type    |-> "open",
     account |-> pub,
     source  |-> srcHash,
     rep     |-> rep]

ReceiveBlock(prevHash, srcHash) ==
    [type      |-> "receive",
     previous  |-> prevHash,
     source    |-> srcHash]

ChangeRepBlock(prevHash, newRep) ==
    [type      |-> "change",
     previous  |-> prevHash,
     rep       |-> newRep]

(***************************************************************************)
(* Ledger helper functions.                                               *)
(***************************************************************************)

PublicKeyOf(hash) ==
    LET blk == distributedLedger[CurrentNode][hash].block IN
    IF blk.type \in {"genesis","open"} THEN blk.account
    ELSE PublicKeyOf(blk.previous)

BalanceAt(hash) ==
    LET blk == distributedLedger[CurrentNode][hash].block IN
    CASE blk.type = "genesis" -> blk.balance
         [] blk.type = "open"   -> BalanceAt(blk.source)
         [] blk.type = "send"   -> blk.balance
         [] blk.type = "receive"-> BalanceAt(blk.previous) + (BalanceAt(blk.source) - BalanceAt(blk.previous))
         [] blk.type = "change" -> BalanceAt(blk.previous)
         [] OTHER               -> 0

(***************************************************************************)
(* Top-level actions.                                                     *)
(***************************************************************************)

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ UNCHANGED <<>>

CreateGenesisBlock(node) ==
    LET pub   == KeyPair[Ownership[node]] IN
    LET blk   == GenesisBlock(pub) IN
    LET hNew  == blk \* the abstract hash value for the block
    IN
    /\ lastHash = NoHash
    /\ distributedLedger' = [distributedLedger EXCEPT
                              ![node][hNew] = [block |-> blk,
                                                signature |-> SignHash(hNew, Ownership[node])]]
    /\ lastHash' = hNew
    /\ UNCHANGED <<received>>

CreateSendBlock(node) ==
    LET pub   == KeyPair[Ownership[node]] IN
    LET prev  == lastHash IN
    LET bal   == BalanceAt(prev) - 1 IN
    LET dest  == CHOOSE k \in PublicKey : k # pub IN
    LET blk   == SendBlock(prev, bal, dest) IN
    LET hNew  == blk IN
    /\ BalanceAt(prev) >= 1
    /\ distributedLedger' = [distributedLedger EXCEPT
                              ![node][hNew] = [block |-> blk,
                                                signature |-> SignHash(hNew, Ownership[node])]]
    /\ lastHash' = hNew
    /\ UNCHANGED <<received>>

CreateOpenBlock(node) ==
    LET pub   == KeyPair[Ownership[node]] IN
    LET src   == CHOOSE h \in Hash :
                  distributedLedger[node][h].block.type = "send" /\ 
                  distributedLedger[node][h].block.destination = pub IN
    LET rep   == CHOOSE k \in PublicKey : k # pub IN
    LET blk   == OpenBlock(pub, src, rep) IN
    LET hNew  == blk IN
    /\ distributedLedger' = [distributedLedger EXCEPT
                              ![node][hNew] = [block |-> blk,
                                                signature |-> SignHash(hNew, Ownership[node])]]
    /\ lastHash' = hNew
    /\ UNCHANGED <<received>>

CreateReceiveBlock(node) ==
    LET pub   == KeyPair[Ownership[node]] IN
    LET prev  == lastHash IN
    LET src   == CHOOSE h \in Hash :
                  distributedLedger[node][h].block.type = "send" /\
                  distributedLedger[node][h].block.destination = pub IN
    LET blk   == ReceiveBlock(prev, src) IN
    LET hNew  == blk IN
    /\ distributedLedger' = [distributedLedger EXCEPT
                              ![node][hNew] = [block |-> blk,
                                                signature |-> SignHash(hNew, Ownership[node])]]
    /\ lastHash' = hNew
    /\ UNCHANGED <<received>>

CreateChangeRepBlock(node) ==
    LET pub   == KeyPair[Ownership[node]] IN
    LET prev  == lastHash IN
    LET newRep== CHOOSE k \in PublicKey : k # pub IN
    LET blk   == ChangeRepBlock(prev, newRep) IN
    LET hNew  == blk IN
    /\ distributedLedger' = [distributedLedger EXCEPT
                              ![node][hNew] = [block |-> blk,
                                                signature |-> SignHash(hNew, Ownership[node])]]
    /\ lastHash' = hNew
    /\ UNCHANGED <<received>>

Next ==
    \/ \E n \in Node : CreateGenesisBlock(n)
    \/ \E n \in Node : CreateSendBlock(n)
    \/ \E n \in Node : CreateOpenBlock(n)
    \/ \E n \in Node : CreateReceiveBlock(n)
    \/ \E n \in Node : CreateChangeRepBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

=============================================================================