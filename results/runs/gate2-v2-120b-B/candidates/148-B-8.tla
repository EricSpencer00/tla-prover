---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    KeyPair,
    Node,
    GenesisBalance,
    Ownership

VARIABLES
    lastHash,
    distributedLedger,
    received

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(* ------------------------------------------------------------------------ *)
(* Signatures and validation                                               *)
(* ------------------------------------------------------------------------ *)

Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPub, expectedHash) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = expectedPub
    /\ sig.data = expectedHash

(* ------------------------------------------------------------------------ *)
(* Block definitions                                                       *)
(* ------------------------------------------------------------------------ *)

AccountBalance == 0 .. GenesisBalance

GenesisBlock(publicKey) ==
    [type |-> "genesis",
     account |-> publicKey,
     balance |-> GenesisBalance]

SendBlock(prev, bal, dest) ==
    [type |-> "send",
     previous |-> prev,
     balance |-> bal,
     destination |-> dest]

OpenBlock(src, acct, rep) ==
    [type |-> "open",
     source |-> src,
     account |-> acct,
     rep |-> rep]

ReceiveBlock(prev, src) ==
    [type |-> "receive",
     previous |-> prev,
     source |-> src]

ChangeBlock(prev, rep) ==
    [type |-> "change",
     previous |-> prev,
     rep |-> rep]

Block == 
    [type : {"genesis", "send", "receive", "open", "change"}] \cup
    [type : {"genesis"}, account : PublicKey, balance : Nat] \cup
    [type : {"send"}, previous : Hash, balance : Nat, destination : PublicKey] \cup
    [type : {"open"}, source : Hash, account : PublicKey, rep : PublicKey] \cup
    [type : {"receive"}, previous : Hash, source : Hash] \cup
    [type : {"change"}, previous : Hash, rep : PublicKey]

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock
NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(* ------------------------------------------------------------------------ *)
(* Helper functions                                                        *)
(* ------------------------------------------------------------------------ *)

GenesisBlockExists == lastHash # NoHash

PublicKeyOf(ledger, h) ==
    IF ledger[h] = NoBlock THEN NoHash
    ELSE
        LET blk == ledger[h].block IN
        IF blk.type \in {"genesis", "open"} THEN blk.account
        ELSE PublicKeyOf(ledger, blk.previous)

BalanceAt(ledger, h) ==
    IF ledger[h] = NoBlock THEN 0
    ELSE
        LET blk == ledger[h].block IN
        CASE blk.type = "genesis" -> blk.balance
           [] blk.type = "send"    -> blk.balance
           [] blk.type = "receive" ->
                BalanceAt(ledger, blk.previous) +
                (BalanceAt(ledger, blk.source) - BalanceAt(ledger, blk.previous))
           [] blk.type = "open"    ->
                BalanceAt(ledger, blk.source)
           [] blk.type = "change"  -> BalanceAt(ledger, blk.previous)

IsAccountOpen(ledger, pub) ==
    \E h \in Hash :
        ledger[h] # NoBlock /\
        ledger[h].block.type \in {"genesis", "open"} /\
        ledger[h].block.account = pub

TopBlock(ledger, pub) ==
    CHOOSE h \in Hash :
        ledger[h] # NoBlock /\
        PublicKeyOf(ledger, h) = pub /\
        ~\E h2 \in Hash :
            ledger[h2] # NoBlock /\
            ledger[h2].block.type \in {"send", "receive", "change"} /\
            ledger[h2].block.previous = h

(* ------------------------------------------------------------------------ *)
(* Invariants                                                              *)
(* ------------------------------------------------------------------------ *)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A n \in Node :
        \A h \in Hash :
            LET sb == distributedLedger[n][h] IN
            sb # NoBlock =>
                LET pub == PublicKeyOf(distributedLedger[n], h) IN
                ValidateSignature(sb.signature, pub, h)

(* ------------------------------------------------------------------------ *)
(* Genesis creation                                                        *)
(* ------------------------------------------------------------------------ *)

CreateGenesisBlock(priv) ==
    LET pub == KeyPair[priv] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(GenesisBlock(pub), lastHash, lastHash')
    /\ distributedLedger' = [n \in Node |-> 
            [distributedLedger[n] EXCEPT ![lastHash'] = 
                [block |-> GenesisBlock(pub),
                 signature |-> SignHash(lastHash', priv)]]]
    /\ UNCHANGED received

(* ------------------------------------------------------------------------ *)
(* Block validation helpers                                                *)
(* ------------------------------------------------------------------------ *)

ValidateOpenBlock(ledger, blk) ==
    /\ blk.type = "open"
    /\ ledger[blk.source] # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = blk.account

ValidateSendBlock(ledger, blk) ==
    /\ blk.type = "send"
    /\ ledger[blk.previous] # NoBlock
    /\ blk.balance \in AccountBalance
    /\ blk.balance <= BalanceAt(ledger, blk.previous)

ValidateReceiveBlock(ledger, blk) ==
    /\ blk.type = "receive"
    /\ ledger[blk.previous] # NoBlock
    /\ ledger[blk.source] # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = 
         PublicKeyOf(ledger, blk.previous)

ValidateChangeBlock(ledger, blk) ==
    /\ blk.type = "change"
    /\ ledger[blk.previous] # NoBlock

(* ------------------------------------------------------------------------ *)
(* Block creation actions                                                  *)
(* ------------------------------------------------------------------------ *)

CreateOpenBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E src \in Hash :
        \E rep \in PublicKey :
            LET blk == OpenBlock(src, pub, rep) IN
            /\ ValidateOpenBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                {{block |-> blk,
                  signature |-> SignHash(lastHash', priv)}}]
            /\ UNCHANGED distributedLedger

CreateSendBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        PublicKeyOf(ledger, prev) = pub /\
        \E bal \in AccountBalance :
            \E dest \in PublicKey :
                LET blk == SendBlock(prev, bal, dest) IN
                /\ ValidateSendBlock(ledger, blk)
                /\ CalculateHash(blk, lastHash, lastHash')
                /\ received' = [received EXCEPT ![node] = @ \cup
                    {{block |-> blk,
                      signature |-> SignHash(lastHash', priv)}}]
                /\ UNCHANGED distributedLedger

CreateReceiveBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        PublicKeyOf(ledger, prev) = pub /\
        \E src \in Hash :
            LET blk == ReceiveBlock(prev, src) IN
            /\ ValidateReceiveBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                {{block |-> blk,
                  signature |-> SignHash(lastHash', priv)}}]
            /\ UNCHANGED distributedLedger

CreateChangeBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        PublicKeyOf(ledger, prev) = pub /\
        \E newRep \in PublicKey :
            LET blk == ChangeBlock(prev, newRep) IN
            /\ ValidateChangeBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, lastHash')
            /\ received' = [received EXCEPT ![node] = @ \cup
                {{block |-> blk,
                  signature |-> SignHash(lastHash', priv)}}]
            /\ UNCHANGED distributedLedger

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeBlock(node)

(* ------------------------------------------------------------------------ *)
(* Block processing actions                                                *)
(* ------------------------------------------------------------------------ *)

ProcessOpen(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateOpenBlock(ledger, blk)
    /\ ~IsAccountOpen(ledger, blk.account)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature, blk.account, lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]
    /\ UNCHANGED <<>>

ProcessSend(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateSendBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
         PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]
    /\ UNCHANGED <<>>

ProcessReceive(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateReceiveBlock(ledger, blk)
    /\ ~\E h \in Hash :
          ledger[h] # NoBlock /\ ledger[h].block.type = "receive" /\ ledger[h].block.source = blk.source
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
         PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]
    /\ UNCHANGED <<>>

ProcessChange(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateChangeBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, lastHash')
    /\ ValidateSignature(sb.signature,
         PublicKeyOf(ledger, blk.previous), lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]
    /\ UNCHANGED <<>>

ProcessBlock(node) ==
    \E sb \in received[node] :
        \/ ProcessOpen(node, sb)
        \/ ProcessSend(node, sb)
        \/ ProcessReceive(node, sb)
        \/ ProcessChange(node, sb)

(* ------------------------------------------------------------------------ *)
(* Initialization and next-step                                            *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E priv \in PrivateKey : CreateGenesisBlock(priv)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ CryptographicInvariant

====