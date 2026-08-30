---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

PublicKeyOf == [k \in PrivateKey |-> [i \in 1..GenesisBalance |-> k]]
NoBlock == [hash |-> NoHash, account |-> NoHash, pred |-> NoHash, typ |-> "none", amt |-> 0, signer |-> NoHash]

VARIABLES lastHash, ledger, recv

vars == <<lastHash, ledger, recv>>

Balances == [Node -> Nat]

RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN Balances[x] + SumBalances(S \ {x})

BalanceChain(n, h) ==
    IF h = NoHash THEN 0
    ELSE LET b == ledger[n][h] IN
        IF b.typ = "send" THEN BalanceChain(n, b.pred) - b.amt
        ELSE IF b.typ = "receive" THEN BalanceChain(n, b.pred) + b.amt
        ELSE BalanceChain(n, b.pred)

TypeInvariant == /\ lastHash \in Hash \cup {NoHashVal}
                 /\ ledger \in [Node -> [Hash -> [hash : Hash \cup {NoHash}, account : Node \cup {NoHash}, pred : Hash \cup {NoHash}, typ : {"send", "receive", "open", "change", "none"}, amt : Nat, signer : PublicKey \cup {NoHash}]]]
                 /\ recv \in [Node -> SUBSET [hash : Hash, account : Node \cup {NoHash}, pred : Hash \cup {NoHash}, typ : {"send", "receive", "open", "change"}, amt : Nat, signer : PublicKey \cup {NoHash}]]

Init == /\ lastHash = NoHashVal
        /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
        /\ recv = [n \in Node |-> {}]

ValidateBlock(n, blk) ==
    /\ ledger[n][blk.hash] = NoBlock
    /\ ~ \E r \in recv[n] : r.hash = blk.hash
    /\ blk.signer = PublicKeyOf[blk.account]
    /\ IF blk.typ = "send" THEN BalanceChain(n, blk.pred) >= blk.amt ELSE TRUE
    /\ ledger[n][blk.pred] # NoBlock \/ blk.typ \in {"open", "commit"}

CreateGenesisBlock(nk) ==
    /\ lastHash = NoHashVal
    /\ \E h \in Hash :
         LET blk == [hash |-> h, account |-> nk, pred |-> NoHash, typ |-> "open", amt |-> GenesisBalance, signer |-> PublicKeyOf[nk]] IN
         /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
         /\ recv' = [n \in Node |-> recv[n] \cup {blk}]
    /\ lastHash' = NoHashVal

CreateSendBlock(nk, h, rc, amt) ==
    /\ \E prev \in Hash :
        /\ ledger[nk][prev] # NoBlock
        /\ ledger[nk][h] = NoBlock
        /\ amt \in 1..BalanceChain(nk, prev)
        /\ LET blk == [hash |-> h, account |-> nk, pred |-> prev, typ |-> "send", amt |-> amt, signer |-> PublicKeyOf[nk]] IN
           /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
           /\ recv' = [n \in Node |-> recv[n] \cup {blk}]
    /\ lastHash' = NoHashVal

CreateOpenBlock(nk, h, src, amt) ==
    /\ ledger[nk][h] = NoBlock
    /\ amt \in 1..GenesisBalance
    /\ LET blk == [hash |-> h, account |-> nk, pred |-> NoHash, typ |-> "open", amt |-> amt, signer |-> PublicKeyOf[nk]] IN
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
       /\ recv' = [n \in Node |-> recv[n] \cup {blk}]
    /\ lastHash' = NoHashVal

CreateReceiveBlock(nk, h, src) ==
    /\ ledger[nk][h] = NoBlock
    /\ \E prev \in Hash, amt \in 1..GenesisBalance :
        /\ ledger[nk][prev] # NoBlock
        /\ LET blk == [hash |-> h, account |-> nk, pred |-> prev, typ |-> "receive", amt |-> amt, signer |-> PublicKeyOf[nk]] IN
           /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
           /\ recv' = [n \in Node |-> recv[n] \cup {blk}]
    /\ lastHash' = NoHashVal

CreateChangeBlock(nk, h) ==
    /\ ledger[nk][h] = NoBlock
    /\ \E prev \in Hash :
        /\ ledger[nk][prev] # NoBlock
        /\ LET blk == [hash |-> h, account |-> nk, pred |-> prev, typ |-> "change", amt |-> 0, signer |-> PublicKeyOf[nk]] IN
           /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
           /\ recv' = [n \in Node |-> recv[n] \cup {blk}]
    /\ lastHash' = NoHashVal

Validate(n, blk) ==
    /\ ValidateBlock(n, blk)
    /\ ledger' = [ledger EXCEPT ![n][blk.hash] = blk]
    /\ recv' = [recv EXCEPT ![n] = recv[n] \ {blk}]
    /\ lastHash' = NoHashVal

Next == \/ \E nk \in PrivateKey : CreateGenesisBlock(nk)
        \/ \E nk \in PrivateKey, h \in Hash, rc \in Node, amt \in 1..GenesisBalance : CreateSendBlock(nk, h, rc, amt)
        \/ \E nk \in PrivateKey, h \in Hash, src \in Node, amt \in 1..GenesisBalance : CreateOpenBlock(nk, h, src, amt)
        \/ \E nk \in PrivateKey, h \in Hash, src \in Node : CreateReceiveBlock(nk, h, src)
        \/ \E nk \in PrivateKey, h \in Hash : CreateChangeBlock(nk, h)
        \/ \E n \in Node, blk \in recv[n] : Validate(n, blk)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlock => ledger[n][h].signer = PublicKeyOf[ledger[n][h].account]
====