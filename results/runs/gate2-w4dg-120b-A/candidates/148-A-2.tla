---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash
AssumeNoBlock: NoBlock \notin Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Hash \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

TypeOK == TypeInvariant

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

NoBlockSigned == [hash |-> NoHash, prev |-> NoHash, who |-> NoHash, kind |-> "none", amt |-> 0]

IsSignedBy(b, owner) == b.kind # "none" /\ owner = (CHOOSE p \in PublicKey : <<p, owner>> \in PrivateKey)

BalanceOf(n, h) ==
    IF h = NoHash THEN 0
    ELSE LET b == ledger[n][h] IN
        LET base == IF b.prev = NoHash THEN 0 ELSE BalanceOf(n, b.prev) IN
            CASE b.kind = "send" -> base - b.amt
                 b.kind = "open" -> 0 + b.amt
                 b.kind = "receive" -> base + b.amt
                 b.kind = "chgrep" -> base
                 OTHER -> base

SumOfAllBalances ==
    LET ids == (Node \X Hash) \cup {<<Node, NoBlock>>} IN
    LET rec(S) ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN LET rest == S \ {x} IN
            LET bal == BalanceOf(x[1], x[2]) IN bal + rec(rest)
    IN rec(ids)

CreateGenesisBlock(priv) ==
    /\ ledger[CHOOSE n \in Node : <<priv, n>> \in PrivateKey] = [h \in Hash |-> NoBlockVal]
    /\ lastHash = NoHash
    /\ let owner == CHOOSE n \in Node : <<priv, n>> \in PrivateKey in
        LET b == CHOOSE bh \in Hash :
            /\ ledger[owner][bh] = NoBlockVal
            /\ bh = CalculateHash([owner |-> owner, prev |-> NoHash, kind |-> "send", amt |-> GenesisBalance])
        IN /\ lastHash' = b
           /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![b] = [hash |-> b, prev |-> NoHash, who |-> owner, kind |-> "send", amt |-> GenesisBalance]]]
           /\ received' = [n \in Node |-> {b}]
    /\ UNCHANGED <<>>

CreateSendBlock(n, hprev, amt) ==
    /\ ledger[n][hprev] # NoBlockVal
    /\ BalanceOf(n, hprev) >= amt
    /\ lastHash # NoHash
    /\ \E bh \in Hash :
         /\ ledger[n][bh] = NoBlockVal
         /\ bh = CalculateHash([owner |-> n, prev |-> hprev, kind |-> "send", amt |-> amt])
         /\ lastHash' = bh
         /\ ledger' = [Node |-> [ledger[Node] EXCEPT ![bh] = [hash |-> bh, prev |-> hprev, who |-> n, kind |-> "send", amt |-> amt]]]
         /\ received' = [Node |-> received[Node] \cup {bh}]
    /\ UNCHANGED <<>>

CreateOpenBlock(n, hsend) ==
    /\ ledger[n][hsend] # NoBlockVal
    /\ ledger[n][hsend].kind = "send"
    /\ ledger[n][hsend].who # n
    /\ \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].prev # hsend
    /\ lastHash # NoHash
    /\ \E bh \in Hash :
         /\ ledger[n][bh] = NoBlockVal
         /\ bh = CalculateHash([owner |-> n, prev |-> hsend, kind |-> "open", amt |-> 0])
         /\ lastHash' = bh
         /\ ledger' = [Node |-> [ledger[Node] EXCEPT ![bh] = [hash |-> bh, prev |-> hsend, who |-> n, kind |-> "open", amt |-> 0]]]
         /\ received' = [Node |-> received[Node] \cup {bh}]
    /\ UNCHANGED <<>>

CreateReceiveBlock(n, hprev, hsend) ==
    /\ ledger[n][hsend] # NoBlockVal
    /\ ledger[n][hsend].kind = "send"
    /\ ledger[n][hsend].who # n
    /\ ledger[n][hprev] # NoBlockVal
    /\ lastHash # NoHash
    /\ \E bh \in Hash :
         /\ ledger[n][bh] = NoBlockVal
         /\ bh = CalculateHash([owner |-> n, prev |-> hprev, kind |-> "receive", amt |-> ledger[n][hsend].amt, src |-> ledger[n][hsend].who])
         /\ lastHash' = bh
         /\ ledger' = [Node |-> [ledger[Node] EXCEPT ![bh] = [hash |-> bh, prev |-> hprev, who |-> n, kind |-> "receive", amt |-> ledger[n][hsend].amt, src |-> ledger[n][hsend].who]]]
         /\ received' = [Node |-> received[Node] \cup {bh}]
    /\ UNCHANGED <<>>

CreateChangeRepBlock(n, hprev) ==
    /\ ledger[n][hprev] # NoBlockVal
    /\ lastHash # NoHash
    /\ \E bh \in Hash :
         /\ ledger[n][bh] = NoBlockVal
         /\ bh = CalculateHash([owner |-> n, prev |-> hprev, kind |-> "chgrep", amt |-> 0])
         /\ lastHash' = bh
         /\ ledger' = [Node |-> [ledger[Node] EXCEPT ![bh] = [hash |-> bh, prev |-> hprev, who |-> n, kind |-> "chgrep", amt |-> 0]]]
         /\ received' = [Node |-> received[Node] \cup {bh}]
    /\ UNCHANGED <<>>

ValidateAndApply(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] = NoBlockVal
    /\ ledger' = [Node |-> [ledger[Node] EXCEPT ![h] = ledger[CHOOSE c \in Node : ledger[c][h] # NoBlockVal][h]]]
    /\ received' = [Node |-> [Node |-> IF Node = n THEN received[n] \ {h} ELSE received[Node]]]
    /\ UNCHANGED <<lastHash>>

Next ==
    \/ \E priv \in PrivateKey : CreateGenesisBlock(priv)
    \/ \E n \in Node, h \in Hash, amt \in 1..GenesisBalance : CreateSendBlock(n, h, amt)
    \/ \E n \in Node, hsend \in Hash : CreateOpenBlock(n, hsend)
    \/ \E n \in Node, hprev \in Hash, hsend \in Hash : CreateReceiveBlock(n, hprev, hsend)
    \/ \E n \in Node, hprev \in Hash : CreateChangeRepBlock(n, hprev)
    \/ \E n \in Node, h \in Hash : ValidateAndApply(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => IsSignedBy(ledger[n][h], n)

====