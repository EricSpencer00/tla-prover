---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, inTransit

vars == <<lastHash, ledger, inTransit>>

NoHash == NoHashVal
NoBlock == NoBlockVal

InLedger(n, h) == \E x \in ledger[n] : x.hash = h
Matching(x) == \E y \in ledger[x.node] : y.hash = x.prevHash

RECURSIVE BalanceOf(_, _)
BalanceOf(chain, n) ==
  IF chain = <<>> THEN 0
  ELSE
    LET head == Head(chain) IN
    IF head.type = "receive" THEN BalanceOf(Tail(chain), n) + head.amount
    ELSE IF head.type = "send" THEN BalanceOf(Tail(chain), n) - head.amount
    ELSE BalanceOf(Tail(chain), n)

RECURSIVE Chain(_, _)
Chain(chain, n) ==
  IF chain = <<>> THEN <<>>
  ELSE
    LET head == Head(chain) IN
    IF head.owner = n THEN Chain(Tail(chain), n) \cup {head}
    ELSE Chain(Tail(chain), n)

Balance(n) == BalanceOf(Chain(<<>>, n), n)

RECURSIVE Claimed(_, _)
Claimed(sends, n) ==
  IF sends = <<>> THEN <<>>
  ELSE
    LET head == Head(sends) IN
    IF head.receiver = n THEN Claimed(Tail(sends), n) \cup {head}
    ELSE Claimed(Tail(sends), n)

TotalClaimed(n) == BalanceOf(Claimed(Chain(<<>>, n), n), n)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> {[hash |-> NoHash, node |-> n, owner |-> NoPublicKey, type |-> "genesis", prevHash |-> NoHash, amount |-> 0, signature |-> NoHash, publicKey |-> NoPublicKey] : FALSE}]
  /\ inTransit = [n \in Node |-> {}]

CreateGenesisBlock(p) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash(<<>>, GenesisBalance)
  /\ \A n \in Node :
       ledger' = [ledger EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "genesis", prevHash |-> NoHash, amount |-> GenesisBalance, signature |-> p, publicKey |-> publicOf(p)]}]
  /\ UNCHANGED inTransit

CreateSendBlock(p, amount) ==
  /\ lastHash # NoHash
  /\ ~\E x \in ledger : x.hash = CalculateHash(lastHash, amount)
  /\ Balance(publicOf(p)) >= amount
  /\ lastHash' = CalculateHash(lastHash, amount)
  /\ \A n \in Node :
       ledger' = [ledger EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "send", prevHash |-> lastHash, amount |-> amount, signature |-> p, publicKey |-> publicOf(p)]}]
  /\ \A n \in Node : inTransit' = [inTransit EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "send", prevHash |-> lastHash, amount |-> amount, signature |-> p, publicKey |-> publicOf(p)]}]

CreateOpenBlock(p) ==
  /\ lastHash # NoHash
  /\ ~\E x \in ledger : x.hash = CalculateHash(lastHash, 0)
  /\ \A block \in Chain(<<>>, publicOf(p)) : block.type # "send" \/ block.receiver # publicOf(p)
  /\ lastHash' = CalculateHash(lastHash, 0)
  /\ \A n \in Node :
       ledger' = [ledger EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "open", prevHash |-> noHash, amount |-> 0, signature |-> p, publicKey |-> publicOf(p)]}]
  /\ \A n \in Node : inTransit' = [inTransit EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "open", prevHash |-> noHash, amount |-> 0, signature |-> p, publicKey |-> publicOf(p)]}]

CreateReceiveBlock(p, amount) ==
  /\ lastHash # NoHash
  /\ ~\E x \in ledger : x.hash = CalculateHash(lastHash, amount)
  /\ \A block \in TotalClaimed(publicOf(p)) : block.amount # amount
  /\ lastHash' = CalculateHash(lastHash, amount)
  /\ \A n \in Node :
       ledger' = [ledger EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "receive", prevHash |-> lastHash, amount |-> amount, signature |-> p, publicKey |-> publicOf(p)]}]
  /\ \A n \in Node : inTransit' = [inTransit EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "receive", prevHash |-> lastHash, amount |-> amount, signature |-> p, publicKey |-> publicOf(p)]}]

CreateChangeBlock(p) ==
  /\ lastHash # NoHash
  /\ ~\E x \in ledger : x.hash = CalculateHash(lastHash, 0)
  /\ \A block \in Chain(<<>>, publicOf(p)) : block.type = "genesis" \/ block.type = "open"
  /\ lastHash' = CalculateHash(lastHash, 0)
  /\ \A n \in Node :
       ledger' = [ledger EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "change", prevHash |-> lastHash, amount |-> 0, signature |-> p, publicKey |-> publicOf(p)]}]
  /\ \A n \in Node : inTransit' = [inTransit EXCEPT ![n] = @ \cup {[hash |-> lastHash, node |-> n, owner |-> publicOf(p), type |-> "change", prevHash |-> lastHash, amount |-> 0, signature |-> p, publicKey |-> publicOf(p)]}]

Validate(n, block) ==
  /\ block \in inTransit[n]
  /\ block.publicKey = publicOf(block.signature)
  /\ Matching(block)
  /\ IF block.type = "send" THEN block.amount <= Balance(block.owner)
     ELSE IF block.type = "open" THEN ~\E x \in Chain(<<>>, block.publicKey) : x.type = "send" /\ x.receiver = block.publicKey
     ELSE IF block.type = "receive" THEN ~\E x \in TotalClaimed(block.owner) : x.amount = block.amount
     ELSE TRUE
  /\ ledger' = [ledger EXCEPT ![n] = @ \cup {block}]
  /\ inTransit' = [inTransit EXCEPT ![n] = @ \ {block}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E p \in PrivateKey : CreateGenesisBlock(p) \/ CreateChangeBlock(p)
  \/ \E p \in PrivateKey, amount \in 0..GenesisBalance : CreateSendBlock(p, amount) \/ CreateReceiveBlock(p, amount)
  \/ \E p \in PrivateKey : CreateOpenBlock(p)
  \/ \E n \in Node, block \in inTransit[n] : Validate(n, block)

Spec == Init /\ [][Next]_vars

TypeInvariant == /\ lastHash \in Hash \cup {NoHash}
                  /\ ledger \in [Node -> SUBSET (SUBSET (Hash \cup {NoHash} \X Node \X PublicKey \X {"genesis", "send", "open", "receive", "change"} \X (Hash \cup {NoHash}) \X (0..GenesisBalance) \X PrivateKey \X PublicKey))]
                  /\ inTransit \in [Node -> SUBSET (Hash \cup {NoHash} \X Node \X PublicKey \X {"genesis", "send", "open", "receive", "change"} \X (Hash \cup {NoHash}) \X (0..GenesisBalance) \X PrivateKey \X PublicKey)]

SafetyInvariant == \A n \in Node : \A block \in ledger[n] : block.signature \in PrivateKey /\ publicOf(block.signature) = block.publicKey

====