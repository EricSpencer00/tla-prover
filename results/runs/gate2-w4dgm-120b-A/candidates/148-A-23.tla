---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Hash,
  NoHashVal,
  PrivateKey,
  PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal,
  CalculateHash,
  NoHash,
  NoBlock

EMPTY == "empty"
Account == PublicKey

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

BlockTypes == {"genesis", "send", "open", "receive", "changeRep"}

\* A signed block: its chain owner, its type, the previous link in the chain,
\* an optional second link (for receive), the amount moved, and the signature.
Blocks == [account : Account,
           type : BlockTypes,
           link1 : Hash \cup {NoHash},
           link2 : Hash \cup {NoHash},
           amount : 0..GenesisBalance,
           signature : PublicKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Blocks \cup {EMPTY}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> EMPTY]]
  /\ received = [n \in Node |-> {}]

\* Genesis block: posted to every node's ledger immediately, no reception step.
CreateGenesisBlock(creator) ==
  /\ lastHash = NoHash
  /\ creator \in PrivateKey
  /\ LET h == CalculateHash([type |-> "genesis", link1 |-> NoHash,
                             link2 |-> NoHash, amount |-> GenesisBalance])
         blk == [account |-> PublicKey[creator], type |-> "genesis",
                 link1 |-> NoHash, link2 |-> NoHash,
                 amount |-> GenesisBalance, signature |-> PublicKey[creator]]
     IN /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
        /\ UNCHANGED received

CreateSendBlock(sender, recipient, amt) ==
  /\ sender \in PrivateKey
  /\ recipient \in Account
  /\ amt \in 1..GenesisBalance
  /\ ledger[Node[sender]][lastHash].account = PublicKey[sender]
  /\ Balance(ledger, Node[sender], lastHash) >= amt
  /\ LET h == CalculateHash([type |-> "send", link1 |-> lastHash,
                             link2 |-> NoHash, amount |-> amt])
         blk == [account |-> PublicKey[sender], type |-> "send",
                 link1 |-> lastHash, link2 |-> NoHash,
                 amount |-> amt, signature |-> PublicKey[sender]]
     IN /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateOpenBlock(creator, recvHash) ==
  /\ creator \in PrivateKey
  /\ recvHash \in Hash
  /\ ledger[Node[creator]][recvHash].type = "send"
  /\ ledger[Node[creator]][recvHash].account = PublicKey[creator]
  /\ ledger[Node[creator]][recvHash].signature = PublicKey[creator]
  /\ LET h == CalculateHash([type |-> "open", link1 |-> recvHash,
                             link2 |-> NoHash, amount |-> EMPTY])
         blk == [account |-> PublicKey[creator], type |-> "open",
                 link1 |-> recvHash, link2 |-> NoHash,
                 amount |-> EMPTY, signature |-> PublicKey[creator]]
     IN /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateReceiveBlock(creator, recvHash) ==
  /\ creator \in PrivateKey
  /\ recvHash \in Hash
  /\ ledger[Node[creator]][recvHash].type = "send"
  /\ ledger[Node[creator]][recvHash].account # PublicKey[creator]
  /\ ledger[Node[creator]][recvHash].signature = PublicKey[creator]
  /\ ledger[Node[creator]][lastHash].account = PublicKey[creator]
  /\ LET h == CalculateHash([type |-> "receive", link1 |-> lastHash,
                             link2 |-> recvHash, amount |-> EMPTY])
         blk == [account |-> PublicKey[creator], type |-> "receive",
                 link1 |-> lastHash, link2 |-> recvHash,
                 amount |-> EMPTY, signature |-> PublicKey[creator]]
     IN /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateChangeRepBlock(creator) ==
  /\ creator \in PrivateKey
  /\ ledger[Node[creator]][lastHash].account = PublicKey[creator]
  /\ LET h == CalculateHash([type |-> "changeRep", link1 |-> lastHash,
                             link2 |-> NoHash, amount |-> EMPTY])
         blk == [account |-> PublicKey[creator], type |-> "changeRep",
                 link1 |-> lastHash, link2 |-> NoHash,
                 amount |-> EMPTY, signature |-> PublicKey[creator]]
     IN /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]

ValidateSendBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].signature = ledger[n][h].account
  /\ ledger[n][h].link1 = lastHash
  /\ ledger[n][lastHash].account = ledger[n][h].account
  /\ Balance(ledger, n, lastHash) >= ledger[n][h].amount
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

ValidateOpenBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].type = "open"
  /\ ledger[n][h].signature = ledger[n][h].account
  /\ ledger[n][h].link1 = h
  /\ ledger[n][h].link2 = NoHash
  /\ ledger[n][h].account = ledger[n][h].account
  /\ ledger[n][ledger[n][h].link1].type = "send"
  /\ ledger[n][ledger[n][h].link1].account = h
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

ValidateReceiveBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].type = "receive"
  /\ ledger[n][h].signature = ledger[n][h].account
  /\ ledger[n][h].link2 # NoHash
  /\ ledger[n][ledger[n][h].link2].type = "send"
  /\ ledger[n][ledger[n][h].link2].account # ledger[n][h].account
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

ValidateChangeRepBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].type = "changeRep"
  /\ ledger[n][h].signature = ledger[n][h].account
  /\ ledger[n][h].link1 = lastHash
  /\ ledger[n][lastHash].account = ledger[n][h].account
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E creator \in PrivateKey : CreateGenesisBlock(creator)
  \/ \E sender \in PrivateKey, recipient \in Account, amt \in 1..GenesisBalance :
       CreateSendBlock(sender, recipient, amt)
  \/ \E creator \in PrivateKey, recvHash \in Hash : CreateOpenBlock(creator, recvHash)
  \/ \E creator \in PrivateKey, recvHash \in Hash : CreateReceiveBlock(creator, recvHash)
  \/ \E creator \in PrivateKey : CreateChangeRepBlock(creator)
  \/ \E n \in Node, h \in Hash : ValidateSendBlock(n, h)
  \/ \E n \in Node, h \in Hash : ValidateOpenBlock(n, h)
  \/ \E n \in Node, h \in Hash : ValidateReceiveBlock(n, h)
  \/ \E n \in Node, h \in Hash : ValidateChangeRepBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Balance is derived by walking the chain backwards, counting net inflow.
Balance(ledger, n, h) ==
  IF h = NoHash THEN 0
  ELSE LET blk == ledger[n][h] IN
       IF blk.type = "genesis" THEN blk.amount
       ELSE IF blk.type = "send" THEN Balance(ledger, n, blk.link1) - blk.amount
       ELSE IF blk.type = "receive" THEN Balance(ledger, n, blk.link1) + ledger[n][blk.link2].amount
       ELSE Balance(ledger, n, blk.link1)

TotalBalance(ledger) ==
  LET balances == [n \in Node |-> Balance(ledger, n, lastHash)]
  IN balances[Node[CHOOSE k \in PrivateKey : TRUE]]
       + balances[Node[CHOOSE k \in PrivateKey : TRUE]]

TypeInvariant == TypeOK
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # EMPTY => ledger[n][h].signature = ledger[n][h].account

BalanceInequality == TotalBalance(ledger) <= GenesisBalance

====