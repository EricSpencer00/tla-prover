------------------------- MODULE Nano -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey,
  Node, GenesisBalance, NoBlockVal, NoHash, CalculateHash, NoBlock

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

EmptyNodeLedger == [n \in Hash |-> NoBlockVal]

RECURSIVE ChainBalance(_)
ChainBalance(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE
       IN IF ledger[h] = NoBlockVal
            THEN ChainBalance(S \ {h})
            ELSE LET b == ledger[h] IN b.amount + ChainBalance(S \ {h})

RECURSIVE ChainSent(_)
ChainSent(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE
       IN IF ledger[h] = NoBlockVal
            THEN ChainSent(S \ {h})
            ELSE LET b == ledger[h]
                 IN IF b.type = "send" THEN b.amount + ChainSent(S \ {h}) ELSE ChainSent(S \ {h})

RECURSIVE ChainReceived(_)
ChainReceived(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE
       IN IF ledger[h] = NoBlockVal
            THEN ChainReceived(S \ {h})
            ELSE LET b == ledger[h]
                 IN IF b.type \in {"open", "receive", "change"} THEN b.amount + ChainReceived(S \ {h})
                    ELSE ChainReceived(S \ {h})

PublicOf(k) == CHOOSE p \in PublicKey : PublicOfKey[p] = k

PublicOfKey == [p \in PublicKey |-> p]
AccountOf(h) == IF ledger[h] = NoBlockVal THEN NoHash ELSE ledger[h].account

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Hash -> [account: Hash \cup {NoHash}, type: {"send", "open", "receive", "change"},
                         amount: 0..GenesisBalance, prev: Hash \cup {NoHash}, rep: PublicKey \cup {NoHash}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = EmptyNodeLedger
  /\ received = [n \in Node |-> {}]

Validate(n, h) ==
  /\ ledger[h] = NoBlockVal
  /\ h \in received[n]
  /\ (IF lastHash = NoHash THEN TRUE ELSE CalculateHash(h, lastHash) = h)
  /\ LET b == {n \in Hash : ledger[n] # NoBlockVal /\ ledger[n].account = h} \ {NoHash}
     IN IF b = {} THEN TRUE ELSE \A x \in b : ledger[x].prev = NoHash
  /\ CASE ledger[h].type = "send" ->
        /\ ChainBalance(AccountOf(h)) >= ledger[h].amount
        /\ AccountOf(h) \notin b
     [] ledger[h].type = "open" ->
        /\ ChainSent(AccountOf(h)) = 0
        /\ ChainBalance(AccountOf(h)) = 0
        /\ PublicOf(ledger[h].rep) = ledger[h].account
     [] ledger[h].type = "receive" ->
        /\ ChainReceived(AccountOf(h)) = 0
        /\ ChainBalance(AccountOf(h)) = 0
        /\ ledger[ledger[h].prev] # NoBlockVal
        /\ ledger[ledger[h].prev].type = "send"
        /\ ledger[ledger[h].prev].account = ledger[h].account
        /\ ledger[ledger[h].prev].amount = ledger[h].amount
        /\ PublicOf(ledger[h].rep) = ledger[h].account
     [] ledger[h].type = "change" ->
        /\ ChainReceived(AccountOf(h)) = 0
        /\ ChainBalance(AccountOf(h)) >= ledger[h].amount
        /\ PublicOf(ledger[h].rep) = ledger[h].account
  /\ ledger' = [ledger EXCEPT ![h] =
        [account |-> AccountOf(h), type |-> "send", amount |-> GenesisBalance,
         prev |-> NoHash, rep |-> NoHash]]

Broadcast(h) == [n \in Node |-> received[n] \cup {h}]

CreateGenesis(n) ==
  /\ lastHash = NoHash
  /\ lastHash' = NoHash
  /\ ledger' = [ledger EXCEPT ![NoHash] =
        [account |-> NoHash, type |-> "open", amount |-> GenesisBalance,
         prev |-> NoHash, rep |-> PublicOf(NodeKey[n])]]
  /\ received' = Broadcast(NoHash)

CreateSend(n) ==
  /\ lastHash # NoHash
  /\ \E r \in Node, amt \in 1..GenesisBalance :
       /\ ChainBalance(AccountOf(lastHash)) >= amt
       /\ \E h \in Hash :
            /\ ledger' = [ledger EXCEPT
                          ![h] = [account |-> AccountOf(lastHash), type |-> "send", amount |-> amt,
                                   prev |-> lastHash, rep |-> PublicOf(NodeKey[n])]]
            /\ lastHash' = h
            /\ received' = Broadcast(h)

CreateOpen(n) ==
  /\ lastHash # NoHash
  /\ \E s \in Node, h \in Hash :
       /\ ledger[h] # NoBlockVal
       /\ ledger[h].account = NoHash
       /\ ledger[h].type = "send"
       /\ ledger[h].account = PublicOf(NodeKey[n])
       /\ \E nh \in Hash :
            /\ ledger' = [ledger EXCEPT
                          ![nh] = [account |-> PublicOf(NodeKey[n]), type |-> "open", amount |-> 0,
                                   prev |-> h, rep |-> PublicOf(NodeKey[n])]]
            /\ lastHash' = nh
            /\ received' = Broadcast(nh)

CreateReceive(n) ==
  /\ lastHash # NoHash
  /\ \E h \in Hash :
       /\ ledger[h] # NoBlockVal
       /\ ledger[h].account \in PublicKey
       /\ ledger[h].type = "send"
       /\ \E nh \in Hash :
            /\ ledger' = [ledger EXCEPT
                          ![nh] = [account |-> ledger[h].account, type |-> "receive", amount |-> ledger[h].amount,
                                   prev |-> lastHash, rep |-> ledger[h].rep]]
            /\ lastHash' = nh
            /\ received' = Broadcast(nh)

CreateChange(n) ==
  /\ lastHash # NoHash
  /\ \E amt \in 1..GenesisBalance, nh \in Hash :
       /\ ChainBalance(AccountOf(lastHash)) >= amt
       /\ ledger' = [ledger EXCEPT
                     ![nh] = [account |-> AccountOf(lastHash), type |-> "change", amount |-> amt,
                              prev |-> lastHash, rep |-> PublicOf(NodeKey[n])]]
       /\ lastHash' = nh
       /\ received' = Broadcast(nh)

Next ==
  \/ \E n \in Node : CreateGenesis(n) \/ CreateOpen(n) \/ CreateReceive(n) \/ CreateChange(n)
  \/ \E n \in Node : CreateSend(n)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  \A h \in Hash :
    (ledger[h] # NoBlockVal) => (PublicOfKey[ledger[h].rep] = AccountOf(h))
===============================================================