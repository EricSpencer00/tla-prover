---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

VARIABLES lastHash, ledger, recv

vars == <<lastHash, ledger, recv>>

\* An account's chain is the set of blocks that sit anywhere on it; the recursive
\* balance walk walks the blocks reachable from the freshest one backwards.
\* Because block hashes are unique, the "next" relation below is a function.
OnChain(h) == {b \in Hash : (b = h \/ OnChain(ledger[h].prev))}
Tallies(o) == LET Recs(o) == {b \in Hash : ledger[b].type = "receive" /\ ledger[b].dst = o}
                 Balances(o) ==
                    IF Recs(o) = {}
                    THEN 0
                    ELSE LET b == CHOOSE x \in Recs(o) : TRUE
                         IN ledger[b].amount + Tallies(o)
                 IN Balances(o)
NoRecv(n) == {b \in Hash : ledger[b].type \in {"send", "open", "receive"} /\ ledger[b].dst \in {n}}
Recv(n) == {b \in Hash : ledger[b].type \in {"send", "open", "receive"} /\ ledger[b].dst = n}

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Hash -> [type : {"genesis", "send", "open", "receive", "change"},
                          prev : Hash \cup {NoHash}, owner : PublicKey,
                          dst : Node, amount : Nat, sig : PrivateKey]]
  /\ recv \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> [type |-> "genesis", prev |-> NoHash, owner |-> NoBlock,
                               dst |-> NoBlock, amount |-> 0, sig |-> NoBlock]]
  /\ recv = [n \in Node |-> {}]

CreateGenesisBlock(p) ==
  /\ lastHash = NoHash
  /\ \E h \in Hash :
       /\ ledger[h].type = "genesis"
       /\ ledger' = [ledger EXCEPT ![h] =
                        [type |-> "genesis", prev |-> NoHash, owner |-> PublicKey[p],
                         dst |-> NoBlock, amount |-> GenesisBalance, sig |-> p]]
       /\ lastHash' = h
       /\ recv' = [n \in Node |-> {h}]
  /\ UNCHANGED <<>>

CreateSendBlock(n, p) ==
  /\ ledger' = [h \in Hash |->
       IF \E q \in Hash :
            /\ ledger[q].type = "genesis"
            /\ ledger[q].owner = PublicKey[p]
            /\ ledger[q].amount >= 1
            /\ ledger[h].type = "send"
            /\ ledger[h].prev = q
            /\ ledger[h].owner = PublicKey[p]
            /\ ledger[h].dst = n
            /\ ledger[h].amount = 1
            /\ ledger[h].sig = p
          THEN TRUE
          ELSE FALSE
       THEN ledger[h] ELSE [type |-> "genesis", prev |-> NoHash, owner |-> NoBlock,
                                 dst |-> NoBlock, amount |-> 0, sig |-> NoBlock]]
  /\ recv' = [m \in Node |-> IF \E q \in Hash :
                                /\ ledger[q].type = "send" /\ ledger[q].dst = n /\ ledger[q].sig = p
                                THEN {q} ELSE {}]
  /\ UNCHANGED lastHash

CreateOpenBlock(n, p) ==
  /\ \E h \in Hash :
       /\ ledger[h].type = "send" /\ ledger[h].dst = n /\ ledger[h].sig = p
       /\ ledger' = [ledger EXCEPT ![h] =
                        [type |-> "open", prev |-> NoHash, owner |-> PublicKey[p],
                         dst |-> n, amount |-> 0, sig |-> p]]
       /\ recv' = [m \in Node |-> IF m = n THEN {h} ELSE {}]
  /\ UNCHANGED lastHash

CreateReceiveBlock(n, p) ==
  /\ \E h \in Hash :
       /\ ledger[h].type = "send" /\ ledger[h].dst = n /\ ledger[h].sig = p
       /\ \E g \in Hash :
            /\ ledger[g].type \in {"open", "receive"} /\ ledger[g].dst = n
            /\ ledger[h].prev = g
            /\ ledger' = [ledger EXCEPT ![h] =
                            [type |-> "receive", prev |-> g, owner |-> PublicKey[p],
                             dst |-> n, amount |-> 1, sig |-> p]]
            /\ recv' = [m \in Node |-> IF m = n THEN {h} ELSE {}]
  /\ UNCHANGED lastHash

CreateChangeReprBlock(n, p) ==
  /\ \E g \in Hash :
       /\ ledger[g].type \in {"open", "receive"}
       /\ ledger[g].dst = n /\ ledger[g].owner = PublicKey[p]
       /\ \E h \in Hash :
            /\ ledger[h].type = "change" /\ ledger[h].prev = g
               /\ ledger[h].owner = PublicKey[p] /\ ledger[h].sig = p
            /\ ledger' = [ledger EXCEPT ![h] =
                            [type |-> "change", prev |-> g, owner |-> PublicKey[p],
                             dst |-> NoBlock, amount |-> 0, sig |-> p]]
            /\ recv' = [m \in Node |-> IF m = n THEN {h} ELSE {}]
            /\ UNCHANGED lastHash

ValidateBlock(n, h) ==
  /\ h \in recv[n]
  /\ ledger[h].type # "genesis"
  /\ ledger[h].sig \in PrivateKey
  /\ ledger[h].owner = PublicKey[ledger[h].sig]
  /\ \A g \in recv[n] : g < h
  /\ recv' = [recv EXCEPT ![n] = recv[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E p \in PrivateKey : CreateGenesisBlock(p)
  \/ \E n \in Node, p \in PrivateKey :
       \/ CreateSendBlock(n, p) \/ CreateOpenBlock(n, p) \/ CreateReceiveBlock(n, p) \/ CreateChangeReprBlock(n, p)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every recorded block must survive a signature check against its owning key.
SafetyInvariant ==
  \A h \in Hash :
    ledger[h].type # "genesis" => ledger[h].owner = PublicKey[ledger[h].sig]

====