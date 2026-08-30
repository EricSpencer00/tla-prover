---- MODULE Nano ----
EXTENDS Integers, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

Accounts == PublicKey

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

NoBlock == [prev |-> NoHashVal, recv |-> NoHashVal, kind |-> "none", amount |-> 0, signer |-> NoHashVal]

RECURSIVE SumAmount(_)
SumAmount(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN x.amount + SumAmount(S \ {x})

RECURSIVE WalkChain(_)
WalkChain(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE e \in S : e.kind = "send" IN x \cup WalkChain(S \ {x})

\* Money is conserved: the total balance across all accounts is exactly the
\* amount of every send block that has been claimed, and no more.
BalanceConserved ==
  SumAmount(WalkChain(ledger[NoHash])) = GenesisBalance

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> Accounts \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Hash |-> NoBlockVal]
  /\ received = [nd \in Node |-> {}]

CreateGenesisBlock ==
  \E k \in PrivateKey, nd \in Node :
    /\ lastHash = NoHashVal
    /\ lastHash' = CalculateHash([kind |-> "open", amount |-> GenesisBalance], NoHashVal)
    /\ LET b == [prev |-> NoHashVal, recv |-> NoHashVal, kind |-> "open",
                  amount |-> GenesisBalance, signer |-> k] IN
         ledger' = [n \in Hash |-> IF n = lastHash THEN b ELSE ledger[n]]
    /\ received' = [nd' \in Node |-> received[nd'] \cup {lastHash}]

CreateSendBlock ==
  \E nd \in Node, k \in PrivateKey, rc \in PublicKey, amt \in 1..GenesisBalance :
    /\ lastHash # NoHashVal
    /\ ledger[lastHash].signer \in PrivateKey
    /\ ledger' = [ledger EXCEPT ![CalculateHash([kind |-> "send", amount |-> amt], lastHash)] =
                    [prev |-> lastHash, recv |-> rc, kind |-> "send", amount |-> amt, signer |-> k]]
    /\ lastHash' = CalculateHash([kind |-> "send", amount |-> amt], lastHash)
    /\ received' = [nd' \in Node |-> received[nd'] \cup {CalculateHash([kind |-> "send", amount |-> amt], lastHash)}]

CreateOpenBlock ==
  \E nd \in Node, k \in PrivateKey, s \in Hash :
    /\ lastHash # NoHashVal
    /\ ledger[s] # NoBlockVal
    /\ ledger[s].kind = "send"
    /\ ledger[s].recv = Accounts[PublicKey][ledger[s].signer]
    /\ \A x \in WalkChain(ledger[NoHash]) : x.signer # k
    /\ ledger' = [ledger EXCEPT ![CalculateHash([kind |-> "open", amount |-> ledger[s].amount], lastHash)] =
                    [prev |-> lastHash, recv |-> NoHashVal, kind |-> "open",
                     amount |-> ledger[s].amount, signer |-> k]]
    /\ lastHash' = CalculateHash([kind |-> "open", amount |-> ledger[s].amount], lastHash)
    /\ received' = [nd' \in Node |-> received[nd'] \cup {CalculateHash([kind |-> "open", amount |-> ledger[s].amount], lastHash)}]

CreateReceiveBlock ==
  \E nd \in Node, k \in PrivateKey, s \in Hash :
    /\ lastHash # NoHashVal
    /\ ledger[s] # NoBlockVal
    /\ ledger[s].kind \in {"send", "open"}
    /\ ledger[s].recv = Accounts[PublicKey][ledger[s].signer]
    /\ \A x \in WalkChain(ledger[NoHash]) : x.signer # k
    /\ ledger' = [ledger EXCEPT ![CalculateHash([kind |-> "receive", amount |-> ledger[s].amount], lastHash)] =
                    [prev |-> lastHash, recv |-> s, kind |-> "receive",
                     amount |-> ledger[s].amount, signer |-> k]]
    /\ lastHash' = CalculateHash([kind |-> "receive", amount |-> ledger[s].amount], lastHash)
    /\ received' = [nd' \in Node |-> received[nd'] \cup {CalculateHash([kind |-> "receive", amount |-> ledger[s].amount], lastHash)}]

CreateChangeRepresentativeBlock ==
  \E nd \in Node, k \in PrivateKey :
    /\ lastHash # NoHashVal
    /\ ledger' = [ledger EXCEPT ![CalculateHash([kind |-> "change", amount |-> 0], lastHash)] =
                    [prev |-> lastHash, recv |-> NoHashVal, kind |-> "change",
                     amount |-> 0, signer |-> k]]
    /\ lastHash' = CalculateHash([kind |-> "change", amount |-> 0], lastHash)
    /\ received' = [nd' \in Node |-> received[nd'] \cup {CalculateHash([kind |-> "change", amount |-> 0], lastHash)}]

\* Validation requires only the node's own copy of the ledger, never the
\* whole network's, which is what makes the system a replicated ledger.
ProcessBlock ==
  \E nd \in Node, h \in Hash :
    /\ h \in received[nd]
    /\ ledger[h] # NoBlockVal
    /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
    /\ received' = [received EXCEPT ![nd] = received[nd] \ {h}]
    /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
  \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock \/ ProcessBlock

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  /\ TypeInvariant
  /\ \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].signer \in PrivateKey
====