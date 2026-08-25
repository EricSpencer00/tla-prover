---- MODULE MCEcho ----
EXTENDS Echo

(* Concrete instantiation of the abstract constants *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Test variant that prints the adjacency relation at startup *)
TestSpec == Init /\ (Print(R, "R") = R) /\ [][Next]_vars

====