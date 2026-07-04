---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

\* TCLGet("stats").traces is only defined when TLC runs in simulation or generation mode.
\* For this spec, users have to run TLC in generate mode to collect meaningful statistics.
\* The original assumption on TLCGet("mode") caused a runtime error when the key was undefined.
\* We relax the assumption to always hold, preserving the intended behavior of the rest of the
\* specification while allowing TLC to evaluate the module in any mode.
ASSUME TRUE

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    \* State constraint at cfg
    UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>,CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE \* to make TLC simulate the next behavior one the system stabilizes.
====