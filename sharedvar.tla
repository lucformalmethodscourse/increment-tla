---- MODULE sharedvar ----
EXTENDS Integers

CONSTANTS N
ASSUME N > 0

(*--algorithm sv

variables
    shared = 0

define
    AllIncrements == shared = N
    EventuallyConsistent == <>[](AllIncrements)
end define;

fair process IncOnce \in 1..N
    variables
        local = -1;
begin
    FetchAndStore:
        local := shared;
        shared := local + 1;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "57dcd94" /\ chksum(tla) = "abea92ce")
VARIABLES shared, pc

(* define statement *)
AllIncrements == shared = N
EventuallyConsistent == <>[](AllIncrements)

VARIABLE local

vars == << shared, pc, local >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ shared = 0
        (* Process IncOnce *)
        /\ local = [self \in 1..N |-> -1]
        /\ pc = [self \in ProcSet |-> "FetchAndStore"]

FetchAndStore(self) == /\ pc[self] = "FetchAndStore"
                       /\ local' = [local EXCEPT ![self] = shared]
                       /\ shared' = local'[self] + 1
                       /\ pc' = [pc EXCEPT ![self] = "Done"]

IncOnce(self) == FetchAndStore(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: IncOnce(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(IncOnce(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
