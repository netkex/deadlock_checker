---- MODULE Testset ----

EXTENDS Integers


CONSTANTS 
    PROCESSES,
    STATES,
    FINAL_STATE

VARIABLES
  bolt,
  in_critical, 
  current_state,
  testset_result

vars == <<bolt, in_critical, current_state, testset_result>>

TypeOK ==
  /\ bolt \in 0..1
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ testset_result \in [PROCESSES -> BOOLEAN]

Init ==
  /\ bolt = 0
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ testset_result = [p \in PROCESSES |-> FALSE]

Exclusion == 
    \/ in_critical[0] = FALSE 
    \/ in_critical[1] = FALSE

End_program == 
    /\ current_state[0] = FINAL_STATE
    /\ current_state[1] = FINAL_STATE
    /\ UNCHANGED vars

Testset(p) ==
    \/ (
        /\ bolt = 0
        /\ bolt' = 1
        /\ testset_result' = [testset_result EXCEPT ![p] = TRUE]
        /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
        /\ UNCHANGED <<in_critical>>)
    \/ (
        /\ bolt = 1
        /\ testset_result' = [testset_result EXCEPT ![p] = FALSE]
        /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
        /\ UNCHANGED <<bolt, in_critical>>)

Wait_while(p) == 
    \/ (
        /\ ~testset_result[p]
        /\ current_state' = [current_state EXCEPT ![p] = @ - 1]
        /\ UNCHANGED <<bolt, in_critical, testset_result>>)
    \/ (
        /\ testset_result[p]
        /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
        /\ UNCHANGED <<bolt, in_critical, testset_result>>)

Enter_critical(p) ==
    /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
    /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<bolt, testset_result>>

Do_critical(p) == 
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
    /\ UNCHANGED <<bolt, in_critical, testset_result>>

Exit_critical(p) == 
    /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<bolt, testset_result>>

Drop_bolt(p) == 
    /\ bolt' = 0
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
    /\ UNCHANGED <<in_critical, testset_result>>

Run_process(p) == 
    \/ (current_state[p] = 0 /\ Testset(p))
    \/ (current_state[p] = 1 /\ Wait_while(p))
    \/ (current_state[p] = 2 /\ Enter_critical(p))
    \/ (current_state[p] = 3 /\ Do_critical(p))
    \/ (current_state[p] = 4 /\ Exit_critical(p))
    \/ (current_state[p] = 5 /\ Drop_bolt(p))


Next == 
    \/ \E p \in PROCESSES: Run_process(p)
    \/ End_program

Fairness ==
    \A p \in PROCESSES: WF_vars(Run_process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Ends == 
    <>[] \A s \in PROCESSES: current_state[s] = FINAL_STATE

--------------------------------------

PROCESSES_const == 0..5
STATES_const == 0..FINAL_STATE

====