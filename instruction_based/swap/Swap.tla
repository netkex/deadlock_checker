---- MODULE Swap ----

EXTENDS Integers


CONSTANTS 
    PROCESSES,
    STATES,
    FINAL_STATE

VARIABLES
  bolt,
  in_critical, 
  current_state,
  key

vars == <<bolt, in_critical, current_state, key>>

TypeOK ==
  /\ bolt \in 0..1
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ key \in [PROCESSES -> 0..1]

Init ==
  /\ bolt = 0
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ key = [p \in PROCESSES |-> 1]

Exclusion == 
    \/ in_critical[0] = FALSE 
    \/ in_critical[1] = FALSE

End_program == 
    /\ current_state[0] = FINAL_STATE
    /\ current_state[1] = FINAL_STATE
    /\ UNCHANGED vars


Increment_state(p) == 
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<bolt, in_critical, key>> 

Set_state(p, state) == 
    /\ current_state' = [current_state EXCEPT ![p] = state]
    /\ UNCHANGED <<bolt, in_critical, key>>

Set_critical_increment_state(p, critical_value) == 
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ in_critical' = [in_critical EXCEPT ![p] = critical_value]
    /\ UNCHANGED <<bolt, key>>


Swap_and_set_state(p, new_state) == 
    /\ bolt' = key[p]
    /\ key' = [key EXCEPT ![p] = bolt]
    /\ current_state' = [current_state EXCEPT ![p] = new_state]
    /\ UNCHANGED <<in_critical>>

Enter_critical(p) ==
    /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
    /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<bolt, key>>

Do_critical(p) == 
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
    /\ UNCHANGED <<bolt, in_critical, key>>

Exit_critical(p) == 
    /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<bolt, key>>


Run_process(p) == 
    \/ (current_state[p] = 0 /\ (
        \/ (key[p] /= 0 /\ Increment_state(p))
        \/ (key[p] = 0  /\ Set_state(p, 2))))
    \/ (current_state[p] = 1 /\ Swap_and_set_state(p, 0))
    \/ (current_state[p] = 2 /\ Enter_critical(p))
    \/ (current_state[p] = 3 /\ Do_critical(p))
    \/ (current_state[p] = 4 /\ Exit_critical(p))
    \/ (current_state[p] = 5 /\ Swap_and_set_state(p, FINAL_STATE))


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