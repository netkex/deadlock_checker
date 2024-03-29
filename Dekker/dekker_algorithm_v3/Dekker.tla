---- MODULE Dekker ----

(*******************************************************************************)
(* State |                   Mutual Exclusion Code                             *)
(* init  |        bool interested[2] = {false, false};  // mutal               *)
(********|**********************************************************************)
(*       | Process 0                        | Process 1                        *)
(********|**********************************|***********************************)
(* 0     | interested[0] = true;            | interested[1] = true;            *)
(* 1     | while (interested[1])            | while (interested[0])            *)
(*       |     ; // Активное ожидание       |     ; // Активное ожидание       *)
(* 2     | start_critical();                | start_critical();                *)
(* 3     | action_in_critical();            | action_in_critical();            *)
(* 4     | end_critical();                  | end_critical();                  *)
(* 5     | interested[0] = false;           | interested[1] = false;           *)
(*******************************************************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE

VARIABLES
  in_critical, 
  current_state,
  interested

vars == <<in_critical, current_state, interested>>

TypeOK ==
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ interested \in [PROCESSES -> BOOLEAN]

Init ==
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ interested = [p \in PROCESSES |-> FALSE]

Exclusion == 
  ~ \E p1, p2 \in PROCESSES:
    /\ p1 /= p2
    /\ in_critical[p1]
    /\ in_critical[p2] 

End_program == 
  /\ current_state[0] = FINAL_STATE
  /\ current_state[1] = FINAL_STATE
  /\ UNCHANGED vars


Wait_while(p) == 
  \/ (
    /\ interested[1 - p]
    /\ UNCHANGED vars)
  \/ (
    /\ ~interested[1 - p]
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<in_critical, interested>>)

Enter_critical(p) ==
  /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
  /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<interested>>

Do_critical(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<in_critical, interested>>

Exit_critical(p) == 
  /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<interested>>

Set_interested(p, value) == 
  /\ interested' = [interested EXCEPT ![p] = value] 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<in_critical>>

Run_process(p) == 
  \/ (current_state[p] = 0 /\ Set_interested(p, TRUE))
  \/ (current_state[p] = 1 /\ Wait_while(p))
  \/ (current_state[p] = 2 /\ Enter_critical(p))
  \/ (current_state[p] = 3 /\ Do_critical(p))
  \/ (current_state[p] = 4 /\ Exit_critical(p))
  \/ (current_state[p] = 5 /\ Set_interested(p, FALSE))


Next == 
  \/ \E p \in PROCESSES: Run_process(p)
  \/ End_program

Fairness ==
  \A p \in PROCESSES: WF_vars(Run_process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Ends == 
  <>[] \A s \in PROCESSES: current_state[s] = FINAL_STATE

--------------------------------------

PROCESSES_const == 0..1
STATES_const == 0..FINAL_STATE

====