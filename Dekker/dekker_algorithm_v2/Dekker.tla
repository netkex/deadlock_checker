---- MODULE Dekker ----

(*******************************************************************************)
(* State |                   Mutual Exclusion Code                             *)
(* init  |           bool inside[2] = {false, false};  // mutal                *)
(********|**********************************************************************)
(*       | Process 0                        | Process 1                        *)
(********|**********************************|***********************************)
(* 0     | while (inside[1])                | while (inside[0])                *)
(*       |     ; // Активное ожидание       |     ; // Активное ожидание       *)
(* 1     | inside[0] = true;                | inside[1] = true;                *)
(* 2     | start_critical();                | start_critical();                *)
(* 3     | action_in_critical();            | action_in_critical();            *)
(* 4     | end_critical();                  | end_critical();                  *)
(* 5     | inside[0] = false;               | inside[1] = false;               *)
(*******************************************************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE

VARIABLES
  in_critical, 
  current_state,
  inside

vars == <<in_critical, current_state, inside>>

TypeOK ==
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ inside \in [PROCESSES -> BOOLEAN]

Init ==
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ inside = [p \in PROCESSES |-> FALSE]

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
    /\ inside[1 - p]
    /\ UNCHANGED vars)
  \/ (
    /\ ~inside[1 - p]
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<in_critical, inside>>)

Enter_critical(p) ==
  /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
  /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<inside>>

Do_critical(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<in_critical, inside>>

Exit_critical(p) == 
  /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<inside>>

Set_inside(p, value) == 
  /\ inside' = [inside EXCEPT ![p] = value] 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<in_critical>>

Run_process(p) == 
  \/ (current_state[p] = 0 /\ Wait_while(p))
  \/ (current_state[p] = 1 /\ Set_inside(p, TRUE))
  \/ (current_state[p] = 2 /\ Enter_critical(p))
  \/ (current_state[p] = 3 /\ Do_critical(p))
  \/ (current_state[p] = 4 /\ Exit_critical(p))
  \/ (current_state[p] = 5 /\ Set_inside(p, FALSE))


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