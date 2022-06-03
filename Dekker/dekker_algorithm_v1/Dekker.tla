---- MODULE Dekker ----

(*******************************************************************************)
(* State |                   Mutual Exclusion Code                             *)
(* init  |                   int turn = 0;  // mutal                           *)
(********|**********************************************************************)
(*       | Process 0                        | Process 1                        *)
(********|**********************************|***********************************)
(* 0     | while (turn != 0)                | while (turn != 1)                *)
(*       |     ; // Активное ожидание       |     ; // Активное ожидание       *)
(* 1     | start_critical();                | start_critical();                *)
(* 2     | action_in_critical();            | action_in_critical();            *)
(* 3     | end_critical();                  | end_critical();                  *)
(* 4     | turn = 1;                        | trun = 0;                        *)
(*******************************************************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE

VARIABLES
  turn,
  in_critical, 
  current_state

vars == <<turn, in_critical, current_state>>

TypeOK ==
  /\ turn \in 0..1
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]

Init ==
  /\ turn = 0
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]

Exclusion == 
  \/ in_critical[0] = FALSE 
  \/ in_critical[1] = FALSE

End_program == 
  /\ current_state[0] = FINAL_STATE
  /\ current_state[1] = FINAL_STATE
  /\ UNCHANGED vars


Wait_while(p) == 
  \/ (
    /\ turn /= p
    /\ UNCHANGED vars)
  \/ (
    /\ turn = p
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<turn, in_critical>>)

Enter_critical(p) ==
  /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
  /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<turn>>

Do_critical(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<turn, in_critical>>

Exit_critical(p) == 
  /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<turn>>

Set_turn(p, value) == 
  /\ turn' = value
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<in_critical>>

Run_process(p) == 
  \/ (current_state[p] = 0 /\ Wait_while(p))
  \/ (current_state[p] = 1 /\ Enter_critical(p))
  \/ (current_state[p] = 2 /\ Do_critical(p))
  \/ (current_state[p] = 3 /\ Exit_critical(p))
  \/ (current_state[p] = 4 /\ Set_turn(p, 1 - p))


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