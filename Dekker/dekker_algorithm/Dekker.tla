---- MODULE Dekker ----

(****************************************************)
(* State |  Mutual Exclusion Code                   *)
(*       | // mutual variables                      *)
(* init  | int turn = 0;                            *)
(* init  | bool interested[2] = {false, false};     *)
(********|*******************************************)
(*       | // enter critical section, p - process   *)
(* 0     | interested[p] = true;                    *)
(* 1     | while (interested[other])                *)
(* 2     |     if (turn == 1 - p) {                 *)
(* 3     |         interested[p] = false;           *)
(* 4     |         while (turn == 1 - p)            *)
(*       |             ; // Активное ожидание       *)
(* 5     |         interested[p] = true;            *)
(* 6     |     }                                    *)
(* 7     | start_critical();                        *)
(* 8     | action_in_critical();                    *)
(*       | // exit critical section                 *)
(* 9     | end_critical();                          *)
(* 10    | turn = 1 - p;                            *)
(* 11    | interested[p] = false;                   *)
(****************************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE, 
  ENTER_CRITICAL_SECTION_STATES,
  EXITING_CRITICAL_SECTION_STATES,
  CRITICAL_STATE,
  ENTER_WHILE_SECTION

VARIABLES
  turn,
  in_critical, 
  current_state,
  interested

vars == <<turn, in_critical, current_state, interested>>

TypeOK ==
  /\ turn \in 0..1
  /\ current_state \in [PROCESSES -> STATES]
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ interested \in [PROCESSES -> BOOLEAN]

Init ==
  /\ turn = 0
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ interested = [p \in PROCESSES |-> FALSE]

Exclusion == 
  \/ in_critical[0] = FALSE 
  \/ in_critical[1] = FALSE

End_program == 
  /\ current_state[0] = FINAL_STATE
  /\ current_state[1] = FINAL_STATE
  /\ UNCHANGED vars


Increment_state(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<turn, in_critical, interested>> 

Set_state(p, state) == 
  /\ current_state' = [current_state EXCEPT ![p] = state]
  /\ UNCHANGED <<turn, in_critical, interested>> 

Set_critical_increment_state(p, critical_value) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ in_critical' = [in_critical EXCEPT ![p] = critical_value]
  /\ UNCHANGED <<turn, interested>>

Set_turn_increment_state(p, turn_value) == 
  /\ turn' = turn_value
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<interested, in_critical>>

Set_intersted_increment_state(p, state_value) == 
  /\ interested' = [interested EXCEPT ![p] = state_value] 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<turn, in_critical>>

Enter_while_section(p) == 
  \/ (current_state[p] = 1 /\ (
    \/ (interested[1 - p] = FALSE /\ Set_state(p, 7))
    \/ (interested[1 - p] = TRUE  /\ Increment_state(p))))
  \/ (current_state[p] = 2 /\ (
    \/ (turn /= 1 - p /\ Set_state(p, 1))
    \/ (turn = 1 - p  /\ Increment_state(p)))) 
  \/ (current_state[p] = 3 /\ Set_intersted_increment_state(p, FALSE))
  \/ (current_state[p] = 4 /\ (
    \/ (turn = 1 - p /\ Set_state(p, 4))
    \/ (turn /= 1 - p /\ Increment_state(p))))
  \/ (current_state[p] = 5 /\ Set_intersted_increment_state(p, TRUE))
  \/ (current_state[p] = 6 /\ Set_state(p, 1))
  \/ (current_state[p] = 7 /\ Set_critical_increment_state(p, TRUE))

Enter_critical(p) ==
  \/ (current_state[p] = 0 /\ Set_intersted_increment_state(p, TRUE))
  \/ (current_state[p] \in ENTER_WHILE_SECTION /\ Enter_while_section(p))

Do_critical(p) == 
  /\ Increment_state(p)

Exit_critical(p) == 
  \/ (current_state[p] = 9 /\ Set_critical_increment_state(p, FALSE))
  \/ (current_state[p] = 10 /\ Set_turn_increment_state(p, 1 - p))
  \/ (current_state[p] = 11 /\ Set_intersted_increment_state(p, FALSE))

Run_process(p) == 
  \/ (current_state[p] \in ENTER_CRITICAL_SECTION_STATES /\ Enter_critical(p))
  \/ (current_state[p] = CRITICAL_STATE /\ Do_critical(p))
  \/ (current_state[p] \in EXITING_CRITICAL_SECTION_STATES /\ Exit_critical(p))


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
ENTER_CRITICAL_SECTION_STATES_const == 0..(CRITICAL_STATE - 1)
EXITING_CRITICAL_SECTION_STATES_const == CRITICAL_STATE..(FINAL_STATE - 1)
ENTER_WHILE_SECTION_const == 1..(CRITICAL_STATE - 1)
====