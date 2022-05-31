---- MODULE Dekker ----

EXTENDS Integers


CONSTANTS 
    PROCESSES,
    STATES,
    FINAL_STATE

VARIABLES
  wants_to_enter, 
  turn,
  in_critical, 
  current_state

vars == <<wants_to_enter, turn, in_critical, current_state>>

TypeOK ==
  /\ wants_to_enter \in [PROCESSES -> BOOLEAN]
  /\ turn \in 0..1
  /\ in_critical \in [PROCESSES -> BOOLEAN ]
  /\ current_state \in STATES

Init ==
  /\ turn = 0
  /\ wants_to_enter = [p \in PROCESSES |-> FALSE]
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
        /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
        /\ UNCHANGED <<turn, wants_to_enter, in_critical>>)

Enter_critical(p) ==
    /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
    /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<turn, wants_to_enter>>

Set_turn(p, value) == 
    /\ turn' = value
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
    /\ UNCHANGED <<in_critical, wants_to_enter>>

Exit_critical(p) == 
    /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<turn, wants_to_enter>>


Run_process_0 == 
    \/ (current_state[0] = 0 /\ Wait_while(0))
    \/ (current_state[0] = 1 /\ Enter_critical(0))
    \/ (current_state[0] = 2 /\ Set_turn(0, 1))
    \/ (current_state[0] = 3 /\ Exit_critical(0))

Run_process_1 == 
    \/ (current_state[1] = 0 /\ Wait_while(1))
    \/ (current_state[1] = 1 /\ Enter_critical(1))
    \/ (current_state[1] = 2 /\ Set_turn(1, 0))
    \/ (current_state[1] = 3 /\ Exit_critical(1))

Next == 
    \/ Run_process_0 
    \/ Run_process_1 
    \/ End_program

Spec == Init /\ [][Next]_vars

--------------------------------------

PROCESSES_const == 0..1
STATES_const == 0..FINAL_STATE

====