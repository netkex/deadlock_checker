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

Run_process(p) == 
    /\ current_state[p] /= FINAL_STATE
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<turn, wants_to_enter, in_critical>>

Next == 
    \/ Run_process(0) 
    \/ Run_process(1) 
    \/ End_program

Spec == Init /\ [][Next]_vars

--------------------------------------

PROCESSES_const == 0..1
STATES_const == 0..FINAL_STATE

====