From Picalc Require Import Interface.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation u := "u".
Notation v := "v".

(* Shows that the semantics are non-deterministic

    The state
        x<y>,P | x(u),u<v>,Q | x<z>,R
    can step into two states (ignoring substitution for now):
        (1) P | y<v>,Q | x<y>,R
        (2) x<y>,P | z<v>,Q | R
    
    In (1), the leftmost thread sends the message "y" on the channel "x" to the 
    center thread. The center thread receives, binds its input to "u", and then 
    waits to send on channel "u". After receiving the message from the leftmost
    thread, the sent message "y" is substituted for all occurrences of "u".

    In (2), the same thing happens, but it is instead the rightmost thread that
    sends to the center thread.
*)

Example milner_2_2 : forall P Q R,
    (<{x<y>,P | x(u),u<v>,Q | x<z>,R}> ~>* <{P | y<v>,[u:=y]Q | x<z>,R}>) /\
    (<{x<y>,P | x(u),u<v>,Q | x<z>,R}> ~>* <{x<y>,P | z<v>,[u:=z]Q | R}>).
Proof.
    split.
    - send 0 <-> 1.
    - send 1 <-> 2.
Qed.
