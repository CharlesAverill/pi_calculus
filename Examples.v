From Picalc Require Import Interface.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation u := "u".
Notation v := "v".

(* Shows that the semantics are non-deterministic

    The state
        x<y>,# | x(u),u<v>,# | x<z>,#
    can step into two states:
        (1) # | y<v>,# | x<y>,#
        (2) x<y>,# | z<v>,# | #
    
    In (1), the leftmost thread sends the message "y" on the channel "x" to the 
    center thread. The center thread receives, binds its input to "u", and then 
    waits to send on channel "u". After receiving the message from the leftmost
    thread, the sent message "y" is substituted for all occurrences of "u".

    In (2), the same thing happens, but it is instead the rightmost thread that
    sends to the center thread.
*)

Example milner_2_2 :
    (<{x<y>,# | x(u),u<v>,# | x<z>,#}> ~>* <{# | y<v>,# | x<z>,#}>) /\
    (<{x<y>,# | x(u),u<v>,# | x<z>,#}> ~>* <{x<y>,# | z<v>,# | #}>).
Proof.
    split.
    - step.
        send 0 -> 1.
        rewrite <- Congr_Par_assoc; reflexivity. 
        reflexivity.
    - step.
        send 1 -> 2.
            rewrite <- Congr_Par_assoc. reflexivity.
        parswap. rotate right. reflexivity.
Qed.
