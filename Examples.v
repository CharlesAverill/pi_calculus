From Picalc Require Import Interface.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation u := "u".
Notation v := "v".
Notation w := "w".

(* Shows that the semantics are non-deterministic

    The state
        x<y>,# | x(u),u<v>,# | x<y>,#
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
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{# | y<v>,# | x<y>,#}>) /\
    (<{x<y>,# | x(u),u<v>,# | x<y>,#}> ~>* <{x<y>,# | z<v>,# | #}>).
Proof.
    split.
    - step.
        apply SPar, SInput.
        psimpl. mstep_rename.
    - step.
        rotate left. parswap.
        apply SPar, SInput.
        psimpl. rotate left. parswap. mstep_rename.
Qed.
