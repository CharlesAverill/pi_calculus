From Picalc Require Export Step.

(* Rotate P|Q|R to Q|R|P *)
Tactic Notation "rotate" "left" :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_rotate_l
    | [|- _ ~> _] => apply Step_Par_rotate_l
    | [|- _ ~>* _] => apply multistep_Par_rotate_l
    end.

(* Rotate P|Q|R to R|P|Q *)
Tactic Notation "rotate" "right" :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_rotate_r
    | [|- _ ~> _] => apply Step_Par_rotate_r
    | [|- _ ~>* _] => apply multistep_Par_rotate_r
    end.

(* Swap P|Q|R to Q|P|R*)
Ltac parswap :=
    match goal with
    | [|- _ =c= _] => apply Congr_Par_swap
    | [|- _ ~> _] => apply Step_Par_swap
    | [|- _ ~>* _] => apply multistep_Par_swap
    end.

Ltac psimpl := cbn [subst String.eqb Ascii.eqb Bool.eqb].
Ltac pauto := psimpl; eauto with picalc.

Ltac step :=
    match goal with
    | [|- ?X ~>* ?Y] => eapply MStep
    end.

(* Backtrack over all IO processes *)
Ltac get_in_out_procs p name :=
    multimatch p with
    | <{_<_>,_}> => remember p as name
    | <{_(_),_}> => remember p as name
    | <{?P|?Q}> => get_in_out_procs P name + get_in_out_procs Q name
    end.

Ltac normalize_par :=
    repeat match goal with
    | [|- context[<{?A|?B|?C}>]] =>
        rewrite Congr_Par_assoc
    end.

(* Solve alpha equivalence congruence goals *)
Ltac mstep_rename_congr xname yname :=
    multimatch goal with
    | [ H0: xname = ?x, H1: yname = ?y |- _ ] =>
        match x with
        | Output ?u1 ?v1 _ => match y with
            | Output ?u2 ?v2 _ =>
                rewrite H0, H1;
                match goal with
                | [|- ?X0 =c= ?Y0] =>
                    change Y0 with <{[u1:=u2](X0)}>
                end;
                now apply Congr_Alpha_Equiv
            end
        end
    end.

(* Solve alpha equivalence multistep goals *)
Ltac mstep_rename :=
    multimatch goal with
    | [|- <{?X}> ~>* <{?Y}>] =>
        normalize_par;
        let xname := fresh "term" in
        let yname := fresh "term" in
        get_in_out_procs X xname;
        get_in_out_procs Y yname;
        eapply MCongr;
        mstep_rename_congr xname yname
    end.
