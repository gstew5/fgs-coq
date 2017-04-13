Require Import Arith Omega List.

Module Type VAL.
  (** The uninterpreted type of values communicated on wires. 
      In a concrete implementation, [t] might equal [bit] or [bool]. *)
  Parameter t : Type.

  (** R1: The type [t] is inhabited. *)
  Parameter init_t : t.
End VAL.  

Module Type DELAY.
  Parameter n : nat.
  Parameter gt0 : 0 < n.
End DELAY.  

Lemma lt_S {n i} : S i < n -> i < n.
Proof. omega. Qed.
  
Module Type DELAY_N_BUS (V : VAL) (D : DELAY).
  Notation val := V.t.
  Notation delay := D.n.
  
  (** The uninterpreted type of bus internal state *)
  Parameter state : Type.
  
  (** The uninterpreted execution semantics of the bus *)
  Parameter step : val -> state -> state.
  Parameter value : forall i : nat, i < delay -> state -> val.  
  
  (** High-level requirements: *)

  (* R1: There exists an initial state. *)
  Axiom init_state : state.

  (* R2: *)
  Axiom step_values :
    forall (v_in : val)
           (s_in : state),
      let s_out := step v_in s_in in 
      value 0 D.gt0 s_out = v_in
      /\ forall i (pf : S i < delay) (v_i : val), 
          value i (lt_S pf) s_in = v_i ->
          value (S i) pf s_out = v_i.
End DELAY_N_BUS.

Module DelayNBus (V : VAL) (D : DELAY).
  Notation val := V.t.
  Notation delay := D.n.

  Definition state := {l : list val | length l = delay}.
  Definition list_of_state (s : state) : list val :=
    match s with
    | exist _ l _ => l
    end.
  
  Lemma cons_length {A} x (l : list A) : length (x :: l) = S (length l).
  Proof. reflexivity. Qed.
  
  Lemma removelast_length {A} n (l : list A) :
    length l = S n -> length (removelast l) = n.
  Proof.
    revert n; induction l; inversion 1; subst; destruct l; auto.
    assert (removelast (a::a0::l) = a::removelast (a0::l)) as -> by auto.
    assert (length (a::removelast (a0::l)) = S (length (removelast (a0::l)))) as -> by auto.
    assert (length (a0::l) = S (length l)) as -> by auto.
    rewrite (IHl (length l)); auto.    
  Qed.    

  Lemma nth_removelast {A i l} {v : A} :
    i < length (removelast l) ->
    nth i (removelast l) v = nth i l v.
  Proof.
    revert i; induction l; auto.
    intros i H; destruct l. { simpl in H; omega. }
    assert (H2: removelast (a::a0::l) = a::removelast (a0::l)) by auto.
    rewrite H2 in H|-*; destruct i; auto.
    assert (nth (S i) (a :: removelast (a0 :: l)) v =
            nth i (removelast (a0 :: l)) v) as -> by auto.
    assert (nth (S i) (a :: a0 :: l) v = nth i (a0 :: l) v) as -> by auto.
    rewrite IHl; auto.
    clear - H; revert H; generalize (removelast (a0::l)); simpl; intros; omega.
  Qed.    
  
  Program Definition step (v_in : val) (s_in : state) : state :=
    exist _ _ (removelast_length _ _ (cons_length v_in (list_of_state s_in))).
  Next Obligation. destruct s_in as [l e]; auto. Qed.

  Definition value i (pf : i < delay) (s : state) : val :=
    List.nth i (list_of_state s) V.init_t.
  
  Lemma step_values : 
    forall (v_in : val)
           (s_in : state),
      let s_out := step v_in s_in in 
      value 0 D.gt0 s_out = v_in
      /\ forall i (pf : S i < delay) (v_i : val), 
          value i (lt_S pf) s_in = v_i ->
          value (S i) pf s_out = v_i.
  Proof.
    intros v_in s_in; simpl; split.
    { unfold value; destruct (step v_in s_in) as [l e] eqn:H; destruct l.
      { generalize D.gt0; intros H2; simpl in e. 
        elimtype False; clear - e H2; rewrite <-e in H2; omega. }
      unfold step in H; inversion H; simpl; clear H.
      destruct (list_of_state s_in); inversion H1; subst; auto. }
    intros i pf v_i.
    unfold value; destruct (step v_in s_in) as [l e] eqn:H.
    assert (S i < length l) by (rewrite e; auto).
    simpl; unfold step in H; inversion H; clear e H pf.
    destruct (list_of_state s_in); inversion H2; subst.
    { simpl in H0; omega. }
    clear H; intros <-.
    assert (H1: i < length (removelast (t::l0))).
    { revert H0; generalize (removelast (t::l0)); simpl.
      intros l H; omega. }
    assert (nth (S i) (v_in :: removelast (t :: l0)) V.init_t =
            nth i (removelast (t :: l0)) V.init_t) as -> by auto.
    rewrite nth_removelast; auto.
  Qed.    
End DelayNBus.

Module Type DELAY_1_BUS (V : VAL).
  Notation val := V.t.
  
  (** The uninterpreted type of bus internal state *)
  Parameter state : Type.
  
  (** The uninterpreted execution semantics of the bus *)
  Parameter step : val -> state -> state.
  Parameter output : state -> val.
  
  (** High-level requirements: *)

  (* R1: There exists an initial state. *)
  Axiom init_state : state.

  (* R2: *)
  Axiom step_output :
    forall (v_in : val) (s_in : state),
      let s_out := step v_in s_in in
      output s_out = v_in.
End DELAY_1_BUS.

Module Delay1Bus_of_DelayNBus (V : VAL) : DELAY_1_BUS V.
  Notation val := V.t.
                                            
  Module Delay1 : DELAY.                                            
    Definition n := 1.
    Lemma gt0 : 0 < n. Proof. unfold n; omega. Qed.
  End Delay1.

  Declare Module Delay1Bus : DELAY_N_BUS V Delay1.

  Definition state := Delay1Bus.state.
  Definition step := Delay1Bus.step.
  Definition init_state := Delay1Bus.init_state.

  Definition output (s : state) : val :=
    Delay1Bus.value 0 Delay1.gt0 s.

  Lemma step_output :
    forall (v_in : val) (s_in : state),
      let s_out := step v_in s_in in
      output s_out = v_in.
  Proof.
    intros v_in s_in; simpl.
    destruct (Delay1Bus.step_values v_in s_in) as [H1 _]; auto.
  Qed.
End Delay1Bus_of_DelayNBus.