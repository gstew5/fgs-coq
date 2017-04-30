Require Import Arith Omega List.

(** The *)

Definition is_true : bool -> Prop := fun b => b = true.
Coercion is_true : bool >-> Sortclass.

Module Type VAL.
  (** The uninterpreted type of values communicated on wires. 
      In a concrete implementation, [t] might equal [bit] or [bool]. *)
  Parameter t : Type.
  Parameter init : t.

  (** We can coerce bus values to type [bool]. *)
  Parameter is_true : t -> bool.

  (** There are two bus-value constructors... *)
  Parameter high : t.
  Parameter low : t.

  (** ...satisfying the following properties: *)
  Parameter high_is_true : is_true high = true.
  Parameter low_is_false : is_true low = false.
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
  Axiom value_init_state :
    forall i (pf : i < delay), value i pf init_state = V.init.

  (* R3: *)
  Axiom step_values :
    forall (v_in : val)
           (s_in : state),
      let s_out := step v_in s_in in 
      value 0 D.gt0 s_out = v_in
      /\ forall i (pf : S i < delay) (v_i : val), 
          value i (lt_S pf) s_in = v_i ->
          value (S i) pf s_out = v_i.
End DELAY_N_BUS.

Module DelayNBus (V : VAL) (D : DELAY) : DELAY_N_BUS V D.
  Notation val := V.t.
  Notation delay := D.n.

  Definition state := {l : list val | length l = delay}.
  Definition list_of_state (s : state) : list val :=
    match s with
    | exist _ l _ => l
    end.

  Program Definition init_state : state :=
    exist _ (List.repeat V.init delay) _.
  Next Obligation. apply repeat_length. Qed.
  
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
    List.nth i (list_of_state s) V.init.

  Lemma value_init_state :
    forall i (pf : i < delay), value i pf init_state = V.init.
  Proof.
    intros i pf; unfold value, init_state, list_of_state.
    clear pf; revert i; induction delay; simpl; destruct i; auto.
  Qed.
    
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
    assert (nth (S i) (v_in :: removelast (t :: l0)) V.init =
            nth i (removelast (t :: l0)) V.init) as -> by auto.
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

  (* R2: The output of the initial state is the default value V.init. *)
  Axiom init_state_output : output init_state = V.init.

  (* R3: *)
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

  Lemma init_state_output : output init_state = V.init.
  Proof.
    unfold init_state, output; simpl.
    rewrite Delay1Bus.value_init_state; auto.
  Qed.    

  Lemma step_output :
    forall (v_in : val) (s_in : state),
      let s_out := step v_in s_in in
      output s_out = v_in.
  Proof.
    intros v_in s_in; simpl.
    destruct (Delay1Bus.step_values v_in s_in) as [H1 _]; auto.
  Qed.
End Delay1Bus_of_DelayNBus.

Module Type PRIMARY_SIDE.
  Parameter is_primary : bool.
End PRIMARY_SIDE.  

Module Type PILOT_FLYING_SYSTEM_SIDE (V : VAL) (P : PRIMARY_SIDE).
  Notation val := V.t.
  Notation is_true := V.is_true.
  Coercion is_true : val >-> bool.
  Notation is_primary := P.is_primary.
  
  (* The uninterpreted type of FGS side states *)
  Parameter state : Type.
  Parameter init_state : state.

  (* The transition function *)
  Parameter step : forall (ts ospf : val) (s : state), state.

  (* Projections for accessing parts of the state *)
  Parameter pre_TS : state -> val.
  Parameter pre_OSPF : state -> val.

  (* Is this the flying side? *)
  Parameter pilot_flying : state -> bool.

  (* Auxiliary functions for stating requirements *)
  Definition rise (s : state) (old : state -> bool) (new : bool) : bool :=
    negb (old s) && new.
  Definition rise_ts (s : state) (ts : bool) : bool := rise s pre_TS ts.
  Definition rise_ospf (s : state) (ospf : bool) : bool := rise s pre_OSPF ospf.

  (*** High-level requirements ***)

  (* This side is flying initially only if it's the primary side. *)
  Axiom hlr1 : pilot_flying init_state = is_primary.

  (* pre_TS set to true initially -- this ensures that we don't respond 
     to a spurious rising edge in the initial state. *)
  Axiom hlr2 : is_true (pre_TS init_state).

  (* pre_OSPF set to true if other side is flying, otherwise false. *)
  Axiom hlr3 : is_true (pre_OSPF init_state) = negb is_primary.

  (* If this side is flying and we observe a rising edge on the OSPF channel, 
     then we're no longer flying in the next state. *)
  Axiom hlr4 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = true ->
      rise_ospf s ospf = true ->
      pilot_flying (step ts ospf s) = false.

  (* If this side is flying and we DON'T observe a rising OSPF edge, 
     then we continue flying in the next state. *)
  Axiom hlr5 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = true ->
      rise_ospf s ospf = false ->
      pilot_flying (step ts ospf s) = true.

  (* If this side isn't flying and we observe a rise TS edge, 
     then we're flying in the next state. *)
  Axiom hlr6 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = false->
      rise_ts s ts = true ->
      pilot_flying (step ts ospf s) = true.

  (* If this side isn't flying and we DON'T observe a rise TS edge, 
     then we're NOT flying in the next state. *)
  Axiom hlr7 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = false ->
      rise_ts s ts = false ->
      pilot_flying (step ts ospf s) = false.

  (* pre_TS is updated at each step to equal the incoming value on the 
     TS channel *)
  Axiom hlr8 :
    forall (s : state) (ts ospf : val),
      pre_TS (step ts ospf s) = ts.

  (* pre_OSPF is updated at each step to equal the incoming value on the 
     OSPF channel *)
  Axiom hlr9 :
    forall (s : state) (ts ospf : val),
      pre_OSPF (step ts ospf s) = ospf.
End PILOT_FLYING_SYSTEM_SIDE.

Module PilotFlyingSystem_Side (V : VAL) (P : PRIMARY_SIDE)
  : PILOT_FLYING_SYSTEM_SIDE V P.
      
  Notation val := V.t.
  Notation is_true := V.is_true.
  Coercion is_true : val >-> bool.
  Notation is_primary := P.is_primary.

  Inductive PilotFlyingSide : Type := PilotFlying | NotPilotFlying.
  
  Record the_state : Type :=                                                           
    mkState {
        status : PilotFlyingSide;
        pre_TS : val;
        pre_OSPF : val
      }.
  Definition state : Type := the_state.

  Definition init_state : state :=
    mkState
      (if is_primary then PilotFlying else NotPilotFlying)
      (* pre_TS = *) V.high
      (* pre_OSPF = *) (if is_primary then V.low else V.high).

  Definition rise (s : state) (old : state -> bool) (new : bool) : bool :=
    negb (old s) && new.
  Definition rise_ts (s : state) (ts : bool) : bool := rise s pre_TS ts.
  Definition rise_ospf (s : state) (ospf : bool) : bool := rise s pre_OSPF ospf.
  
  Definition step (ts ospf : val) (s : state) : state :=
    let next_pfs :=
        match status s with
        (* Transition 1: Other side becomes the flying side *)
        | PilotFlying =>
          if rise_ospf s ospf then NotPilotFlying else PilotFlying

        (* Transition 2: Transfer switch pressed *)
        | NotPilotFlying =>
          if rise_ts s ts then PilotFlying else NotPilotFlying
        end
    in
    mkState next_pfs ts ospf.

  Definition pilot_flying (s : state) : bool :=
    match status s with
    | PilotFlying => true
    | NotPilotFlying => false
    end.

  (* This side is flying initially only if it's the primary side. *)
  Lemma hlr1 : pilot_flying init_state = is_primary.
  Proof.
    unfold pilot_flying, init_state; simpl.
    destruct is_primary; auto.
  Qed.    

  (* pre_TS set to true initially -- this ensures that we don't respond 
     to a spurious rising edge in the initial state. *)
  Lemma hlr2 : is_true (pre_TS init_state).
  Proof. 
    unfold init_state, pre_TS; simpl.
    apply V.high_is_true.
  Qed.    
    
  (* pre_OSPF set to true if other side is flying, otherwise false. *)
  Lemma hlr3 : is_true (pre_OSPF init_state) = negb is_primary.
  Proof.
    unfold init_state, pre_OSPF; simpl; destruct is_primary; simpl.
    { apply V.low_is_false. }
    apply V.high_is_true.
  Qed.    

  (* If this side is flying and we observe a rising edge on the OSPF channel, 
     then we're no longer flying in the next state. *)
  Lemma hlr4 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = true ->
      rise_ospf s ospf = true ->
      pilot_flying (step ts ospf s) = false.
  Proof.
    intros s ts ospf; unfold pilot_flying, rise_ospf; simpl; destruct (status s).
    { intros _; unfold rise_ospf; intros ->; auto. }
    inversion 1.
  Qed.    

  (* If this side is flying and we DON'T observe a rising OSPF edge, 
     then we continue flying in the next state. *)
  Lemma hlr5 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = true ->
      rise_ospf s ospf = false ->
      pilot_flying (step ts ospf s) = true.
  Proof.
    intros s ts ospf; unfold pilot_flying, rise_ospf; simpl; destruct (status s).
    { intros _; unfold rise_ospf; intros ->; auto. }
    inversion 1.
  Qed.    

  (* If this side isn't flying and we observe a rising TS edge, 
     then we're flying in the next state. *)
  Lemma hlr6 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = false ->
      rise_ts s ts = true ->
      pilot_flying (step ts ospf s) = true.
  Proof.
    intros s ts ospf; unfold pilot_flying, rise_ospf; simpl; destruct (status s).
    { inversion 1. }
    intros _; unfold rise_ts; intros ->; auto.
  Qed.    

  (* If this side isn't flying and we DON'T observe a rising TS edge, 
     then we're NOT flying in the next state. *)
  Lemma hlr7 :
    forall (s : state) (ts ospf : val),
      pilot_flying s = false ->
      rise_ts s ts = false ->
      pilot_flying (step ts ospf s) = false.
  Proof.
    intros s ts ospf; unfold pilot_flying, rise_ospf; simpl; destruct (status s).
    { inversion 1. }
    intros _; unfold rise_ts; intros ->; auto.
  Qed.    

  (* pre_TS is updated at each step to equal the incoming value on the 
     TS channel *)
  Lemma hlr8 :
    forall (s : state) (ts ospf : val),
      pre_TS (step ts ospf s) = ts.
  Proof. auto. Qed.

  (* pre_OSPF is updated at each step to equal the incoming value on the 
     OSPF channel *)
  Lemma hlr9 :
    forall (s : state) (ts ospf : val),
      pre_OSPF (step ts ospf s) = ospf.
  Proof. auto. Qed.
End PilotFlyingSystem_Side.

Module BoolInitHigh <: VAL.
  Definition t := bool.                          
  Definition init := true.
  Definition is_true (b : t) : bool := b.
  Definition high := true.
  Definition low := false.
  Lemma high_is_true : is_true high = true.
  Proof. unfold is_true, high; reflexivity. Qed.
  Lemma low_is_false : is_true low = false.
  Proof. unfold is_true, low; reflexivity. Qed.
End BoolInitHigh.    

Module BoolInitLow <: VAL.
  Definition t := bool.                          
  Definition init := false.
  Definition is_true (b : t) : bool := b.
  Definition high := true.
  Definition low := false.
  Lemma high_is_true : is_true high = true.
  Proof. unfold is_true, high; reflexivity. Qed.
  Lemma low_is_false : is_true low = false.
  Proof. unfold is_true, low; reflexivity. Qed.
End BoolInitLow.    

Module PilotFlyingSystem.
  Module LeftSidePrimary <: PRIMARY_SIDE. Definition is_primary := true.
  End LeftSidePrimary.

  Module RightSideNotPrimary <: PRIMARY_SIDE. Definition is_primary := false.
  End RightSideNotPrimary.
    
  Module Left_Side := PilotFlyingSystem_Side BoolInitHigh LeftSidePrimary.
  Module Right_Side := PilotFlyingSystem_Side BoolInitLow RightSideNotPrimary.

  Module LR_Bus := Delay1Bus_of_DelayNBus BoolInitHigh.
  Module RL_Bus := Delay1Bus_of_DelayNBus BoolInitLow.

  Record state : Type :=
    mkState {
        left_side  : Left_Side.state;
        right_side : Right_Side.state;

        lr_bus : LR_Bus.state;
        rl_bus : RL_Bus.state;

        pre_TS : bool                   
      }.

  Definition init_state : state :=
    mkState
      Left_Side.init_state
      Right_Side.init_state
      LR_Bus.init_state
      RL_Bus.init_state
      true.

  (* State transition relation *)
  Section step.
    Variables (s : state) (ts : bool).

    (* Update LR_Bus and Right_Side *)
    Definition c1 := Left_Side.pilot_flying (left_side s).
    Definition next_LR := LR_Bus.step c1 (lr_bus s).
    Definition c2 := LR_Bus.output next_LR.
    Definition next_RS := Right_Side.step ts c2 (right_side s).
    
    (* Update RL_Bus and Left_Side *)    
    Definition c3 := Right_Side.pilot_flying (right_side s).
    Definition next_RL := RL_Bus.step c3 (rl_bus s).
    Definition c4 := RL_Bus.output next_RL.
    Definition next_LS := Left_Side.step ts c4 (left_side s).
    
    Definition step : state := 
      (* Return the resulting state *)
      mkState
        next_LS
        next_RS
        next_LR
        next_RL
        ts.

    Lemma c1_c2 : c1 = c2.
    Proof. unfold c2, next_LR; rewrite LR_Bus.step_output; auto. Qed.

    Lemma c3_c4 : c3 = c4.
    Proof. unfold c4, next_RL; rewrite RL_Bus.step_output; auto. Qed.
  End step.    
  
  (* Observable behaviors: *)
  Definition left_pilot_flying (s : state) : bool :=
    Left_Side.pilot_flying (left_side s).
  Definition right_pilot_flying (s : state) : bool :=
    Right_Side.pilot_flying (right_side s).
End PilotFlyingSystem.

Module SystemRequirements.
  Import PilotFlyingSystem.

  Inductive step_star : state -> state -> Prop := 
  | step_refl : forall s, step_star s s
  | step_trans :
      forall s s' ts,
        let s'' := step s ts in 
        step_star s'' s' ->
        step_star s s'.

  Inductive reachable : state -> Prop :=
  | reachable_init : reachable init_state
  | reachable_step_star :
      forall s s',
        reachable s ->
        step_star s s' ->
        reachable s'.

  Inductive valid : state -> Prop :=
  | mkValid :
      forall s,
        (* pre_TS consistency *)
        Left_Side.pre_TS (left_side s) = pre_TS s ->
        Right_Side.pre_TS (right_side s) = pre_TS s ->        

        (* pre_OSPF consistency *)
        Left_Side.pre_OSPF (left_side s) = RL_Bus.output (rl_bus s) ->
        Right_Side.pre_OSPF (right_side s) = LR_Bus.output (lr_bus s) ->        

        (* at least one side is flying *)
        left_pilot_flying s \/ right_pilot_flying s ->

        (* buses differ when sides same *)
        (left_pilot_flying s = right_pilot_flying s ->
         LR_Bus.output (lr_bus s) = negb (RL_Bus.output (rl_bus s))) -> 
        
        valid s.

  Lemma rise_right_ospf_left_pilot_flying :
    forall s ts,
      Left_Side.pre_OSPF (left_side s) = RL_Bus.output (rl_bus s) ->
      Right_Side.pre_OSPF (right_side s) = LR_Bus.output (lr_bus s) ->
      right_pilot_flying s ->            
      (left_pilot_flying s = right_pilot_flying s ->
       LR_Bus.output (lr_bus s) = negb (RL_Bus.output (rl_bus s))) ->
      Right_Side.rise_ospf (right_side s) (c2 s) = true ->
      Left_Side.pilot_flying (Left_Side.step ts (c4 s) (left_side s)).
  Proof.
    intros s ts H2 H3 H4 H5 H6.
    unfold Right_Side.rise_ospf, Right_Side.rise in H6.
    rewrite Bool.andb_true_iff in H6; destruct H6 as [H6 H7].
    rewrite <-c1_c2 in H7; unfold c1 in H7.
    rewrite Left_Side.hlr5; try reflexivity; auto.
    unfold Left_Side.rise_ospf, Left_Side.rise.
    apply Bool.andb_false_intro1.
    unfold Left_Side.is_true.
    rewrite H2; rewrite H3 in H6; rewrite <-H5.
    { unfold Right_Side.is_true in H6; generalize H6.
      destruct (LR_Bus.output _); auto. }
    rewrite H4; unfold left_pilot_flying; rewrite H7; auto. 
  Qed.

  Lemma rise_left_ospf_right_pilot_flying :
    forall s ts,
      Left_Side.pre_OSPF (left_side s) = RL_Bus.output (rl_bus s) ->
      Right_Side.pre_OSPF (right_side s) = LR_Bus.output (lr_bus s) ->
      left_pilot_flying s ->            
      (left_pilot_flying s = right_pilot_flying s ->
       LR_Bus.output (lr_bus s) = negb (RL_Bus.output (rl_bus s))) ->
      Left_Side.rise_ospf (left_side s) (c4 s) = true ->
      Right_Side.pilot_flying (Right_Side.step ts (c2 s) (right_side s)).
  Proof.
    intros s ts H2 H3 H4 H5 H6.
    unfold Left_Side.rise_ospf, Left_Side.rise in H6.
    rewrite Bool.andb_true_iff in H6; destruct H6 as [H6 H7].
    rewrite <-c3_c4 in H7; unfold c3 in H7.
    rewrite Right_Side.hlr5; try reflexivity; auto.
    unfold Right_Side.rise_ospf, Right_Side.rise.
    apply Bool.andb_false_intro1.
    rewrite H3; rewrite H2 in H6; rewrite H5.
    { unfold Left_Side.is_true in H6; rewrite H6; auto. }
    rewrite H4; unfold right_pilot_flying; rewrite H7; auto. 
  Qed.
  
  Lemma valid_step_valid :
    forall s ts,
      valid s ->
      valid (step s ts).
  Proof.
    (* surely automatable with some effort *)
    intros s ts; inversion 1; subst; constructor.
    { unfold step, next_LS; simpl; rewrite Left_Side.hlr8; auto. }
    { unfold step, next_RS; simpl; rewrite Right_Side.hlr8; auto. }
    { unfold step, next_LS; simpl. rewrite Left_Side.hlr9; auto. }
    { unfold step, next_RS; simpl. rewrite Right_Side.hlr9; auto. }    
    { destruct H4 as [H4|H4]; unfold step, left_pilot_flying, right_pilot_flying; simpl.
      { unfold next_LS, next_RS.
        destruct (Left_Side.rise_ospf (left_side s) (c4 s)) eqn:H6.
        { right; apply rise_left_ospf_right_pilot_flying; auto. }
        left; rewrite Left_Side.hlr5; try reflexivity; auto. }
      unfold next_LS, next_RS.
      destruct (Right_Side.rise_ospf (right_side s) (c2 s)) eqn:H6.
      { left; apply rise_right_ospf_left_pilot_flying; auto. }
      right; rewrite Right_Side.hlr5; try reflexivity; auto. }
    unfold left_pilot_flying, right_pilot_flying, step; simpl.
    unfold next_LS, next_RS, next_RL, next_LR.
    rewrite RL_Bus.step_output, LR_Bus.step_output; intros H6.
    unfold c1, c3; destruct H4 as [H4|H4].
    { destruct (Left_Side.rise_ospf (left_side s) (c4 s)) eqn:H7.
      { assert (H8: Right_Side.pilot_flying (Right_Side.step ts (c2 s) (right_side s))).
        { apply rise_left_ospf_right_pilot_flying; auto. }
        rewrite <-H6 in H8; rewrite Left_Side.hlr4 in H8; auto; inversion H8. }
      rewrite Left_Side.hlr5 in H6; auto.
      unfold left_pilot_flying in H4; rewrite H4.
      destruct (Right_Side.pilot_flying (right_side s)) eqn:H8; auto.
      assert (H9: Right_Side.rise_ospf (right_side s) (c2 s) = false).
      { destruct (Right_Side.rise_ospf _ _) eqn:H9; auto.
        rewrite Right_Side.hlr4 in H6; auto. }
      unfold Left_Side.rise_ospf, Left_Side.rise, Left_Side.is_true in H7.
      unfold Right_Side.rise_ospf, Right_Side.rise, Right_Side.is_true in H9.
      rewrite H2 in H7; rewrite H3 in H9; rewrite H5 in H9.
      { unfold c4, next_RL in H7; rewrite RL_Bus.step_output in H7.
        unfold c2, next_LR in H9; rewrite LR_Bus.step_output in H9.
        unfold c3 in H7; unfold c1 in H9; rewrite H8 in H7; rewrite H4 in H9.
        rewrite Bool.negb_involutive, Bool.andb_comm in H9; simpl in H9.
        rewrite H9 in H7; auto. }
      unfold left_pilot_flying, right_pilot_flying; rewrite H4, H8; auto. }
    destruct (Right_Side.rise_ospf (right_side s) (c2 s)) eqn:H7.
    { assert (H8: Left_Side.pilot_flying (Left_Side.step ts (c4 s) (left_side s))).
      { apply rise_right_ospf_left_pilot_flying; auto. }
      rewrite H6 in H8; rewrite Right_Side.hlr4 in H8; auto; inversion H8. }
    rewrite Right_Side.hlr5 in H6; auto.
    unfold right_pilot_flying in H4; rewrite H4.
    destruct (Left_Side.pilot_flying (left_side s)) eqn:H8; auto.
    assert (H9: Left_Side.rise_ospf (left_side s) (c4 s) = false).
    { destruct (Left_Side.rise_ospf _ _) eqn:H9; auto.
      rewrite Left_Side.hlr4 in H6; auto. }
    unfold Right_Side.rise_ospf, Right_Side.rise, Right_Side.is_true in H7.
    unfold Left_Side.rise_ospf, Left_Side.rise, Left_Side.is_true in H9.    
    rewrite H2 in H9; rewrite H3 in H7; rewrite <-H5 in H9.
    { unfold c4, next_RL in H9; rewrite RL_Bus.step_output in H9.
      unfold c2, next_LR in H7; rewrite LR_Bus.step_output in H7.
      unfold c3 in H9; unfold c1 in H7; rewrite H8 in H7; rewrite H4 in H9.
      rewrite Bool.andb_comm in H9; simpl in H9; rewrite H9 in H7; auto. }
    unfold left_pilot_flying, right_pilot_flying; rewrite H4, H8; auto. 
  Qed.      

  Lemma valid_step_star_valid s s' :
    step_star s s' ->
    valid s ->
    valid s'.
  Proof.
    induction 1; auto; intros Hval.
    apply IHstep_star.
    apply valid_step_valid; auto.
  Qed.

  Lemma init_valid : valid init_state.
  Proof.
    unfold init_state; constructor; simpl; auto.
    { generalize Left_Side.hlr2; auto. }
    { generalize Right_Side.hlr2; auto. }
    { generalize Left_Side.hlr3; unfold Left_Side.is_true; intros ->.
      rewrite RL_Bus.init_state_output; auto. }
    { generalize Right_Side.hlr3; unfold Right_Side.is_true; intros ->.
      rewrite LR_Bus.init_state_output; auto. }
    { left; unfold left_pilot_flying; simpl; rewrite Left_Side.hlr1; reflexivity. }
    unfold left_pilot_flying; simpl; rewrite Left_Side.hlr1.
    unfold right_pilot_flying; simpl; rewrite Right_Side.hlr1; inversion 1.
  Qed.    
                       
  Lemma reachable_valid s :
    reachable s ->
    valid s.
  Proof.
    induction 1; subst.
    { apply init_valid. }
    eapply valid_step_star_valid; eauto.
  Qed.    

  (** High-level System Requirements *)
  
  Definition pressed (s : state) (ts : bool) := 
    pre_TS s = false /\ ts = true.

  Definition switching_sides (s : state) :=
    (left_pilot_flying s /\ LR_Bus.output (lr_bus s) = false) \/
    (right_pilot_flying s /\ RL_Bus.output (rl_bus s) = false).

  Theorem at_least_one_pilot_flying :
    forall s,
      reachable s ->
      left_pilot_flying s \/ right_pilot_flying s.
  Proof.
    intros s H; generalize (reachable_valid _ H).
    inversion 1; subst; auto.
  Qed.    

  Theorem at_most_one_pilot_flying_except_when_switching_sides :
    forall s,
      reachable s -> 
      ~switching_sides s ->
      left_pilot_flying s = negb (right_pilot_flying s).
  Proof.
    intros s H H0; generalize (reachable_valid _ H); inversion 1; subst.
    destruct H6.
    { destruct (right_pilot_flying s) eqn:H8; auto.
      elimtype False; apply H0; unfold switching_sides.
      rewrite H7, H6, H8; auto.
      destruct (RL_Bus.output (rl_bus s)).
      { left; split; reflexivity. }
      right; split; reflexivity. }
    rewrite H6; destruct (left_pilot_flying s) eqn:H8; auto.
    elimtype False; apply H0; unfold switching_sides.
    rewrite H6, H8, H7; auto.
    destruct (RL_Bus.output (rl_bus s)).
    { left; split; reflexivity. }
    right; split; reflexivity. 
  Qed.

  Theorem pressing_transfer_changes_side_l2r : 
    forall s ts,
      reachable s ->
      left_pilot_flying s ->
      pressed s ts ->
      right_pilot_flying (step s ts).
  Proof.
    intros s ts H H1 [H2 H3].
    generalize (reachable_valid _ H); inversion 1; subst.
    unfold right_pilot_flying, step; simpl; unfold next_RS.
    
    rewrite Right_Side.hlr6; try reflexivity.
    
    
End SystemRequirements.    
    
  
  
  
