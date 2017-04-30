Require Import components.

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

  Theorem pressing_changes_side_right : 
    forall s ts,
      reachable s ->
      pressed s ts ->
      right_pilot_flying s = false ->      
      right_pilot_flying (step s ts).
  Proof.
    intros s ts H [H1 H2] H3.
    generalize (reachable_valid _ H); inversion 1; subst.
    unfold right_pilot_flying, step; simpl; unfold next_RS.
    rewrite Right_Side.hlr6; try reflexivity; auto.
    unfold Right_Side.rise_ts, Right_Side.rise.
    rewrite H5, H1; auto.
  Qed.    

  Theorem pressing_changes_side_left :
    forall s ts,
      reachable s ->
      pressed s ts ->
      left_pilot_flying s = false ->      
      left_pilot_flying (step s ts).
  Proof.
    intros s ts H [H1 H2] H3.
    generalize (reachable_valid _ H); inversion 1; subst.
    unfold left_pilot_flying, step; simpl; unfold next_LS.
    rewrite Left_Side.hlr6; try reflexivity; auto.
    unfold Left_Side.rise_ts, Left_Side.rise.
    rewrite H4, H1; auto.
  Qed.    

  Theorem left_initial_pilot : left_pilot_flying init_state.
  Proof.
    unfold init_state, left_pilot_flying; simpl.
    rewrite Left_Side.hlr1; reflexivity.
  Qed.

  Theorem no_change_unless_switching_or_pressed_left :
    forall s ts,
      reachable s ->
      ~switching_sides s ->
      ~pressed s ts ->
      left_pilot_flying (step s ts) = left_pilot_flying s.
  Proof.
    intros s ts H H1 H2.
    generalize (reachable_valid _ H); inversion 1; subst.
    unfold left_pilot_flying, step; simpl; unfold next_LS.
    destruct (Left_Side.pilot_flying (left_side s)) eqn:H9.
    { destruct (Left_Side.pilot_flying (Left_Side.step _ _ _)) eqn:H10; auto.
      generalize (at_most_one_pilot_flying_except_when_switching_sides _ H H1).
      unfold left_pilot_flying in *; rewrite H9; intros Hx; symmetry in Hx.
      assert (Hy: Right_Side.pilot_flying (right_side s) = false).
      { unfold right_pilot_flying in Hx.
        destruct (Right_Side.pilot_flying (right_side s)); auto. }
      assert (H11: Left_Side.rise_ospf (left_side s) (c4 s) = true).
      { destruct (Left_Side.rise_ospf (left_side s) (c4 s)) eqn:H11; auto.
        rewrite Left_Side.hlr5 in H10; auto. }
      unfold Left_Side.rise_ospf, Left_Side.rise, Left_Side.is_true in H11.
      rewrite H5 in H11.
      assert (H12: RL_Bus.output (rl_bus s) = false).
      { destruct (RL_Bus.output (rl_bus s)); auto. }
      unfold c4, next_RL, c3 in H11.
      rewrite Hy, RL_Bus.step_output in H11.
      rewrite H12 in H11; auto. }
    unfold right_pilot_flying in *.
    generalize (at_most_one_pilot_flying_except_when_switching_sides _ H H1).
    unfold left_pilot_flying, right_pilot_flying in *; intros H10.
    unfold c4, next_RL; rewrite RL_Bus.step_output; unfold c3.
    rewrite Left_Side.hlr7; auto.
    unfold Left_Side.rise_ts, Left_Side.rise, Left_Side.is_true; rewrite H3.
    clear - H2; unfold pressed in H2.
    destruct (pre_TS s); auto.
    destruct ts; auto; simpl; elimtype False; auto.
  Qed.    

  Theorem no_change_unless_switching_or_pressed_right :
    forall s ts,
      reachable s ->
      ~switching_sides s ->
      ~pressed s ts ->
      right_pilot_flying (step s ts) = right_pilot_flying s.
  Proof.
    intros s ts H H1 H2.
    generalize (reachable_valid _ H); inversion 1; subst.
    unfold right_pilot_flying, step; simpl; unfold next_RS.
    destruct (Right_Side.pilot_flying (right_side s)) eqn:H9.
    { destruct (Right_Side.pilot_flying (Right_Side.step _ _ _)) eqn:H10; auto.
      generalize (at_most_one_pilot_flying_except_when_switching_sides _ H H1).
      unfold right_pilot_flying in *; rewrite H9; intros Hx; symmetry in Hx.
      assert (Hy: Left_Side.pilot_flying (left_side s) = false).
      { unfold left_pilot_flying in Hx.
        destruct (Left_Side.pilot_flying (left_side s)); auto. }
      assert (H11: Right_Side.rise_ospf (right_side s) (c2 s) = true).
      { destruct (Right_Side.rise_ospf (right_side s) (c2 s)) eqn:H11; auto.
        rewrite Right_Side.hlr5 in H10; auto. }
      unfold Right_Side.rise_ospf, Right_Side.rise, Right_Side.is_true in H11.
      rewrite H6 in H11.
      assert (H12: LR_Bus.output (lr_bus s) = false).
      { destruct (LR_Bus.output (lr_bus s)); auto. }
      unfold c2, next_LR, c1 in H11.
      rewrite Hy, LR_Bus.step_output in H11.
      rewrite H12 in H11; auto. }
    unfold right_pilot_flying in *.
    generalize (at_most_one_pilot_flying_except_when_switching_sides _ H H1).
    unfold left_pilot_flying, right_pilot_flying in *; intros H10.
    unfold c2, next_LR; rewrite LR_Bus.step_output; unfold c1.
    rewrite Right_Side.hlr7; auto.
    unfold Right_Side.rise_ts, Right_Side.rise, Right_Side.is_true; rewrite H4.
    clear - H2; unfold pressed in H2.
    destruct (pre_TS s); auto.
    destruct ts; auto; simpl; elimtype False; auto.
  Qed.    
End SystemRequirements.    
