Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Omega.

Definition odd := PeanoNat.Nat.Odd.

Section ecc.
  Variable N : nat.
  Hypothesis N_odd : odd N.

  (* codes: finite functions mapping {0..N-1} to bool *)
  Definition code := {ffun 'I_N -> bool}.
  Definition code0 : code := finfun (fun i : 'I_N => false).
  Definition code1 : code := finfun (fun i : 'I_N => true).  

  (* encode *)
  Variable encode : bool -> code.
  Hypothesis encode_ok :
    forall (b:bool) (i:'I_N), (encode b) i = b.

  (* hamming distance *)
  Definition hamming (c1 c2 : code) : nat :=
    \sum_(i : 'I_N | c1 i != c2 i) 1.

  Lemma hamming_comm c1 c2 : hamming c1 c2 = hamming c2 c1.
  Proof. by apply: congr_big => // i; rewrite eq_sym. Qed.

  (* decode *)
  Variable decode : code -> bool.
  Hypothesis decode_ok :
    forall c : code,
      (hamming c code0 < hamming c code1 -> decode c = false) /\
      hamming c code1 < hamming c code0 -> decode c = true.

  (* syndrome *)
  Variable syndrome : code -> code.
  Hypothesis syndrome_ok :
    forall c : code,
      hamming c (syndrome c) <= Nat.div2 N.

  Lemma odd_decomp :
    forall n : nat, odd n -> exists n', n = 2 * n' + 1.
  Proof. move => n []n' ->; exists n' => //. Qed. (* by defn. of odd *)

  Lemma hamming_code0_code1_N :
    forall c : code,
      hamming c code0 + hamming c code1 = N.
  Proof.
    rewrite /hamming /code0 /code1 => c; clear - c.
    rewrite !sum1_card -cardUI.
  Admitted.
    
  Lemma syndrome_hamming_neq :
    forall c : code,
      hamming (syndrome c) code0 != hamming (syndrome c) code1.
  Proof.
    case: (odd_decomp N_odd) => N' H c.
    move: (syndrome_ok code0); rewrite H.
    have ->: (2*N'+1 = (2*N'+1)%coq_nat) by [].    
    have ->: (2*N'+1 = (2*N').+1)%coq_nat by omega.
    rewrite PeanoNat.Nat.div2_succ_double.
  
  Theorem decode_encode_id :
    forall b : bool, decode (syndrome (encode b)) = b.
  Proof.
    intros b.
    have H: hamming c (

  