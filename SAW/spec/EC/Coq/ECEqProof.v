From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

From CryptolToCoq Require Import SAWCoreBitvectors.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.

From Crypto Require Import Curves.Weierstrass.Jacobian.


From Top Require Import GroupMulWNAF.
From Top Require Import EC_fiat_P384_7.
From Top Require Import EC_fiat_P384_gen.

Set Implicit Arguments.

Theorem ecEq_bv_true : forall n v,  
  ecEq (bitvector n) (PEqWord n) v v = true.

  intros.
  apply bvEq_refl.

Qed.

Theorem ecEq_bv_false : forall n v1 v2,
  v1 <> v2 ->
  ecEq (bitvector n) (PEqWord n) v1 v2 = false.

  intros.
  unfold ecEq.
  simpl.
  case_eq (bvEq n v1 v2); intros; trivial.
  apply bvEq_eq in H0.
  intuition.
Qed.

Theorem ecEq_vec_bv_true : forall n1 n2 v,
  (ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v) = true.

  intros.
  unfold ecEq.
  simpl.
  unfold vecEq.
  Locate foldr.
  Print foldr.

  Print SAWCoreVectorsAsCoqVectors.

Admitted.

Theorem ecEq_vec_bv_false : forall n1 n2 v1 v2,
  v1 <> v2 ->
  (ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2) = false.

Admitted.

Theorem ecNotEq_vec_bv_false : forall n1 n2 v,
  (ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v) = false.

    intros.
  unfold ecNotEq.
  

Admitted.

Theorem ecNotEq_vec_bv_true : forall n1 n2 v1 v2,
  v1 <> v2 ->
  (ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2) = true.
Admitted.

Theorem rep_false_eq_int_bv : forall n, (replicate n _ false) = (intToBv n 0).

Admitted.

Theorem ecOr_0_if : forall n x y, 
    ecOr (bitvector n) (PLogicWord n) x y = (replicate n _ false) ->
    (x = (replicate n _ false) /\ y = (replicate n _ false)).
Admitted.

Theorem fold_or_impl_0 : forall (n1 n2 : nat) x y,
  ecFoldl n1 (seq n2 Bool) (seq n2 Bool) (ecOr (seq n2 Bool) (PLogicSeqBool n2))
     y x = intToBv n2 0 ->
  (x = (replicate n1 _ (replicate n2 _ false)) /\ y = (replicate n2 _ false)).

  induction n1; intros; simpl in *.
  unfold replicate. simpl in *.
  generalize H.
  eapply (case0 (fun x => foldl (bitvector n2) (bitvector n2) 0%nat (ecOr (bitvector n2) (PLogicWord n2)) y x = intToBv n2 0 ->
x = nil (Vec n2 bool) /\ y = gen n2 bool (fun _ : Nat => false))); eauto; intuition.
  simpl in *; subst.
  rewrite <- rep_false_eq_int_bv.
  trivial.

  unfold replicate in *. simpl.
  generalize H.
  eapply (caseS' x); intuition;
  simpl in *;
  edestruct IHn1; eauto;
  subst.
  f_equal.
  edestruct ecOr_0_if; eauto.
  edestruct ecOr_0_if; eauto.

Qed.

Section ECEqProof.

  Definition F := seq 6 (seq 64 Bool).

  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).
  Variable Fone  : F.
  Variable Fopp  : F -> F.
  Variable Fadd  : F -> F -> F.
  Variable Fsub  : F -> F -> F.
  Variable Fmul  : F -> F -> F.
  Variable Fsquare : F -> F.
  Variable Finv : F -> F.
  Definition Fdiv (x y:F) := Fmul x (Finv y).

  Variable fiat_from_bytes : seq 384 Bool -> F.
  Variable fiat_to_bytes : F -> seq 384 Bool.

  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30).
  Local Notation "x ^ 3" := (x^2*x) (at level 30).

  Theorem fiat_field_nz_eq_0 : 
    (fiat_field_nz 0) = (intToBv 64 0).

    reflexivity.

  Qed.

  Theorem fiat_field_nz_neq_0 : forall x,
    x <> 0 ->
    (fiat_field_nz x) <> (intToBv 64 0).

    intuition.
    eapply H.
    eapply fold_or_impl_0; eauto.

  Qed.

  (* Here, we assume that the basic operations form a field up to strict equality.
   *)
  Definition Feq := (@eq F).
  Hypothesis F_Field : @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
  Existing Instance F_Field.

  (* Now we assume that equality is decidable. This, we could implement relatively easily.
   *)
  Hypothesis Feq_dec : DecidableRel (@eq F).
  Existing Instance Feq_dec.

  (* Here we assume the field has characteristic at least 3. *)
  Hypothesis Fchar_3 : @Ring.char_ge F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul 3.
  Existing Instance Fchar_3.

  Lemma zero_squared_zero : 0^2 = 0.
    nsatz.
  Qed.

  Lemma mul_zero_r: forall x, x * 0 = 0.
    intros.
    nsatz.
  Qed.

  Lemma mul_zero_l: forall x, 0 * x = 0.
    intros.
    nsatz.
  Qed.

  Lemma minus_zero_r : forall x, x - 0 = x.

    intros.
    nsatz.

  Qed.

  Lemma plus_zero_r : forall x, x + 0 = x.
    intros.
    nsatz.
  Qed.

  (* Here, we posit abstract EC curve parameters.  We could probably
     take the actual values for P-384 instead.
   *)
  Variable a : F.
  Variable b : F.

  (* Now we can instantiate the type of points on the
     curve in Jacobian/projective coordinates.
   *)
  Definition point := @Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec.


  Definition fromPoint (p:point) : (F*F*F) :=
    proj1_sig p.

  Definition fiat_point_add := fiat_point_add Fsquare Fmul Fsub Fadd.
  Definition fiat_point_add_jac := fiat_point_add false.

  Definition prodToSeq(p : F * F * F) : seq 3 F :=
    cons _ (fst (fst p)) _ (cons _ (snd (fst p)) _ (cons _ (snd p) _ (@nil F))).

  Theorem zero_lt_three : 0 < 3.
    intuition eauto.
  Qed.

  Theorem one_lt_three : 1 < 3.
    intuition eauto.
  Qed.

  Theorem two_lt_three : 2 < 3.
    intuition eauto.
  Qed.

  Definition seqToProd(p : seq 3 F) : F * F * F :=
    (nth_order p zero_lt_three, nth_order p one_lt_three, nth_order p two_lt_three).

  Definition fiat_point_add_jac_prod (p1 p2 : (F * F * F)) : (F * F * F) :=
    let p3 := fiat_point_add_jac (prodToSeq p1) (prodToSeq p2) in
    (seqToProd p3).


  Definition is_jacobian (p : F * F * F) :=
    let '(X, Y, Z) := p in
    if dec (Feq Z Fzero)
      then True
      else
       Feq (Fmul Y Y)
         (Fadd
            (Fadd (Fmul (Fmul X X) X)
               (Fmul 
                  (Fmul a X)
                  (Fmul 
                   (Fmul Z Z) 
                   (Fmul Z Z))))
            (Fmul b
               (Fmul 
                  (Fmul (Fmul Z Z) Z)
                  (Fmul (Fmul Z Z) Z)))).

  Definition zero_point_h : F * F * F := (0, 1, 0).
  Theorem zero_point_is_jacobian : is_jacobian zero_point_h.

    unfold is_jacobian, zero_point_h.
    simpl.
    unfold Feq.
    destruct (dec (0 = 0)); intuition.

  Qed.

  Definition zero_point : point :=
    exist _ zero_point_h zero_point_is_jacobian.

  Theorem fiat_point_add_jac_prod_is_jacobian : forall p1 p2,
    is_jacobian p1 ->
    is_jacobian p2 ->
    is_jacobian (fiat_point_add_jac_prod p1 p2).
  Admitted.

  Definition toPoint(p : F * F * F)(pf : is_jacobian p) : point :=
    exist _ p pf.

  Definition fiat_point_add_jacobian (p1 p2 : point) : point :=
    toPoint 
      (fiat_point_add_jac_prod (fromPoint p1) (fromPoint p2)) 
      (fiat_point_add_jac_prod_is_jacobian (fromPoint p1) (fromPoint p2) (proj2_sig p1) (proj2_sig p2)).


  (* Assume that squaring satisifes its spec. *)
  Hypothesis fiat_field_square_spec : forall (x : F), Fsquare x = Fmul x x.

  (* Assume that the curve paramFrometer a = -3, as it does for P-384. *)
  Hypothesis a_is_minus_3 : a = Fopp (1 + 1 + 1).

  (* Now, we can prove that the extracted Cryptol code computes the
     same point (up to strict equality) as the specialized (for a = -3)
     point-doubling procedure from fiat-crypto.
  *)

  Definition fiat_point_double := fiat_point_double Fsquare Fmul Fsub Fadd.

  Lemma double_eq_minus_3_h : forall p:point,
      fromPoint (Jacobian.double_minus_3 a_is_minus_3 p) =
      seqToProd (fiat_point_double (prodToSeq (fromPoint p))).
  Proof.

      intros [ [[x y] z] Hp ]; simpl.
      unfold prodToSeq, seqToProd, fromPoint, fiat_point_double, EC_fiat_P384_7.fiat_point_double; simpl.
      repeat rewrite fiat_field_square_spec.
      unfold sawAt, atWithDefault. simpl.
      unfold nth_order, nth. simpl.

      f_equal; intros.

      nsatz.
  
  Qed.

  Theorem prodToSeq_inv : forall x, prodToSeq (seqToProd x) = x.

  Admitted.

  Theorem seqToProd_inv : forall x, seqToProd (prodToSeq x) = x.

  Admitted.

  Theorem double_eq_minus_3 : forall p:point,
      prodToSeq (fromPoint (Jacobian.double_minus_3 a_is_minus_3 p)) =
      (fiat_point_double (prodToSeq (fromPoint p))).
  Proof.

    intros.
    rewrite double_eq_minus_3_h.
    rewrite prodToSeq_inv.
    reflexivity.

  Qed.

  Definition jac_eq (p1 p2 : F * F * F) :=
    let '(X1, Y1, Z1) := p1 in
    let '(X2, Y2, Z2) := p2 in
      if dec (Feq Z1 Fzero)
      then Feq Z2 Fzero
      else
       ~ Feq Z2 Fzero /\
       Feq (Fmul X1 (Fmul Z2 Z2)) (Fmul X2 (Fmul Z1 Z1)) /\
       Feq (Fmul Y1 (Fmul (Fmul Z2 Z2) Z2)) (Fmul Y2 (Fmul (Fmul Z1 Z1) Z1)).

  Theorem jac_eq_refl : forall p, jac_eq p p.
  Admitted.


  Theorem jac_eq_refl_gen : forall p1 p2,
    p1 = p2 ->
    jac_eq p1 p2.

    intros.
    rewrite H.
    apply jac_eq_refl.

  Qed.

  Theorem jac_eq_trans : forall p1 p2 p3,
    jac_eq p1 p2 ->
    jac_eq p2 p3 ->
    jac_eq p1 p3.
  Admitted.

  Theorem jac_eq_symm : forall p1 p2,
    jac_eq p1 p2 ->
    jac_eq p2 p1.
  Admitted.

  Theorem jacobian_eq_jac_eq : forall p1 p2,
    Jacobian.eq p1 p2 ->
    jac_eq (fromPoint p1) (fromPoint p2).
  Admitted.

  Lemma point_add_jac_eq_old : forall (a b:point),
      jac_eq (fromPoint (Jacobian.add a b))
      (seqToProd (fiat_point_add_jac (prodToSeq (fromPoint a)) (prodToSeq (fromPoint b)))).
  Proof.
      intros [ [[xa ya] za] Ha ] [ [[xb yb] zb] Hb ]; simpl.
    
      unfold fiat_point_add_jac, fromPoint, fiat_point_add, EC_fiat_P384_7.fiat_point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, fiat_field_cmovznz; simpl.
      repeat rewrite fiat_field_square_spec.
      unfold sawAt, atWithDefault. simpl.
      
      replace ((negb (if dec (xb * za ^ 2 - xa * zb ^ 2 = Fzero) then 0 else 1) &&
     negb (if dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = Fzero) then 0 else 1) &&
     (if dec (za = Fzero) then 0 else 1) && (if dec (zb = Fzero) then 0 else 1))%bool) with 
      (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
    (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))).

      case_eq (testForDouble za zb (xb * za ^ 2 - xa * zb ^ 2)
      (yb * (za * za ^ 2) - zb * zb ^ 2 * ya +
       (yb * (za * za ^ 2) - zb * zb ^ 2 * ya))); intros.

      replace (xa, ya, za) with (fromPoint
       (exist (fun '(X, Y, Z) => if dec (Z = 0) then True else Y ^ 2 = X ^ 3 + a * X * (Z ^ 2) ^ 2 + b * (Z ^ 3) ^ 2)
          (xa, ya, za) Ha)).
      rewrite <- double_eq_minus_3.
      rewrite seqToProd_inv.

      eapply jac_eq_trans; [idtac | apply jacobian_eq_jac_eq; apply Jacobian.double_minus_3_eq_double].
      apply jac_eq_refl_gen.
   
      unfold Jacobian.double, fromPoint; simpl.
      reflexivity.
      trivial.

      apply jac_eq_refl_gen.
      unfold Feq, seqToProd, nth_order, nth. simpl.
      destruct (dec (zb = 0)); subst.
      rewrite fiat_field_nz_eq_0.
      rewrite ecEq_bv_true.
      trivial.
      destruct (dec (za = 0)); subst.
      rewrite fiat_field_nz_eq_0.
      rewrite ecEq_bv_true.
      rewrite ecEq_bv_false.
      trivial.
      eapply fiat_field_nz_neq_0.
      trivial.
      repeat rewrite ecEq_bv_false; simpl.
      reflexivity.
      eapply fiat_field_nz_neq_0. trivial.
      eapply fiat_field_nz_neq_0. trivial.

      unfold testForDouble.
      destruct (dec (xb * za ^ 2 - xa * zb ^ 2 = 0)).
      simpl.
      rewrite e.
      rewrite <- rep_false_eq_int_bv.
      
      rewrite ecEq_vec_bv_true.
      unfold ecAnd. simpl.
      destruct (dec (yb * (za * za ^ 2) - zb * zb ^ 2 * ya + (yb * (za * za ^ 2) - zb * zb ^ 2 * ya) = 0)).
      rewrite e0.
      rewrite ecEq_vec_bv_true.
      simpl.
      destruct (dec (za = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      simpl.
      destruct (dec (zb = 0)).
      rewrite e1.
      rewrite ecNotEq_vec_bv_false.
      trivial.
      rewrite ecNotEq_vec_bv_true; intuition.
      rewrite ecEq_vec_bv_false; intuition.

      simpl.
      rewrite ecEq_vec_bv_false; intuition.

  Qed.

  (* Need a more general form of the point add correctness proof using Jacobian equality *)
  Lemma point_add_jac_eq : forall (a b:point) a' b',
    jac_eq (fromPoint a) (seqToProd a') ->
    jac_eq (fromPoint b) (seqToProd b') -> 
    jac_eq (fromPoint (Jacobian.add a b)) (seqToProd (fiat_point_add_jac a' b')).

  Admitted.

  Definition groupMul := @groupMul point Jacobian.add zero_point.
  Definition fiat_point_mul := fiat_point_mul Fsquare Fmul Fsub Fadd Fopp.

  Variable min_l : forall n, Nat.min n n = n.

  Variable unsignedToNat : seq 384 Bool -> nat.

  (* Jacobian.v defines an Equivalence instance for Jacobian.eq. Use this to construct a Setoid. *)
  Instance jac_eq_setoid : Setoid point := {equiv := Jacobian.eq}.

  Theorem jac_add_assoc : forall (a b c : point),
    (Jacobian.add (Jacobian.add a b) c) == (Jacobian.add a (Jacobian.add b c)).

  Admitted.

  Theorem jac_add_comm : forall (a b : point),
    (Jacobian.add a b) == (Jacobian.add b a).

  Admitted.

  Theorem jac_add_id_l : forall (a : point),
    (Jacobian.add zero_point a) == a.
  Admitted.

  Theorem jac_double_correct : forall (a : point),
    (Jacobian.double a) == (Jacobian.add a a).
  Admitted.

  Theorem jac_opp_correct : forall (a : point),
    (Jacobian.add a (Jacobian.opp a)) == zero_point.
  Admitted.

  Theorem jac_opp_add_distr : forall (a b : point),
    (Jacobian.opp (Jacobian.add a b)) == (Jacobian.add (Jacobian.opp a) (Jacobian.opp b)).
  Admitted.

  Theorem jac_opp_involutive  : forall (a : point),
    (Jacobian.opp (Jacobian.opp a)) == a.
  Admitted.

  Definition seqToList(A : Type)(n : nat)(s : seq n A) : list A :=
    to_list s.

  Definition windowsSeqToList (n : nat)(s : seq n (seq 16 Bool)) : list SignedWindow := 
    List.map (toSignedInteger 16) (seqToList s).

Definition fiat_pre_comp_table_gen (pred_pred_tsize : nat)
    (p : CryptolPrimitivesForSAWCore.seq (CryptolPrimitivesForSAWCore.TCNum 3) (CryptolPrimitivesForSAWCore.seq (CryptolPrimitivesForSAWCore.TCNum 6) (CryptolPrimitivesForSAWCore.seq (CryptolPrimitivesForSAWCore.TCNum 64) SAWCoreScaffolding.Bool)))  :=
   
(scanl Integer (Vec 3 (Vec 6 (bitvector 64))) (S pred_pred_tsize)
        (fun (z : Vec 3 (Vec 6 (bitvector 64))) (_ : Integer) =>
         EC_fiat_P384_7.fiat_point_add Fsquare Fmul Fsub Fadd false
           (EC_fiat_P384_7.fiat_point_double Fsquare Fmul Fsub Fadd p) z)
        p (CryptolPrimitivesForSAWCore.ecFromTo (CryptolPrimitivesForSAWCore.TCNum 1%nat) (CryptolPrimitivesForSAWCore.TCNum (S pred_pred_tsize)) SAWCoreScaffolding.Integer PLiteralInteger)).

  Theorem fiat_pre_comp_table_gen_7_equiv : forall (p : seq 3 (seq 6 (seq 64 Bool))),
    (fiat_pre_comp_table_gen 62 p) = (fiat_pre_comp_table Fsquare Fmul Fsub Fadd p).

    intros.
    reflexivity.

  Qed.


  Fixpoint preCompTable_fix (p : point) n prev :=
    match n with
    | O => prev :: List.nil
    | S n' => prev :: (preCompTable_fix p n'(Jacobian.add (Jacobian.double p) prev))
    end.

  Theorem preCompTable_h_cons : forall tsize p ls p2, 
  ls <> List.nil -> 
  (preCompTable_h Jacobian.add zero_point tsize (p :: ls) p2) = 
  p :: (preCompTable_h Jacobian.add zero_point tsize ls p2).

    induction tsize; unfold preCompTable_h in *; intuition; simpl in *.
    rewrite <- IHtsize.
    destruct ls; simpl in *. intuition.
    reflexivity.
    intuition.
    eapply app_cons_not_nil.
    symmetry.
    eauto.

  Qed.


  Theorem preCompTable_h_fix_equiv : forall tsize p1 p2,
    (preCompTable_h Jacobian.add zero_point tsize [p2] (Jacobian.double p1)) = 
    (preCompTable_fix p1 tsize p2).

    induction tsize; unfold preCompTable_h in *; intuition; simpl in *.
    rewrite <- IHtsize.
    eapply preCompTable_h_cons.
    intuition.
    discriminate.
  Qed.

  Theorem seqTolist_cons : forall (A : Type)(n : nat) (x : A) (s : Vector.t A n),
    seqToList (cons _ x _ s) = List.cons x (seqToList s).

    intros.
    unfold seqToList, to_list. simpl.
    reflexivity.

  Qed.

  Theorem scanl_gen_equiv : forall A n f1 f2 z1 x,
    (scanl Integer A n
           (fun (z : A) (_ : Integer) =>
            z1 z) x
           (gen n Integer f1))
    = 
    (scanl Integer A n
           (fun (z : A) (_ : Integer) =>
            z1 z) x
           (gen n Integer f2)).

    induction n; intuition; simpl in *.
    f_equal.
    apply IHn.
  Qed.

  Theorem preCompTable_fix_equiv : forall pred_pred_tsize p p2 p2',
    jac_eq (fromPoint p2) (seqToProd p2') ->
    List.Forall2 (fun x y => jac_eq (fromPoint x) (seqToProd y))
  (preCompTable_fix p (S pred_pred_tsize) p2)
(seqToList
  (scanl Integer (Vec 3 (Vec 6 (bitvector 64)))
     (S pred_pred_tsize)
     (fun (z : Vec 3 (Vec 6 (bitvector 64))) (_ : Integer) =>
      EC_fiat_P384_7.fiat_point_add Fsquare Fmul Fsub Fadd false
        (EC_fiat_P384_7.fiat_point_double Fsquare Fmul Fsub Fadd
           (prodToSeq (fromPoint p))) z)
     p2'
     (ecFromTo 1%nat (S pred_pred_tsize) Integer PLiteralInteger))).

    Local Opaque Jacobian.double Jacobian.add EC_fiat_P384_7.fiat_point_double EC_fiat_P384_7.fiat_point_add.

    induction pred_pred_tsize; intuition; simpl in *.
    rewrite seqTolist_cons.
    econstructor.
    trivial.
    econstructor.
    apply point_add_jac_eq.
    rewrite <- double_eq_minus_3_h.
    apply jacobian_eq_jac_eq.
    apply Jacobian.double_minus_3_eq_double.
    trivial.
    econstructor.

    rewrite seqTolist_cons in *.
    simpl in *.
    econstructor.
    trivial.
    erewrite scanl_gen_equiv.
    eapply IHpred_pred_tsize.

    apply point_add_jac_eq.
    rewrite <- double_eq_minus_3_h.
    apply jacobian_eq_jac_eq.
    apply Jacobian.double_minus_3_eq_double.
    trivial.
    
  Qed.

  Theorem recode_rwnaf_odd_eq_fold_list : forall pred_numWindows wsize n,
    (BinInt.Z.of_nat (unsignedToNat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat ((S pred_numWindows) * wsize)))%Z ->
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = spec.toZ (bvToBITS y))
  (recode_rwnaf_odd wsize pred_numWindows
     (BinInt.Z.lor (BinInt.Z.of_nat (unsignedToNat n)) 1))
  (fold_list (fiat_mul_scalar_rwnaf_loop_body n)
     (to_list
        (gen pred_numWindows (bitvector 64)
           (fun i : nat => intToBv 64 (Z.of_nat (addNat i 0%nat)))))
     (append 8 8 Bool (intToBv 8 0)
        (bvOr 8 (bvAnd 8 (drop Bool 376 8 n) (intToBv 8 255)) (intToBv 8 1)))).

    induction pred_numWindows; intros.
    simpl in *.
    econstructor.
    rewrite Z.mod_small.

    (* This only works when window size is less than a byte *)
    admit.
    intuition.
    (* non-negative *)
    admit.
    (* smaller than 2^wsize *)
    admit.
    econstructor.

  Abort.

  Fixpoint bv64Nats_h n v :=
    match n with
    | 0 => List.nil
    | S n' => (intToBv 64 (Z.of_nat v)) :: (bv64Nats_h n' (S v))
    end.

  Definition bv64Nats n := bv64Nats_h n 0.

  Theorem gen_nat_seq_eq_h : forall n v,
    (to_list
        (gen n (bitvector 64)
           (fun i : nat => intToBv 64 (Z.of_nat (addNat i v%nat)))))
    = bv64Nats_h n v.

    induction n; intuition; simpl in *.
    rewrite to_list_cons.
    f_equal.
    rewrite <- IHn.
    f_equal.  
    eapply gen_domain_eq.
    intros.
    rewrite (eqNatAddComm _ (S v)).
    simpl.
    rewrite eqNatAddComm.
    trivial.
  Qed.

  Theorem gen_nat_seq_eq : forall n,
    (to_list
        (gen n (bitvector 64)
           (fun i : nat => intToBv 64 (Z.of_nat (addNat i 0%nat)))))
    = bv64Nats n.

    intros.
    apply gen_nat_seq_eq_h.    
  Qed.

  Fixpoint nats_h n v :=
    match n with
    | 0 => List.nil
    | S n' => v :: (nats_h n' (S v))
    end.

  Definition nats n := nats_h n 0.


  Theorem foo : forall pred_numWindows wsize n z w,
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = spec.toZ (bvToBITS y))
  (recode_rwnaf_odd wsize pred_numWindows z)
  (fold_list (fiat_mul_scalar_rwnaf_loop_body n) (bv64Nats pred_numWindows) w).

    induction pred_numWindows; intros.
    simpl in *.
    admit.

    Local Opaque fiat_mul_scalar_rwnaf_loop_body.
    simpl.
    econstructor.
        

  Qed.

  Theorem fiat_mul_scalar_rwnaf_gen_equiv : forall pred_numWindows wsize n,
    List.Forall2 (fun x (y : bitvector 16) => x = (sbvToInt _ y))
    (recode_rwnaf wsize (S pred_numWindows) (unsignedToNat n)) 
    (seqToList (fiat_mul_scalar_rwnaf_gen pred_numWindows wsize n)).

    intros. 
    unfold recode_rwnaf, fiat_mul_scalar_rwnaf_gen.
    rewrite scanl_pair_eq.
    simpl.
    rewrite gen_nat_seq_eq.
    
  Qed.


  Definition numWindows := 55.
  Definition wsize := 7.

  Theorem wsize_nz : wsize <> 0%nat.
    unfold wsize in *.
    intuition.
    discriminate.
  Qed.

  Theorem numWindows_nz : numWindows <> 0%nat.

    unfold numWindows in *.
    intuition.
    discriminate.

  Qed.

  Theorem Proper_opp : Proper (Jacobian.eq ==> Jacobian.eq) (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_Field Feq_dec).
  Admitted.

  Definition conditional_subtract_if_even_ct := conditional_subtract_if_even_ct Fsquare Fadd Fsub Fmul Fopp.

  Definition fiat_point_opp p :=
    let '(x, y, z) := seqToProd p in
    prodToSeq (x, Fopp y, z).

  Theorem conditional_subtract_if_even_ct_jac_eq_ite : forall n p1 p2,
    jac_eq (seqToProd (EC_fiat_P384_7.conditional_subtract_if_even_ct Fsquare Fmul Fsub Fadd
        Fopp p1 n p2)) (seqToProd (if (Nat.even (unsignedToNat n)) then (fiat_point_add false p1 (fiat_point_opp p2)) else p1)).
  Admitted.

  Theorem groupMul_signedWindows_equiv: forall n t1 t2,
    List.Forall2 (fun x y => jac_eq (fromPoint x) (seqToProd y)) t1 (seqToList t2) ->
    jac_eq
  (fromPoint
     (groupMul_signedWindows Jacobian.add zero_point
        Jacobian.double wsize
        (groupMul_signed_table zero_point Jacobian.opp
           t1)
        (recode_rwnaf wsize numWindows (unsignedToNat n))))
  (seqToProd
     (ecFoldl 54 (seq 3 (seq 6 (seq 64 Bool))) 
        (seq 16 Bool)
        (fiat_double_add_body Fsquare Fmul Fsub Fadd Fopp t2)
        (fiat_select_point_ct
           (sign_extend_16_64
              (ecSShiftR 16 Integer PIntegralInteger
                 (ecAt 55 (seq 16 Bool) Integer
                    PIntegralInteger
                    (fiat_mul_scalar_rwnaf n)
                    (ecDiv Integer PIntegralInteger
                       (ecNumber 384 Integer PLiteralInteger)
                       (ecNumber 7 Integer PLiteralInteger)))
                 (ecNumber 1%nat Integer PLiteralInteger)))
           t2)
        (ecDrop 1%nat 54 (seq 16 Bool)
           (coerce (seq 55 (seq 16 Bool))
              (seq (tcAdd 1%nat 54) (seq 16 Bool))
              (seq_cong1 55 (tcAdd 1%nat 54) 
                 (seq 16 Bool)
                 (reflexivity (tcAdd 1%nat 54)))
              (ecReverse 55 (seq 16 Bool)
                 (fiat_mul_scalar_rwnaf n)))))).

    intros.
    

  Qed.

  Theorem fiat_pre_comp_table_0 : forall p,
    (ecAt 64 (seq 3 (seq 6 (seq 64 Bool))) Integer
           PIntegralInteger
           (fiat_pre_comp_table Fsquare Fmul Fsub Fadd
              p)
           (ecNumber 0%nat Integer PLiteralInteger)) = p.

  Admitted.

  Theorem fiat_point_opp_equiv : forall p,
    jac_eq 
    (fromPoint (Jacobian.opp p))
    (seqToProd (fiat_point_opp (prodToSeq (fromPoint p)))).

    intros.
    unfold fiat_point_opp. simpl.
    unfold seqToProd, prodToSeq, nth_order. simpl.
    destruct p. simpl.
    destruct x. simpl.
    destruct p. 
    apply jac_eq_refl.
  Qed.

  Theorem fiat_point_mul_signedRegular_equiv : forall n p,
    jac_eq
    (fromPoint
       (groupMul_signedRegular_table Jacobian.add zero_point
          Jacobian.double Jacobian.opp wsize numWindows p
          (unsignedToNat n)))
    (seqToProd
       (fiat_point_mul (prodToSeq (fromPoint p))
          n)).

    intros.
    unfold groupMul_signedRegular, groupMul_signedRegularWindows, fiat_point_mul, EC_fiat_P384_7.fiat_point_mul.      
    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply conditional_subtract_if_even_ct_jac_eq_ite.
    unfold groupMul_signedRegular_table, groupMul_signedRegular, groupMul_signedRegularWindows.
    case_eq (Nat.even (unsignedToNat n)); intros.
    eapply jac_eq_symm.
    eapply point_add_jac_eq.
    apply groupMul_signedWindows_equiv.
    rewrite <- fiat_pre_comp_table_gen_7_equiv.
    unfold preCompTable, wsize, tableSize.
    rewrite preCompTable_h_fix_equiv.
    apply preCompTable_fix_equiv.
    rewrite seqToProd_inv.
    apply jac_eq_refl.
    rewrite fiat_pre_comp_table_0.
    apply fiat_point_opp_equiv.
    
    apply jac_eq_symm.
    apply groupMul_signedWindows_equiv.
    unfold preCompTable, wsize, tableSize.
    rewrite preCompTable_h_fix_equiv.
    apply preCompTable_fix_equiv.
    rewrite seqToProd_inv.
    apply jac_eq_refl.

  Qed.

    
  Theorem point_mul_correct : forall (p : point) (n : seq 384 Bool),
      (BinInt.Z.of_nat (unsignedToNat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (numWindows * wsize)))%Z ->
      jac_eq (fromPoint (groupMul (unsignedToNat n) p))
      (seqToProd (fiat_point_mul (prodToSeq (fromPoint p)) n)).

    intros.
    eapply jac_eq_trans; [idtac | eapply fiat_point_mul_signedRegular_equiv].
    unfold groupMul.
    eapply jacobian_eq_jac_eq.

    specialize (@groupMul_signedRegular_table_correct point jac_eq_setoid Jacobian.add Jacobian.Proper_add jac_add_assoc).
    intros.  
    rewrite H0.
    reflexivity.

    apply jac_add_comm.
    apply jac_add_id_l.
    apply Jacobian.Proper_double.
    apply jac_double_correct.
    apply Proper_opp.
    apply jac_opp_correct.
    apply jac_opp_add_distr.
    apply jac_opp_involutive.
    apply wsize_nz.
    apply numWindows_nz.
    trivial.

  Qed.

  Print Assumptions point_mul_correct.

*)



  (* If we want to prove that the generic multiplication operation is correct, we need a group on generic points. *)
  (* probably sufficient to prove the fiat representation multiplcation operation is correct *)

(*

  Definition fiat_point_mul_generic := fiat_point_mul_generic Fsquare Fmul Fadd Fsub Fopp min_l fiat_from_bytes fiat_to_bytes.

  Definition GenericPoint := (seq 384 Bool * (seq 384 Bool * seq 384 Bool))%type.

  Theorem point_mul_generic_correct : forall (p : GenericPoint) (n : seq 384 Bool),
      jac_eq (fromPoint (groupMul (unsignedToNat n) p))
      (seqToProd (fiat_point_mul_generic (prodToSeq (fromPoint p)) n)).
  Qed.

  *)

End ECEqProof.
