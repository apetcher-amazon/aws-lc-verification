From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import BinPos.
From Coq Require Import Ring.
From Coq Require Import Setoid.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import Lia.


From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

From CryptolToCoq Require Import SAWCoreBitvectors.

From Bits Require Import operations.
From Bits Require Import operations.properties.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.

From Crypto Require Import Curves.Weierstrass.Jacobian.


From Top Require Import GroupMulWNAF.
From Top Require Import Zfacts.
From Top Require Import EC_fiat_P384_7.
From Top Require Import EC_fiat_P384_gen.

Set Implicit Arguments.

Theorem bvToNat_toZ_equiv : forall n x,
  (BinInt.Z.of_nat (bvToNat n x)) = bvToInt n x.
Admitted.

Theorem sbvToInt_bvToInt_id : forall n x,
  intToBv n (sbvToInt n x) = x.
Admitted.

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

Require Import CryptolToCoq.SAWCoreVectorsAsCoqVectors.

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
    
      unfold fiat_point_add_jac, fromPoint, fiat_point_add, EC_fiat_P384_gen.fiat_point_add, EC_fiat_P384_7.fiat_point_add, ecNotEq, ecEq, ecZero, ecAnd, ecOr, ecCompl, fiat_field_cmovznz; simpl.
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

    (*
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
  *)

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

(*
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
*)

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

  Theorem toN_int_excl_length : forall n, 
    List.length (toN_excl_int n) = n.

    induction n; intuition idtac; simpl in *.

    rewrite app_length.
    rewrite IHn.
    simpl.
    lia.

  Qed.

  Theorem toN_int_length : forall n, 
    List.length (toN_int n) = (S n).

    intros.
    unfold toN_int.
    rewrite app_length.
    rewrite toN_int_excl_length.
    simpl.
    lia.

  Qed.


  Theorem scanl_fix_convert : forall (A1 A2 B1 B2: Type)
    (conva : A2 -> A1)(convb : B2 -> B1)
    (f1 : A1 -> A1)(f2 : A2 -> A2)
    (fb1 : A1 -> B1)(fb2 : A2 -> B2)
    (fc1 : A1 -> B1)(fc2 : A2 -> B2),
    (forall a, fb1 (conva a) = convb (fb2 a)) ->
    (forall a, (exists b, a = (f2 b)) -> fc1 (conva a) = convb (fc2 a)) ->
    (forall a, (exists b, a = (f2 b)) -> f1 (conva a) = conva (f2 a)) ->
    forall n a1 a2,
    (exists b, a2 = (f2 b)) ->
    a1 = (conva a2) ->
    List.Forall2 (fun b1 b2 => b1 = convb b2)
    (scanl_fix f1 fb1 fc1 n a1)
    (scanl_fix f2 fb2 fc2 n a2).

    induction n; intros; simpl in *; subst.
    econstructor.

    destruct n.
    econstructor.
    eauto.
    econstructor.
    eauto.
    econstructor.

    econstructor.
    eauto.
    eapply IHn.
    eauto.
    eauto.

  Qed.

  Theorem fiat_mul_scalar_rwnaf_odd_loop_body_gen_equiv : forall wsize z,
    recode_rwnaf_odd_scanl_fix_body wsize (bvToInt _ z) =
    (sbvToInt _ 
          (fst (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize z)),
    sbvToInt _ 
         (snd (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize z))).

    intros.
    

  Admitted.

  Theorem mod_drop_equiv : forall s1 m a,
    (Z.modulo (bvToInt _ a) (Z.shiftl 1 (Z.of_nat m))) =
    (bvToInt _ (drop Bool s1 m a)).
 
    intros.
    

  Admitted.


  Theorem bvToInt_sbvToInt_equiv : forall n v,
    n > 0 ->
    (bvToInt n v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
    (sbvToInt n v = bvToInt n v).

    intros.
    unfold sbvToInt, bvToInt, spec.toZ, spec.toPosZ.
    destruct n. lia.
    case_eq (spec.splitmsb (bvToBITS v)); intros.
    destruct b0.

  Admitted.

  Theorem shiftR_bvToInt_nonneg : 
    forall n s x,
    s > 0 ->
    (VectorDef.hd (shiftR (S n) bool false x s) = false).

  Admitted.

  Theorem fiat_mul_scalar_rwnaf_odd_loop_body_gen_snd_nonneg : 
    forall wsize x, 
      wsize > 0 ->
     (VectorDef.hd (snd (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize x)) = false).

    intros.
    unfold fiat_mul_scalar_rwnaf_odd_loop_body_gen.
    unfold snd, Datatypes.snd.
    apply shiftR_bvToInt_nonneg.
    lia.

  Qed.

  Fixpoint recode_rwnaf_odd_bv (wsize : nat)(nw : nat)(n : bitvector 384) :=
    match nw with
    | 0%nat => (drop _ 368 16 n) :: List.nil
    | S nw' =>
      let k_i := (bvSub _ (bvURem _ n (bvMul _ (bvNat _ 2) (shiftL _ _ false (bvNat _ 1%nat) wsize))) (shiftL _ _ false (bvNat _ 1%nat) wsize)) in
      let n' := (shiftR _ _ false (bvSub _ n k_i) wsize) in
      (drop _ 368 16 k_i) :: (recode_rwnaf_odd_bv wsize nw' n')
    end.


  Theorem bvToInt_drop_equiv : forall n1 n2 x,
    ((bvToInt _ x) < Z.pow 2 (Z.of_nat n2))%Z ->
    bvToInt _ (drop _ n1 n2 x) = bvToInt _ x.

  Admitted.

  Theorem sbvToInt_drop_equiv : forall n1 n2 x,
    n2 > 0 -> 
    (-(Z.pow 2 (Z.of_nat (pred n2))) <= (sbvToInt _ x) < Z.pow 2 (Z.of_nat (pred n2)))%Z ->
    sbvToInt _ (drop _ n1 n2 x) = sbvToInt _ x.

  Admitted.

  Theorem sbvToInt_bvSub_equiv : forall n v1 v2,
    n > 1 -> 
      (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v1) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
     (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v2) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
    sbvToInt _ (bvSub n v1 v2) = ((sbvToInt _ v1) - (sbvToInt _ v2))%Z.

  Admitted.

  Theorem bvToInt_intToBv_id : forall n v,
    bvToInt n (intToBv n v) = v.

  Admitted.

  Theorem sbvToInt_intToBv_id : forall n v,
    (-Z.pow 2 (Z.of_nat (pred n)) <= v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
    sbvToInt n (intToBv n v) = v.

  Admitted.

  Theorem sbvToInt_bvURem_equiv : forall n v1 v2,
    n > 0 ->
    (0 < bvToInt _ v2)%Z ->
    (bvToInt _ v2 <= Z.pow 2 (Z.of_nat (pred n)))%Z ->
    sbvToInt n (bvURem _ v1 v2) = Z.modulo (bvToInt _ v1) (bvToInt _ v2).

    intros.
    Local Transparent bvURem.
    unfold bvURem.
    destruct n. lia.
    rewrite bvToInt_sbvToInt_equiv.
    apply bvToInt_intToBv_id.
    trivial.
    rewrite bvToInt_intToBv_id.
    eapply Z.lt_le_trans.
    eapply Z.mod_pos_bound.
    trivial.
    trivial.
  Qed.

  Theorem bvToInt_drop_le : forall n1 n2 v,
    (bvToInt _ (drop _ n1 n2 v) <= bvToInt _ v)%Z.

  Admitted.

  Theorem bvMul_2_shiftl_equiv : forall n v,
    bvMul n (intToBv _ 2) v = shiftL _ _ false v 1.
  Admitted.

  Theorem shiftL_shiftL : forall (A : Type) n (b : A) v n1 n2,
    (shiftL n _ b (shiftL n _ b v n1) n2) = shiftL n _ b v (n1 + n2).
  Admitted.

  Theorem bvToInt_shiftL_1_equiv : forall n s,
    s < n ->
    bvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
    Z.shiftl 1 (Z.of_nat s).
  Admitted.

  Theorem sbvToInt_shiftL_1_equiv : forall n s,
    n > 0 ->
    s < pred n ->
    sbvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
    Z.shiftl 1 (Z.of_nat s).
  Admitted.

  Theorem bvToInt_bvSub_nonneg_equiv : forall n v1 v2,
    (bvToInt _ v2 <= bvToInt _ v1)%Z ->
    (bvToInt n (bvSub _ v1 v2)) =
    ((bvToInt _ v1) - (bvToInt _ v2))%Z.
  Admitted.

  Theorem bvToBITS_bitsToBv_id : forall n v,
    bvToBITS (@bitsToBv n v) = v.
  Admitted.

(*
  Theorem bvToInt_bvAdd_small_equiv : forall n v1 v2,
    (* (sbvToInt _ v2 <= bvToInt _ v1)%Z -> *)
    (0 <= (bvToInt _ v1) + (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
    (bvToInt n (bvAdd _ v1 v2)) =
    ((bvToInt _ v1) + (sbvToInt _ v2))%Z.

    induction v1; intros; simpl in *.
    rewrite bvAdd_id_l.
    admit.

    Local Transparent bvAdd operations.adcB.
    unfold bvAdd, addB, adcB.
    simpl.
    Search bvAdd.
    Search Vector.t O.

  Qed.
  *)

(*

  Theorem toPosZ_addB_tuple_equiv: forall n v1 v2 i1 i2,
    spec.toPosZ (addB (tuple.Tuple (n:=S n) (tval:=v1) i1) (tuple.Tuple (n:=S n) (tval:=v2) i2)) =
    (spec.toPosZ (tuple.Tuple (n:=S n) (tval:=v1) i1) + spec.toZ (tuple.Tuple (n:=S n) (tval:=v2) i2))%Z.


    induction n; intros.
    admit.

    destruct v1.
    admit.
    destruct v2.
    admit.
    simpl in *.

    Local Transparent bvAdd operations.adcB.
    unfold addB, adcB.
    simpl.

    unfold is_true, eqtype.eq_op in *.
    simpl in *.
    repeat rewrite ssrnat.eqn  in *.
    Search ssrnat.eqn.
    unfold ssrnat.eqn in *. simpl in *.

  Qed.

spec.toPosZ
  (addB (tuple.Tuple (n:=S n) (tval:=tval) i) (tuple.Tuple (n:=S n) (tval:=tval0) i0)) =
(spec.toPosZ (tuple.Tuple (n:=S n) (tval:=tval) i) +
 spec.toZ (tuple.Tuple (n:=S n) (tval:=tval0) i0))%Z
*)
(*
  Theorem toPosZ_addB_equiv: forall n v1 v2,
    (spec.toPosZ v1 + spec.toPosZ v2 < Z.pow 2 (Z.of_nat n))%Z ->
    @spec.toPosZ (S n) (addB v1 v2) =
    (spec.toPosZ v1 + spec.toPosZ v2)%Z.

    intros.
    

  Qed.
*)

  Theorem toZ_toPosZ_equiv : forall n (v : spec.BITS (S n)),
    (spec.toZ v mod 2 ^ Z.of_nat (S n) = spec.toPosZ v mod 2 ^ Z.of_nat (S n))%Z.
  Admitted.

  Theorem toPosZ_addB_equiv: forall n (v1 v2 : spec.BITS (S n)),
    (0 <= spec.toPosZ v1 + spec.toZ v2 < Z.pow 2 (Z.of_nat (S n)))%Z ->
    spec.toPosZ (addB v1 v2) =
    (spec.toPosZ v1 + spec.toZ v2)%Z.

    intros.
    erewrite <- (@Zdiv.Zmod_small (spec.toPosZ v1 + spec.toZ v2)); eauto.
    rewrite <- Zdiv.Zplus_mod_idemp_r.
    rewrite toZ_toPosZ_equiv.
    rewrite Zdiv.Zplus_mod_idemp_r.
   
    rewrite addB_def.
  Admitted.


  Theorem sbvToInt_bvNeg_equiv : forall n v,
    sbvToInt n (bvNeg _ v) = Z.opp (sbvToInt _ v).
  Admitted.

  Theorem bvToInt_bvAdd_small_equiv : forall n (v1 v2 : bitvector n),
    (* (sbvToInt _ v2 <= bvToInt _ v1)%Z -> *)
    (0 <= (bvToInt _ v1) + (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
    (bvToInt n (bvAdd _ v1 v2)) =
    ((bvToInt _ v1) + (sbvToInt _ v2))%Z.

    intros.
    unfold bvToInt, sbvToInt in *.
    destruct n.
    (* empty bit vectors *)
    admit.

    Local Transparent bvAdd operations.adcB.
    unfold bvAdd.
    rewrite bvToBITS_bitsToBv_id.
    apply toPosZ_addB_equiv.
    apply H.

  Admitted.

  

  Theorem bvToInt_bvSub_small_equiv : forall n v1 v2,
    (0 <= (bvToInt _ v1) - (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
    (bvToInt n (bvSub _ v1 v2)) =
    ((bvToInt _ v1) - (sbvToInt _ v2))%Z.

    intros.
    rewrite bvSub_eq_bvAdd_neg.
    rewrite <- Z.add_opp_r.
    rewrite bvToInt_bvAdd_small_equiv.
    rewrite sbvToInt_bvNeg_equiv.
    reflexivity.
    
    rewrite sbvToInt_bvNeg_equiv.
    rewrite Z.add_opp_r.
    trivial.
  Qed.

(*
  Theorem bvToInt_shiftL_1_pos : forall n s,
    s < n ->
    (0 < bvToInt n (shiftL _ _ false (intToBv _ 1) s))%Z.
  Admitted.

  Theorem bvToInt_shiftL_1_small : forall n s,
    s < n ->
    (bvToInt n (shiftL _ _ false (intToBv _ 1) s) <= Z.pow 2 (Z.of_nat s))%Z.
  Admitted.
*)
  Theorem bvToInt_shiftR_lt : forall n v s b,
    ((bvToInt n v) < (Z.pow 2 (Z.of_nat s + b)))%Z ->
    ((bvToInt n (shiftR _ _ false v s)) < Z.pow 2 b)%Z.

  Admitted.

  Local Opaque sbvToInt.

  Theorem pow_add_lt : forall k x a b : Z,
    ((2^x) * a < 2^k ->
    b < x ->
    0 <= x ->
    k >= x ->
    (2^x)*a + 2^b < 2^k)%Z.  

    intros.
    remember (k - x)%Z as y.
    assert (a0 <= 2^y - 1)%Z.
    assert (a0 < 2^y)%Z.
    eapply (@Z.mul_lt_mono_pos_l (2^x)).
    eapply Z.pow_pos_nonneg; lia.
    eapply Z.lt_le_trans; eauto.
    subst.  
    rewrite <- Z.pow_add_r.
    rewrite Zplus_minus.
    reflexivity.
    lia.
    lia.
  
    lia.
    eapply Z.le_lt_trans.
    eapply (@Z.add_le_mono_r (2 ^ x * a0)).
    eapply Z.mul_le_mono_nonneg_l.
    eapply Z.pow_nonneg; lia.
    eauto.
    eapply Z.lt_le_trans.
    eapply (@Z.add_lt_mono_l (2 ^ b0)).
    eapply Z.pow_lt_mono_r; eauto.
    lia.
    eauto.
    rewrite Z.mul_sub_distr_l.
    rewrite Z.mul_1_r.
    rewrite Z.sub_simpl_r.
    subst.
    rewrite <- Z.pow_add_r.
    rewrite Zplus_minus.
    reflexivity.
    trivial.
    lia.

  Qed.


  Theorem sub_window_lt : forall n w k,
    (Z.of_nat (w + 1) <= k)%Z ->
    (0 <= n < 2^k)%Z ->
    ((n - (n mod 2 ^ Z.of_nat (w + 1) - 2^Z.of_nat w)) < 2^k)%Z.

    intros.
    rewrite Z.sub_sub_distr.
    assert (n = (2^Z.of_nat (w + 1) * (n / (2^Z.of_nat (w + 1) )) + n mod (2^Z.of_nat (w + 1) )))%Z.
    apply Z.div_mod.
    assert (0 < 2 ^ Z.of_nat (w + 1))%Z.
    eapply Z.pow_pos_nonneg; lia.
    lia.
    rewrite H1 at 1.
    rewrite <- Z.add_sub_assoc.
    rewrite Zminus_diag.
    rewrite Z.add_0_r.

    apply pow_add_lt.
    eapply Z.le_lt_trans; [idtac | apply H0].
    apply Z.mul_div_le.
    eapply Z.pow_pos_nonneg; lia.
    lia.
    lia.
    lia.

  Qed.
  
  Theorem bvToInt_nonneg : forall n v,
    (0 <= bvToInt n v)%Z.
  Admitted.

  Theorem recode_rwnaf_odd_bv_equiv : 
    forall wsize nw n,
    0 < wsize < 16 -> 
    (bvToInt _ n < (Z.pow 2 (Z.of_nat ((S nw) * wsize))))%Z -> 
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = (sbvToInt _ y)) 
    (recode_rwnaf_odd wsize nw (bvToInt _ n)) 
    (recode_rwnaf_odd_bv wsize nw n).


    induction nw; intros.
    econstructor.
    rewrite bvToInt_sbvToInt_equiv.
    rewrite bvToInt_drop_equiv.
    reflexivity.
    eapply Z.lt_le_trans.
    eauto.
    apply Z.pow_le_mono_r.
    lia.
    lia.
    lia.
    eapply Z.le_lt_trans.
    apply bvToInt_drop_le.
    eapply Z.lt_le_trans.
    apply H0.
    apply Z.pow_le_mono_r.
    lia.
    simpl.
    lia.
    econstructor.

    simpl.

    (* the calulcated window value actually fits in a window*)
    assert ((- 2 ^ Z.of_nat wsize <=
     sbvToInt (addNat 368%nat 16%nat)
       (bvSub 384
          (bvURem 384 n
             (shiftL 384 bool false (intToBv 384%nat 1) (wsize + 1)))
          (shiftL 384 bool false (intToBv 384%nat 1) wsize)) <
     2 ^ Z.of_nat wsize)%Z).
    admit.

    match goal with
    | [|- List.Forall2 _ (?a :: _) (?b :: _)] =>
    assert (a = sbvToInt _ b)
    end.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    unfold twoToWsize.
    rewrite Zdouble_shiftl.
    rewrite sbvToInt_drop_equiv; try lia.
    rewrite sbvToInt_bvSub_equiv; try lia.
    f_equal.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    f_equal.
    rewrite Znat.Nat2Z.inj_add.
    reflexivity.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_shiftL_1_equiv; simpl; lia.

    intros.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    apply Z.mod_pos_bound.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_bvURem_equiv; try lia.
    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_pos_nonneg; lia.

    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r; simpl; lia.

    rewrite sbvToInt_shiftL_1_equiv; try lia.
    rewrite Z.shiftl_1_l.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    apply Z.pow_nonneg; lia.
    apply Z.pow_nonneg; lia.
    apply Z.pow_lt_mono_r; simpl; lia.
    simpl; lia.

    split.
    eapply Z.le_trans; [idtac | apply H1].
    apply (@Z.opp_le_mono (2 ^ Z.of_nat wsize)).
    apply Z.pow_le_mono_r; simpl; lia.
    eapply Z.lt_le_trans.
    apply H1.
    apply Z.pow_le_mono_r; simpl; lia.

    lia.

    econstructor; eauto.

    match goal with
    | [|- List.Forall2 _ 
      (recode_rwnaf_odd _ _ ?a) (recode_rwnaf_odd_bv _ _ ?b)
    ] =>
    assert (a = (bvToInt _ b))
    end.

    admit.

    rewrite H3.
    eapply IHnw.
    lia.
    apply bvToInt_shiftR_lt.

    rewrite bvToInt_bvSub_small_equiv.

    rewrite sbvToInt_bvSub_equiv; try lia.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite sbvToInt_shiftL_1_equiv; try lia.
    repeat rewrite Z.shiftl_1_l.
    replace (2 ^ (Z.of_nat wsize + Z.of_nat (S nw * wsize)))%Z with (2 ^ Z.of_nat (S (S nw) * wsize))%Z.
    apply sub_window_lt.
    lia.
    split.
    apply bvToInt_nonneg.
    eauto.
    simpl.
    lia.
    simpl. lia.
  (* 2 * 2 ^wsize is positive *)
    admit.
    (* 2 * 2^wsize < 2^384 *)
    admit.

    rewrite sbvToInt_bvURem_equiv; try lia.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    admit.

    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    admit.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono; simpl; lia.
    lia.

    (* 2 * 2 ^wsize is positive *)
    admit.

    (* 2 * 2^wsize < 2^384 *)
    admit.


    rewrite bvToInt_sbvToInt_equiv.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_nonneg; simpl; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.
    lia.

    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.

    (* by a similar argument to the one above, the difference fits in the original bit width. *)
    rewrite sbvToInt_bvSub_equiv; try lia.
    rewrite sbvToInt_bvURem_equiv; try lia.
    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv; try lia.
    rewrite sbvToInt_shiftL_1_equiv; try lia.
    repeat rewrite Z.shiftl_1_l.
    split.
    apply Zorder.Zle_minus_le_0.
    rewrite <- (@Z.sub_0_r (bvToInt 384%nat n)).
    apply Z.sub_le_mono.
    rewrite Z.sub_0_r.
    apply Z.mod_le.
    apply bvToInt_nonneg.
    apply Z.pow_pos_nonneg; simpl; lia.
    apply Z.pow_nonneg; simpl; lia.
    apply sub_window_lt.
    lia.
    split.
    apply bvToInt_nonneg.
    eauto.

    (* integers from 384 bit vectors are less than 2^384 *)
    admit.

    simpl.
    lia.
  (* 2 * 2 ^wsize is positive *)
    admit.
    (* 2 * 2^wsize < 2^384 *)
    admit.

    rewrite sbvToInt_bvURem_equiv; try lia.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    admit.

    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    (* 2 * 2 ^wsize is positive *)
    admit.

    rewrite bvMul_2_shiftl_equiv.
    rewrite shiftL_shiftL.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_le_mono; simpl; lia.
    lia.

    (* 2 * 2 ^wsize is positive *)
    admit.

    (* 2 * 2^wsize < 2^384 *)
    admit.

    rewrite bvToInt_sbvToInt_equiv.
    split.
    eapply Z.le_trans.
    apply Z.opp_nonpos_nonneg.
    eapply Z.pow_nonneg; simpl; lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_nonneg; simpl; lia.
    lia.
    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.
    lia.

    rewrite bvToInt_shiftL_1_equiv.
    rewrite Z.shiftl_1_l.
    eapply Z.pow_lt_mono_r; simpl; lia.
    lia.
  Admitted.


 Definition recode_rwnaf_odd_bv_scanl_fix_body wsize n :=
      let k_i := (bvSub _ (bvURem _ n (bvMul _ (bvNat _ 2) (shiftL _ _ false (bvNat _ 1%nat) wsize))) (shiftL _ _ false (bvNat _ 1%nat) wsize)) in
      let n' := (shiftR _ _ false (bvSub _ n k_i) wsize) in
      ((drop _ 368 16 k_i), n').

  Theorem recode_rwnaf_odd_bv_scanl_equiv : forall wsize nw n,
    nw > 0 ->
    recode_rwnaf_odd_bv wsize nw n = 
    scanl_fix 
      (fun p => recode_rwnaf_odd_bv_scanl_fix_body wsize (snd p))
      (fun p => fst p)
      (fun p => (drop _ 368 16 (snd p)))
      nw (recode_rwnaf_odd_bv_scanl_fix_body wsize n).

    induction nw; intros.
    lia.
    unfold recode_rwnaf_odd_bv.
    fold recode_rwnaf_odd_bv.
    unfold scanl_fix.
    fold scanl_fix.
    destruct nw.
    reflexivity.

    f_equal.
    eapply IHnw.
    lia.

  Qed.

  Theorem forall2_symm : forall (A B : Type)(P : B -> A -> Prop) lsa lsb,
    List.Forall2 (fun a b => P b a) lsa lsb ->
    List.Forall2 P lsb lsa.
  
    induction 1; intros;
    econstructor; eauto.

  Qed.

  Theorem forall2_trans : forall ( A B C : Type)(R1 : A -> B -> Prop)(R2 : B -> C -> Prop)(R3 : A -> C -> Prop)
    lsa lsb lsc,
    List.Forall2 R1 lsa lsb ->
    (forall a b c, R1 a b -> R2 b c -> R3 a c) ->
    List.Forall2 R2 lsb lsc ->
    List.Forall2 R3 lsa lsc.

    induction lsa; intuition; simpl in *.
    inversion H; subst.
    inversion H1; subst.
    econstructor.

    inversion H; subst.
    inversion H1; subst.
    econstructor.
    eauto.
    eapply IHlsa; eauto.

  Qed.

  Theorem forall2_eq : forall (A : Type)(ls1 ls2 : list A),
    ls1 = ls2 ->
    List.Forall2 eq ls1 ls2.

    induction ls1; intros; simpl in *; subst.
    econstructor.

    econstructor; trivial.
    eauto.

  Qed.

  Theorem forall2_map_eq : forall (A B : Type)(f : B -> A) lsa lsb,
    List.Forall2 (fun a b => a = f b) lsa lsb ->
    lsa = List.map f lsb.

    induction 1; intros; simpl in *; trivial.
    congruence.

  Qed.

  Theorem recode_rwnaf_odd_bv_scanl_fix_body_fiat_equiv : forall wsize z, 
    recode_rwnaf_odd_bv_scanl_fix_body wsize z = 
    fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize z.

    intros. 
    unfold recode_rwnaf_odd_bv_scanl_fix_body.
    unfold fiat_mul_scalar_rwnaf_odd_loop_body_gen.
    reflexivity.

  Qed.

  Theorem fiat_mul_scalar_rwnaf_odd_gen_equiv : forall nw wsize z,
    0 < wsize < 16 ->
    (bvToInt 384%nat z < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    List.Forall2 (fun (x : Z) (y : bitvector 16) => x = (sbvToInt _ y))
  (recode_rwnaf_odd wsize (S (S nw)) (bvToInt _ z))
  (fiat_mul_scalar_rwnaf_odd_gen wsize nw z).

    intros.
    eapply (@forall2_trans  _ _ _ _ (eq)).
    apply (recode_rwnaf_odd_bv_equiv).
    lia.
    lia.
    intros; subst.
    trivial.
    apply forall2_eq.

    unfold fiat_mul_scalar_rwnaf_odd_gen.
  
    rewrite (@scanl_fix_equiv (bitvector 16 * bitvector 384) Integer (bitvector 16) (inhabitant
            (Inhabited_prod (bitvector 16)
               (bitvector 384)))
      (fun p =>
         fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize (snd p))
      (toN_int nw)
      (S nw)
      (fun (p : bitvector 16 * bitvector 384) => fst p) 
      (fun p => drop _ 368 16 (snd p))
      (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize z)); intros.

    rewrite recode_rwnaf_odd_bv_scanl_equiv.
    reflexivity.
    lia.

    apply toN_int_length.
    
  Qed.

  Theorem bvOr_bvToInt_equiv : forall n x y,
    bvToInt n (bvOr n x y) =
    BinInt.Z.lor (bvToInt n x) (bvToInt n y).
  Admitted.

  Theorem fiat_mul_scalar_rwnaf_gen_equiv : forall nw wsize z,
    0 < wsize < 16 ->
    (bvToInt 384%nat z < 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z ->
    List.Forall2 (fun x (y : bitvector 16) => x = (sbvToInt _ y))
    (recode_rwnaf wsize (S (S (S nw))) (bvToInt _ z)) 
    (fiat_mul_scalar_rwnaf_gen wsize nw z).

    intros. 
    unfold recode_rwnaf, fiat_mul_scalar_rwnaf_gen.
    replace (BinInt.Z.lor (bvToInt 384 z) 1) with
      (bvToInt _ (bvOr 384 z (intToBv 384 1))).
    apply fiat_mul_scalar_rwnaf_odd_gen_equiv.
    lia.
    rewrite bvOr_bvToInt_equiv.
    rewrite bvToInt_intToBv_id.
    case_eq (BinInt.Z.odd (bvToInt 384%nat z)); intros.
    rewrite Z_odd_lor_1; eauto.
    rewrite Z_even_lor_1.

    assert (Z.even (2 ^ Z.of_nat (S (S (S nw)) * wsize)) = true)%Z.
    rewrite Z.even_pow.
    trivial.
    lia.
    assert (Z.odd (BinInt.Z.succ (bvToInt 384%nat z)) = true).
    rewrite Z.odd_succ.
    rewrite Zeven.Zeven_odd_bool.
    rewrite H1.
    trivial.
    assert (BinInt.Z.succ (bvToInt 384%nat z) <> 2 ^ Z.of_nat (S (S (S nw)) * wsize))%Z.
    intuition idtac.
    rewrite H4 in H3.
    rewrite <- Z.negb_even in H3.
    rewrite Z.even_pow in H3.
    simpl in *.
    discriminate.
    lia.
    lia.
    rewrite <- Z.negb_odd.
    rewrite H1.
    trivial.
    rewrite bvOr_bvToInt_equiv.
    rewrite bvToInt_intToBv_id.
    reflexivity.

  Qed.

(*
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
*)

  Theorem Proper_opp : Proper (Jacobian.eq ==> Jacobian.eq) (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b F_Field Feq_dec).
  Admitted.

  Definition conditional_subtract_if_even_ct := conditional_subtract_if_even_ct Fsquare Fadd Fsub Fmul Fopp.

  Definition fiat_point_opp p :=
    let '(x, y, z) := seqToProd p in
    prodToSeq (x, Fopp y, z).

  Theorem conditional_subtract_if_even_ct_jac_eq_ite : forall n p1 p2,
    jac_eq (seqToProd (EC_fiat_P384_7.conditional_subtract_if_even_ct Fsquare Fmul Fsub Fadd
        Fopp p1 n p2)) (seqToProd (if (Nat.even (bvToNat _ n)) then (fiat_point_add false p1 (fiat_point_opp p2)) else p1)).
  Admitted.

(*
  Theorem groupMul_signedWindows_equiv: forall n t1 t2,
    List.Forall2 (fun x y => jac_eq (fromPoint x) (seqToProd y)) t1 (seqToList t2) ->
    jac_eq
  (fromPoint
     (groupMul_signedWindows Jacobian.add zero_point
        Jacobian.double wsize
        (groupMul_signed_table zero_point Jacobian.opp
           t1)
        (recode_rwnaf wsize numWindows (bvToInt _ n))))
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

  Admitted.
  *)

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

  Theorem fold_left_unroll_one : forall (A B : Type) def (f : A -> B -> A) (ls : list B) a,
    (List.length ls > 0)%nat ->
    List.fold_left f ls a = List.fold_left f (List.tl ls) (f a (List.hd def ls)).

    destruct ls; intros; simpl in *.
    lia.
    reflexivity.

  Qed.

  Theorem fold_left_R : forall (A1 A2 B1 B2 : Type)(RA : A1 -> A2 -> Prop)(RB : B1 -> B2 -> Prop)(f1 : A1 -> B1 -> A1)(f2: A2 -> B2 -> A2) ls1 ls2 a1 a2,
    RA a1 a2 ->
    List.Forall2 RB ls1 ls2 ->
    (forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> RA (f1 a1 b1) (f2 a2 b2)) ->
    RA (List.fold_left f1 ls1 a1) (List.fold_left f2 ls2 a2).

    induction ls1; destruct ls2; intros; simpl in *; trivial.
    inversion H0.
    inversion H0.
    inversion H0; subst; clear H0.
    eapply IHls1.
    eapply H1; eauto.
    trivial.
    eauto.

  Qed.


  Theorem fiat_selext_point_ct_gen_nth_equiv_h : forall ls n a,
    List.fold_left
      (fun (acc : seq 3 (seq 6 (seq 64 Bool)))
         (p : seq 64 Bool * seq 3 (seq 6 (seq 64 Bool))) =>
       fiat_select_point_loop_body (bvNat 64 (a + n)%nat) acc (fst p) (snd p))
      (combine (List.map (bvAdd _ (bvNat _ a)) (toN_excl_bv 64 (Datatypes.length ls))) ls)
      (of_list [zero_felem; zero_felem; zero_felem]) =
    List.nth n ls (cons F 0 2 (cons F 0 1 (cons F 0 0 (nil F)))).

    induction ls; intros; simpl in *.
    destruct n; reflexivity.

    destruct n.
    

  Abort.

  Theorem fiat_select_point_ct_gen_nth_equiv : forall x ls,
    fiat_select_point_ct_gen x ls = List.nth (bvToNat _ x) ls (cons _ Fzero _ (cons _ Fzero _ (cons _ Fzero _ (nil _)))).

    unfold fiat_select_point_ct_gen.

    (* apply fiat_selext_point_ct_gen_nth_equiv_h. *)
  Admitted.

  Theorem bvSShr_intToBv_equiv : forall n z v,
    bvSShr _ (intToBv (S n) z) v = intToBv (S n) (Z.shiftr z (Z.of_nat v)).
  Admitted.

  Theorem sign_extend_16_64_intToBv_equiv : forall z,
    sign_extend_16_64 (intToBv 16 z) = intToBv 64 z.
  Admitted.

  Theorem hd_rev_eq_last : forall (A : Type)(ls : list A)(def : A),
    List.hd def (List.rev ls) = List.last ls def.
  
    induction ls using rev_ind; intros; simpl in *; trivial.
    rewrite rev_unit.
    simpl.
    rewrite last_last.
    reflexivity.
  Qed.

  Theorem groupDouble_n_zero : forall n,
    groupDouble_n Jacobian.double n zero_point == zero_point.

    induction n; intros; simpl in *.
    reflexivity.
    transitivity (Jacobian.double zero_point).
    eapply Jacobian.Proper_double.
    eauto.
    rewrite jac_double_correct.
    rewrite jac_add_id_l.
    reflexivity.
  Qed.

  Theorem recode_rwnaf_odd_length : forall w nw z,
    List.length (recode_rwnaf_odd w nw z) = (S nw).

    induction nw; intros; simpl in *; trivial.
    rewrite IHnw.
    trivial.

  Qed.

  Theorem recode_rwnaf_length : forall w nw z,
    nw <> 0%nat -> 
    List.length (recode_rwnaf w nw z) = nw.

    intros.
    destruct nw.
    lia.
    apply recode_rwnaf_odd_length.

  Qed.

  Theorem fold_left_scanl_app_equiv : forall (A B : Type) (f : A -> B -> A) ls def a1 a2,
    a2 <> List.nil ->
    List.fold_left
  (fun (x : list A) (y : B) =>
   x ++ [f (List.last x def) y]) ls 
  (List.cons a1 a2) =
    a1 :: (List.fold_left (fun (x : list A) (y : B) =>
   x ++ [f (List.last x def) y]) ls 
  a2 ).

    induction ls; intros; simpl in *; trivial.
    rewrite (@IHls _ a1).
    destruct a2.
    intuition idtac.
    reflexivity.
    f_equal.
    intuition idtac.
    apply app_eq_nil in H0.
    intuition idtac.

  Qed.

  Theorem fold_left_scanl_equiv : forall (A B : Type) def (f : A -> B -> A) ls a,
    List.fold_left (fun x y => x ++ (f (List.last x def) y)::List.nil) ls [a] = 
    EC_fiat_P384_gen.scanl f ls a.

    induction ls; intros; simpl in *; trivial.
    rewrite <- IHls.
    rewrite fold_left_scanl_app_equiv.
    reflexivity.
    congruence.
  Qed.

  Definition fiat_pre_comp_table_gen := fiat_pre_comp_table_gen Fsquare Fmul Fsub Fadd.

  Theorem Forall2_scanl : forall (A1 A2 B1 B2 : Type)(PA : A1 -> A2 -> Prop)(PB : B1 -> B2 -> Prop)
    (f1 : A1 -> B1 -> A1)(f2 : A2 -> B2 -> A2) ls1 ls2 a1 a2,
    List.Forall2 PB ls1 ls2 ->
    (forall a1 a2 b1 b2, PA a1 a2 -> PB b1 b2 -> PA (f1 a1 b1) (f2 a2 b2)) ->
    PA a1 a2 ->
    List.Forall2 PA (EC_fiat_P384_gen.scanl f1 ls1 a1) (EC_fiat_P384_gen.scanl f2 ls2 a2).

    induction ls1; destruct ls2; simpl in *; intros.
    econstructor; eauto.
    inversion H.
    inversion H.
    inversion H; clear H; subst.
    econstructor; eauto.

  Qed.

  (* Not sure if this is true, but we could always add more assumptions that triples are Jacobian*)
  Theorem jac_eq_point_ex : forall p1 p2,
    jac_eq (fromPoint p1) p2 ->
    exists p2', p2 = fromPoint p2'.

    intros.
    unfold jac_eq in *.
    remember (fromPoint p1) as z. destruct z. destruct p.
    destruct p2. destruct p.

    assert ((fun '(X, Y, Z) =>  if dec (Feq Z Fzero)
                          then True
                          else
                           Feq (Fmul Y Y)
                             (Fadd
                                (Fadd (Fmul (Fmul X X) X)
                                   (Fmul (Fmul a X)
                                      (Fmul (Fmul Z Z) (Fmul Z Z))))
                                (Fmul b
                                   (Fmul (Fmul (Fmul Z Z) Z)
                                      (Fmul (Fmul Z Z) Z))))) (f3, f4, f2)).
    destruct (dec (Feq f 0)).
    rewrite H.
    destruct (dec (Feq 0 0)).
    trivial.
    exfalso.
    apply n.
    reflexivity.
    intuition idtac.
    destruct (dec (Feq f2 0)).
    trivial.
    admit.
 
    exists (exist _ _ H0).
    reflexivity.
  Admitted.

  Theorem jac_eq_jacobian_eq: forall p1 p2,
    jac_eq (fromPoint p1) (fromPoint p2) ->
    Jacobian.eq p1 p2.

    intros. 
    unfold jac_eq, Jacobian.eq, fromPoint in *.
    eauto.
  Qed.

  Theorem Forall2_I : forall (A B : Type)(ls1 : list A)(ls2 : list B),
    List.length ls1 = List.length ls2 ->
    List.Forall2 (fun a b => True) ls1 ls2.

    induction ls1; destruct ls2; intros; simpl in *; try lia.
    econstructor.
    econstructor; eauto; econstructor.

  Qed.

  Theorem preCompTable_equiv_h : forall ls1 ls2 p1 p2,
    List.length ls1 = List.length ls2 ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    List.Forall2
  (fun (a0 : point) (b0 : seq 3 F) =>
   jac_eq (fromPoint a0) (seqToProd b0))
  (EC_fiat_P384_gen.scanl
     (fun (a0 : Jacobian.point) (_ : nat) =>
      Jacobian.add (Jacobian.double p1) a0)
     ls1 p1)
  (EC_fiat_P384_gen.scanl
     (fun (z : seq 3 (seq 6 (seq 64 Bool)))
        (_ : Integer) =>
      EC_fiat_P384_7.fiat_point_add Fsquare Fmul
        Fsub Fadd
        (ecNumber 0%nat Bool PLiteralBit)
        (EC_fiat_P384_7.fiat_point_double Fsquare
           Fmul Fsub Fadd
           p2) z)
     ls2 p2).

    intros.
    eapply (@Forall2_scanl _ _ _ _ _ (fun x y => True)); intros.
    eapply Forall2_I; eauto.
    eapply point_add_jac_eq.

    assert (exists p2', p2 = prodToSeq (fromPoint p2')).
    apply jac_eq_point_ex in H0.
    destruct H0.
    exists x.
    rewrite <- H0.
    rewrite prodToSeq_inv.
    reflexivity.

    destruct H3.
    subst.
    rewrite <- double_eq_minus_3.
    rewrite seqToProd_inv in H0.
    rewrite seqToProd_inv.
    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply Jacobian.Proper_double.
    eapply jac_eq_jacobian_eq.
    eauto.
    apply Jacobian.double_minus_3_eq_double.
    trivial.
    trivial.
  Qed.

  Theorem forNats_length : forall n,
    List.length (forNats n) = n.

    induction n; intros; simpl in *; trivial.
    congruence.

  Qed.

  Theorem preCompTable_equiv : forall w p,
    (tableSize w) > 1 ->
    List.Forall2 (fun a b => jac_eq (fromPoint a) (seqToProd b))
      (preCompTable Jacobian.add zero_point Jacobian.double w p)
      (fiat_pre_comp_table_gen (Nat.pred (Nat.pred (tableSize w))) (prodToSeq (fromPoint p))).

    intros.
    unfold preCompTable, preCompTable_h, fiat_pre_comp_table_gen, EC_fiat_P384_gen.fiat_pre_comp_table_gen.
    rewrite (@fold_left_scanl_equiv _ _ _ (fun a b => (Jacobian.add (Jacobian.double p) a))).
    eapply preCompTable_equiv_h.
    rewrite forNats_length.
    rewrite map_length.
    rewrite toN_int_length.
    lia.
    rewrite seqToProd_inv.
    eapply jac_eq_refl.
  Qed.



  Theorem Forall2_nth : forall (A B : Type)(P : A -> B -> Prop) lsa lsb,
    List.Forall2 P lsa lsb ->
    forall n defA defB,
    P defA defB ->
    P (List.nth n lsa defA) (List.nth n lsb defB).

    induction 1; intros; simpl in *.
    destruct n; trivial.
    destruct n; trivial.
    eapply IHForall2; trivial.

  Qed.

  Theorem bvNat_Z_to_nat_eq_intToBv : forall n (z : Z),
    (0 <= z)%Z ->
    bvNat n (Z.to_nat z) = intToBv n z.
  Admitted.

  Theorem skipn_1_eq_tl : forall (A : Type)(ls : list A),
    skipn 1 ls = List.tl ls.

    intros.
    destruct ls; trivial.

  Qed.

  Theorem Forall2_tl : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
    List.Forall2 P ls1 ls2 ->
    List.Forall2 P (List.tl ls1) (List.tl ls2).

    intros.
    inversion H; clear H; subst;
    simpl.
    econstructor.
    trivial.

  Qed.

  Theorem Forall2_rev : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
    List.Forall2 P ls1 ls2 ->
    List.Forall2 P (List.rev ls1) (List.rev ls2).
  
    induction 1; intros; simpl in *.
    econstructor.
    eapply Forall2_app.
    eauto.
    econstructor.
    trivial.  
    econstructor.

  Qed.

  Theorem ct_abs_equiv : forall wsize b1 b2,
    b1 = sbvToInt 16 b2 ->
    sbvToInt 16 (bvAdd 16
                       (bvXor 16 b2
                          (bvNeg 16
                             (bvAnd 16
                                (shiftR 16 bool
                                 false b2 wsize)
                                (bvNat 16 1%nat))))
                       (bvAnd 16
                          (shiftR 16 bool false b2
                             wsize) (bvNat 16 1%nat)))
    =
    Z.abs b1.
  Admitted.

  Theorem groupDouble_n_double_comm : forall n (a1 : point),
    Jacobian.eq
  (Jacobian.double (groupDouble_n Jacobian.double n a1))
  (groupDouble_n Jacobian.double n (Jacobian.double a1)).

    induction n; intros; simpl in *.
    reflexivity.
    apply Jacobian.Proper_double.
    eapply IHn.
  
  Qed.


  Theorem groupDouble_n_fold_left_double_equiv : forall ws ls a1 a2,
    List.length ls = ws ->
    jac_eq (fromPoint a1) (seqToProd a2) ->
    jac_eq
  (fromPoint (groupDouble_n Jacobian.double ws a1))
  (seqToProd
     (List.fold_left
        (fun (x : seq 3 (seq 6 (seq 64 Bool))) (_ : Integer)
         =>
         EC_fiat_P384_7.fiat_point_double Fsquare Fmul Fsub
           Fadd x) ls a2)).

    induction ws; destruct ls; intros; simpl in *; try lia.
    trivial.
    eapply jac_eq_trans; [idtac | eapply IHws].
    apply jacobian_eq_jac_eq.
    eapply groupDouble_n_double_comm.
    lia.
    assert (exists a2', (seqToProd a2) = (fromPoint a2')).
    eapply jac_eq_point_ex; eauto.
    destruct H1. subst.
    replace a2 with (prodToSeq (fromPoint x)).
    rewrite <- double_eq_minus_3.
    rewrite seqToProd_inv.
    apply jacobian_eq_jac_eq.
    transitivity (Jacobian.double x).
    apply Jacobian.Proper_double.
    eapply jac_eq_jacobian_eq.
    eapply jac_eq_trans; eauto.
    eapply jac_eq_refl_gen.
    trivial.

    eapply Jacobian.double_minus_3_eq_double.
    rewrite <- H1.
    apply prodToSeq_inv.
 
  Qed.

  Theorem conditional_point_opp_equiv : forall x p1 p2,
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint (if (dec ((sbvToInt _ x) = 0%Z)) then p1 else (Jacobian.opp p1))).

  Admitted.

  Theorem conditional_point_opp_ifso_equiv : forall x p1 p2,
    sbvToInt _ x <> 0%Z ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint (Jacobian.opp p1)).

    intros.
    eapply jac_eq_trans.
    eapply conditional_point_opp_equiv; eauto.
    destruct (dec (sbvToInt 64 x = 0%Z)).
    congruence.
    apply jac_eq_refl.

  Qed.

  Theorem conditional_point_opp_ifnot_equiv : forall x p1 p2,
    sbvToInt _ x = 0%Z ->
    jac_eq (fromPoint p1) (seqToProd p2) ->
    jac_eq
  (seqToProd
     (conditional_point_opp Fopp x p2))
  (fromPoint p1).

    intros.
    eapply jac_eq_trans.
    eapply conditional_point_opp_equiv; eauto.
    destruct (dec (sbvToInt 64 x = 0%Z)).
    apply jac_eq_refl.
    congruence.

  Qed.
       
  Theorem bvToNat_Z_to_nat_equiv : forall n x z,
    (0 <= z)%Z ->
    sbvToInt n x = z ->
    bvToNat n x = Z.to_nat z.

  Admitted.

  Theorem sbvToInt_sign_extend_16_64_equiv : forall x,
    sbvToInt _ (sign_extend_16_64 x) = sbvToInt _ x.

  Admitted.

  Theorem bvSShr_Z_shiftr_equiv : forall n x1 x2 y1 y2,
    Z.of_nat y1 = y2 ->
    sbvToInt _ x1 = x2 ->
    sbvToInt _ (bvSShr n x1 y1) = Z.shiftr x2 y2.
  Admitted.

  Theorem mul_body_equiv : forall pred_wsize p a1 a2 b1 b2,
    jac_eq (fromPoint a1) (seqToProd a2) ->
    b1 = sbvToInt 16 b2 ->
    jac_eq
  (fromPoint
     (groupMul_signedWindows_fold_body Jacobian.add Jacobian.double
        (S pred_wsize)
        (fun x : Z =>
         if (x <? 0)%Z
         then
          Jacobian.opp
            (List.nth
               (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
               (preCompTable Jacobian.add zero_point Jacobian.double
                  (S pred_wsize) p) zero_point)
         else
          List.nth
            (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
            (preCompTable Jacobian.add zero_point Jacobian.double
               (S pred_wsize) p) zero_point) a1 b1))
  (seqToProd
     (fiat_double_add_body_gen Fsquare Fmul Fsub Fadd Fopp pred_wsize
        (EC_fiat_P384_gen.fiat_pre_comp_table_gen Fsquare Fmul Fsub
           Fadd (Nat.pred (Nat.pred (tableSize (S pred_wsize))))
           (prodToSeq (fromPoint p))) a2 b2)).

    intros.
    unfold fiat_double_add_body_gen.

    rewrite fiat_select_point_ct_gen_nth_equiv.
    unfold groupMul_signedWindows_fold_body.
    unfold groupAdd_signedWindow.
    match goal with
    | [|- context[if ?a then _ else _]] =>
      case_eq a; intros
    end.
    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply jac_add_comm.
    eapply point_add_jac_eq.
    eapply groupDouble_n_fold_left_double_equiv.
    apply toN_int_length.
    trivial.
    
    subst.
    apply Z.ltb_lt in H1.
    eapply jac_eq_symm.
    eapply conditional_point_opp_ifso_equiv.
    unfold point_id_to_limb.
    removeCoerce.
    simpl.
    
    (* probably need to add assumption that the integer is a window, so it is in the right range *)
    admit.

    match goal with
    | [|- jac_eq (fromPoint (List.nth ?a _ _)) (seqToProd (List.nth ?b _ _))] =>
      replace a with b
    end.
    eapply (@Forall2_nth _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    admit.
    (* need to use (0, 1, 0) *)
    admit.

    eapply bvToNat_Z_to_nat_equiv.
    apply Z.shiftr_nonneg.
    apply Z.abs_nonneg.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    apply bvSShr_Z_shiftr_equiv.
    trivial.
    apply ct_abs_equiv.
    trivial.

    eapply jac_eq_trans.
    apply jacobian_eq_jac_eq.
    apply jac_add_comm.
    eapply point_add_jac_eq.
    eapply groupDouble_n_fold_left_double_equiv.
    apply toN_int_length.
    trivial.
    
    subst.
    apply Z.ltb_ge in H1.
    eapply jac_eq_symm.
    eapply conditional_point_opp_ifnot_equiv.
    unfold point_id_to_limb.
    removeCoerce.
    simpl.
    
    (* probably need to add assumption that the integer is a window, so it is in the right range *)
    admit.

    match goal with
    | [|- jac_eq (fromPoint (List.nth ?a _ _)) (seqToProd (List.nth ?b _ _))] =>
      replace a with b
    end.
    eapply (@Forall2_nth _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    admit.
    (* need to use (0, 1, 0) *)
    admit.

    eapply bvToNat_Z_to_nat_equiv.
    apply Z.shiftr_nonneg.
    apply Z.abs_nonneg.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    apply bvSShr_Z_shiftr_equiv.
    trivial.
    apply ct_abs_equiv.
    trivial.
  Admitted.
   

  Theorem fiat_pre_comp_table_gen_nth_0  : forall wsize p def,
    List.nth 0 (EC_fiat_P384_gen.fiat_pre_comp_table_gen Fsquare Fmul
              Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
              p) def = p.

  Admitted.

  Theorem last_nth_equiv_gen
     : forall (A : Type) (def : A) (ls : list A) n,
      n = (Nat.pred (Datatypes.length ls)) ->
       List.last ls def =
       List.nth n ls
         def.

    intros. 
    subst.
    apply last_nth_equiv.

  Qed.


  Definition fiat_point_mul_gen := fiat_point_mul_gen Fsquare Fmul Fsub Fadd Fopp.

  Theorem fiat_point_mul_gen_signedRegular_cases : forall wsize numWindows n p,
    0 < wsize < 16 ->
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S numWindows)) * wsize)))%Z->
    jac_eq
  (seqToProd
     (List.fold_left
        (fiat_double_add_body_gen Fsquare Fmul Fsub Fadd Fopp (Nat.pred wsize)
           (EC_fiat_P384_gen.fiat_pre_comp_table_gen Fsquare Fmul
              Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
              (prodToSeq (fromPoint p))))
        (skipn 1
           (List.rev (fiat_mul_scalar_rwnaf_gen wsize numWindows n)))
        (fiat_select_point_ct_gen
           (sign_extend_16_64
              (bvSShr 15
                 (List.nth (S (S numWindows))
                    (fiat_mul_scalar_rwnaf_gen wsize numWindows n)
                    (bvNat 16 0%nat)) 1))
           (EC_fiat_P384_gen.fiat_pre_comp_table_gen Fsquare Fmul
              Fsub Fadd (Nat.pred (Nat.pred (tableSize wsize)))
              (prodToSeq (fromPoint p))))))
  (fromPoint
     (groupMul_signedWindows Jacobian.add zero_point Jacobian.double
        wsize
        (fun x : Z =>
         if (x <? 0)%Z
         then
          Jacobian.opp
            (List.nth
               (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
               (preCompTable Jacobian.add zero_point Jacobian.double
                  wsize p) zero_point)
         else
          List.nth
            (BinInt.Z.to_nat (BinInt.Z.shiftr (BinInt.Z.abs x) 1))
            (preCompTable Jacobian.add zero_point Jacobian.double
               wsize p) zero_point)
        (recode_rwnaf wsize (S (S (S numWindows)))
           (BinInt.Z.of_nat (bvToNat 384 n))))).

    intros.
    eapply jac_eq_symm.
    rewrite groupMul_signedWindows_fold_equiv.
    rewrite (@fold_left_unroll_one _ _ 0%Z).
    eapply (@fold_left_R _ _ _ _ 
      (fun a1 a2 => jac_eq (fromPoint a1) (seqToProd a2))
      (fun b1 b2 => b1 = sbvToInt 16 b2)
    ).
    erewrite (@forall2_map_eq _ _
      (intToBv 16)
      
      (fiat_mul_scalar_rwnaf_gen
                    wsize numWindows n)
      (recode_rwnaf wsize
                 (S (S (S numWindows)))
                 (BinInt.Z.of_nat
                    (bvToNat _ n)))
    ).
    replace (bvNat 16 0%nat) with (intToBv 16 0%Z).
    rewrite map_nth.
(*
    replace (sign_extend_16_64
           (bvSShr 15
              (intToBv 16
                 (List.nth (S (S numWindows))
                    (recode_rwnaf wsize (S (S (S numWindows)))
                       (BinInt.Z.of_nat (bvToNat 384 n))) 0%Z))
              1))
    with
    (bvNat 64 (Z.to_nat (Z.shiftr (List.nth (S (S numWindows))
                    (recode_rwnaf wsize (S (S (S numWindows)))
                       (BinInt.Z.of_nat (bvToNat 384 n))) 0%Z) 1))).
*)
    rewrite fiat_select_point_ct_gen_nth_equiv.
    unfold groupMul_signedWindows_fold_body.
    unfold groupAdd_signedWindow.
    match goal with
    | [|- context[if ?a then _ else _]] =>
      case_eq a; intros
    end.
    exfalso.
    apply Z.ltb_lt in H1.
    match goal with
    | [H: (?a < 0)%Z |- _] =>
      assert (0 <= a)%Z
    end.
    rewrite hd_rev_eq_last.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    lia.
    
    rewrite Z.abs_eq.

    eapply (@jac_eq_trans _ 
      (fromPoint (List.nth
           (BinInt.Z.to_nat
              (BinInt.Z.shiftr
                    (List.hd 0%Z
                       (List.rev
                          (recode_rwnaf wsize
                             (S (S (S numWindows)))
                             (BinInt.Z.of_nat (bvToNat 384 n)))))
                 1))
           (preCompTable Jacobian.add zero_point
              Jacobian.double wsize p) zero_point)
    )).
    eapply jacobian_eq_jac_eq.
    transitivity 
      (Jacobian.add
     (List.nth
        (BinInt.Z.to_nat
           (BinInt.Z.shiftr
                 (List.hd 0%Z
                    (List.rev
                       (recode_rwnaf wsize
                          (S (S (S numWindows)))
                          (BinInt.Z.of_nat (bvToNat 384 n)))))
              1))
        (preCompTable Jacobian.add zero_point Jacobian.double
           wsize p) zero_point)
     (zero_point)).
    
    eapply Jacobian.Proper_add. 
    reflexivity.
    apply (@groupDouble_n_zero wsize).
    rewrite jac_add_comm.
    apply jac_add_id_l.
    rewrite hd_rev_eq_last.
    rewrite last_nth_equiv.
    rewrite recode_rwnaf_length.
    match goal with 
    | [|- jac_eq (fromPoint (List.nth ?a _ _ )) (seqToProd (List.nth ?b _ _ ))] =>  
      replace a with b
    end.
    eapply (@Forall2_nth _ _ (fun a b => jac_eq (fromPoint a) (seqToProd b))).
    apply preCompTable_equiv.
    admit.
    (* need to use (0, 1, 0) *)
    admit.
  
    apply bvToNat_Z_to_nat_equiv.
    eapply Z.shiftr_nonneg.
    replace (List.nth (Nat.pred (S (S (S numWindows))))
   (recode_rwnaf wsize (S (S (S numWindows)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z
    with
    (List.last
   (recode_rwnaf wsize (S (S (S numWindows)))
      (BinInt.Z.of_nat (bvToNat 384%nat n))) 0)%Z.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    apply last_nth_equiv_gen.
    rewrite recode_rwnaf_length.
    trivial.
    lia.
    rewrite sbvToInt_sign_extend_16_64_equiv.
    apply bvSShr_Z_shiftr_equiv.
    trivial.
    
    apply sbvToInt_intToBv_id.
    (* valid windows *)
    admit.
    lia.

    rewrite hd_rev_eq_last.
    apply recode_rwnaf_last_nonneg.
    lia.
    lia.
    trivial.
    reflexivity.
    
    rewrite bvToNat_toZ_equiv.
    apply forall2_symm.
    eapply forall2_trans.
    apply fiat_mul_scalar_rwnaf_gen_equiv.
    lia.
    admit.
    intros.
    assert (b0 = c).
    eapply H2.
    subst.
    rewrite H1.
    rewrite sbvToInt_bvToInt_id.
    reflexivity.
    eapply forall2_eq.
    reflexivity.

    rewrite skipn_1_eq_tl.
    eapply Forall2_tl.
    eapply Forall2_rev.
    rewrite bvToNat_toZ_equiv.
    apply fiat_mul_scalar_rwnaf_gen_equiv.
    lia.
    admit.

    intros.  
    destruct wsize.
    lia.
    apply mul_body_equiv; trivial.

    rewrite rev_length.
    rewrite recode_rwnaf_length.
    lia.
    lia.

  Admitted.


  Theorem fiat_point_mul_gen_signedRegular_equiv : forall wsize numWindows n p,
    0 < wsize < 16 ->
    (BinInt.Z.of_nat (bvToNat 384%nat n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (S (S (S numWindows)) * wsize)))%Z->
    jac_eq
    (fromPoint
       (groupMul_signedRegular_table Jacobian.add zero_point
          Jacobian.double Jacobian.opp wsize (S (S (S numWindows))) p
          (bvToNat _ n)))
    (seqToProd
       (fiat_point_mul_gen wsize numWindows (Nat.pred (Nat.pred (tableSize wsize))) (prodToSeq (fromPoint p))
          n)).

    intros.
    unfold fiat_point_mul_gen.
    unfold groupMul_signedRegular_table, groupMul_signed_table.

    unfold groupMul_signedRegular, groupMul_signedRegularWindows.

    eapply jac_eq_symm.
    eapply jac_eq_trans.
    eapply conditional_subtract_if_even_ct_jac_eq_ite.

    case_eq (Nat.even (bvToNat _ n)); intros.

    eapply jac_eq_symm.
    eapply point_add_jac_eq.
    eapply jac_eq_symm.
    eapply fiat_point_mul_gen_signedRegular_cases.
    specialize (@fiat_point_mul_gen_signedRegular_cases wsize numWindows n p); intros; trivial.
    trivial.

    rewrite fiat_pre_comp_table_gen_nth_0.
    apply jac_eq_refl_gen.
    unfold fiat_point_opp, prodToSeq, seqToProd.
    simpl.
    destruct p. simpl. destruct x. destruct p. simpl.
    unfold nth_order. simpl.
    reflexivity.

    apply fiat_point_mul_gen_signedRegular_cases; trivial.

  Qed.
    
  Theorem point_mul_correct : forall (p : point) (n : seq 384 Bool),
      (BinInt.Z.of_nat (bvToNat _ n) <
 BinInt.Z.shiftl 1 (BinInt.Z.of_nat (55 * 7)))%Z ->
      jac_eq (fromPoint (groupMul (bvToNat _ n) p))
      (seqToProd (fiat_point_mul (prodToSeq (fromPoint p)) n)).

    intros.
    unfold fiat_point_mul.
    rewrite fiat_point_mul_gen_equiv.
    eapply jac_eq_trans; [idtac | eapply fiat_point_mul_gen_signedRegular_equiv].
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
    lia.
    lia.
    trivial.
    lia.
    trivial.

  Qed.




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

