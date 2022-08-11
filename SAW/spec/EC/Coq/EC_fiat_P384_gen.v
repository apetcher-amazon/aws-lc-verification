
Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Vectors.VectorSpec.
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

From Top Require Import EC_fiat_P384_7.


Definition append_comm (m n : Nat) (a : Type) (Inh_a : Inhabited a) 
  (x : Vec m a) (y : Vec n a) :=
gen (addNat n m) a
  (fun i : Nat =>
   if ltNat i m then sawAt m a x i else sawAt n a y (subNat i m)).


Local Arguments cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments append_comm [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.




Definition fiat_mul_scalar_rwnaf_odd_loop_body_gen (wsize : nat)(s : bitvector 384) :=
(drop Bool 368 16
   (bvSub
      (bvURem 384 s
         (bvMul 384 (bvNat 384 2)
            (shiftL 384 bool false (bvNat 384 1) wsize)))
      (shiftL 384 bool false (bvNat 384 1) wsize)),
shiftR 384 bool false
  (bvSub s
     (bvSub
        (bvURem 384 s
           (bvMul 384 (bvNat 384 2)
              (shiftL 384 bool false (bvNat 384 1) wsize)))
        (shiftL 384 bool false (bvNat 384 1) wsize))) wsize).

Ltac ecSimpl_one :=
  match goal with
    | [ |- context[ecNumber (TCNum ?a) ?t (PLiteralSeqBool (TCNum ?s))]] =>
        replace (ecNumber (TCNum a) t (PLiteralSeqBool (TCNum s))) with (bvNat s a); [idtac | reflexivity] 
    | [ |- context[ecNumber (TCNum ?a) ?t PLiteralInteger]] =>
        replace (ecNumber (TCNum a) t PLiteralInteger) with (Z.of_nat a); [idtac | reflexivity] 
    | [|- context[ecCat ?s1 ?s2 ?t ?a ?b]] =>
        replace (ecCat s1 s2 t a b) with (append a b); [idtac | reflexivity]
    | [|- context[map ?s ?t1 ?t2 ?f ?ls]] =>
        replace (map s t1 t2 f ls) with (SAWCorePrelude.map f _ ls); [idtac | reflexivity]
    | [ |- context[ecPlus Integer ?r (Z.of_nat ?a) (Z.of_nat ?b)]] =>
        replace (ecPlus Integer r (Z.of_nat a) (Z.of_nat b)) with (ecNumber (a + b) Integer PLiteralInteger); [idtac | reflexivity]
    | [ |- context[ecMinus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMinus t (PRingSeqBool s) a b) with (bvSub a b); [idtac | reflexivity]
    | [ |- context[ecPlus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecPlus t (PRingSeqBool s) a b) with (bvAdd a b); [idtac | reflexivity]
    | [ |- context[ecAnd ?t (PLogicSeqBool ?s) ?a ?b]] => 
        replace (ecAnd t (PLogicSeqBool s) a b) with (bvAnd a b); [idtac | reflexivity]
    | [ |- context[ecMul ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMul t (PRingSeqBool s) a b) with (bvMul _ a b); [idtac | reflexivity]
    | [ |- context[ecMod ?t (PIntegralSeqBool ?s) ?a ?b]] => 
        replace (ecMod t (PIntegralSeqBool s) a b) with (bvURem _ a b); [idtac | reflexivity]
    | [ |- context[ecDrop (TCNum ?s1) (TCNum ?s2) ?t ?a]] => 
        replace (ecDrop (TCNum s1) (TCNum s2) t a) with (drop _ s1 s2 a); [idtac | reflexivity]
    | [ |- context[ecShiftL ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftL s t Bool r PZeroBit a (Z.of_nat b)) with (shiftL _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s1 ?t Bool ?r PZeroBit ?a (bvNat ?s2 ?b)]] => 
        replace (ecShiftR s1 t Bool r PZeroBit a (bvNat s2 b)) with (shiftR _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftR s t Bool r PZeroBit a (Z.of_nat b)) with (shiftR _ _ false a b); [idtac | reflexivity]
  end.

Ltac removeCoerce :=
  match goal with
  | [ |- context[coerce ?t1 ?t2 ?p ?a]] => 
    replace (coerce t1 t2 p a) with a; [idtac | reflexivity]
  end.

Theorem fiat_mul_scalar_rwnaf_odd_loop_body_gen_equiv : forall s,
  fiat_mul_scalar_rwnaf_odd_loop_body_gen 7 s = fiat_mul_scalar_rwnaf_odd_loop_body s.

  intros.
  unfold fiat_mul_scalar_rwnaf_odd_loop_body, fiat_mul_scalar_rwnaf_odd_loop_body.
  repeat ecSimpl_one.
  removeCoerce.
  reflexivity.

Qed.


Theorem ecScanl_vec_ext : forall t1 t2 (f1 f2 : t1 -> t2 -> t1) n (ls : Vec n t2) x,
  (forall x y, f1 x y = f2 x y) ->
  (ecScanl n t1 t2 f1 x ls) = (ecScanl n t1 t2 f2 x ls).

  induction ls; intros.
  reflexivity.

  simpl.
  rewrite H.
  f_equal.
  eapply IHls; eauto.

Qed.

Fixpoint toN_excl_int n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_int n') ++ (Z.of_nat n') :: List.nil
  end.

Definition toN_int n :=
  (toN_excl_int n) ++ ((Z.of_nat n) :: List.nil).

Theorem ecFromTo_0_n_equiv : forall n,
  to_list (ecFromTo 0 (TCNum n) Integer PLiteralInteger) = 
  (toN_int n).

  intros.
  unfold ecFromTo, toN_int.
  simpl.

Admitted.

Fixpoint toN_excl_bv s n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_bv s n') ++ (bvNat s n') :: List.nil
  end.

Definition toN_bv s n :=
  (toN_excl_bv s n) ++ ((bvNat s n) :: List.nil).

Theorem ecFromTo_0_n_bv_excl_equiv : forall (s : nat) n,
  to_list (ecFromTo 0 (TCNum n) (CryptolPrimitivesForSAWCore.seq (TCNum s) Bool)
           (PLiteralSeqBool (TCNum s))) = 
  (toN_excl_bv s (S n)).

Admitted.

Theorem ecFromTo_0_n_bv_equiv : forall (s : nat) n,
  to_list (ecFromTo 0 (TCNum n) (CryptolPrimitivesForSAWCore.seq (TCNum s) Bool)
           (PLiteralSeqBool (TCNum s))) = 
  (toN_bv s n).

Admitted.


Theorem ecFromTo_m_n_equiv : forall m n,
  to_list (ecFromTo (TCNum m) (TCNum n) Integer PLiteralInteger) = 
  (List.map (Z.add (Z.of_nat m)) (toN_int (n-m))).

Admitted.

Theorem toList_ecDrop_equiv : forall A (inh : Inhabited A) n m (v : Vec (addNat n m) A),
  to_list (ecDrop n m _ v) = skipn n (to_list v).

Admitted.

Theorem toList_append_equiv : forall A (inh : Inhabited A) n m (v1 : Vec n A)(v2 : Vec m A),
  to_list (append v1 v2) = 
  List.app (to_list v1) (to_list v2).

Admitted.

Theorem toList_map_equiv : forall A (inh : Inhabited A) B n (v : Vec n A) (f : A -> B),
  to_list (SAWCorePrelude.map f _ v) = List.map f (to_list v).

Admitted.

Theorem toList_cons : forall A n (v : Vec n A) a,
  to_list (cons a v) = List.cons a (to_list v).

  intros.
  reflexivity.

Qed.

Fixpoint scanl (A B : Type)(f : A -> B -> A)(ls : list B)(a : A) :=
  match ls with 
  | List.nil => a :: List.nil 
  | b :: ls' => a :: scanl f ls' (f a b)
  end.

Theorem toList_scanl_equiv : forall (A B : Type)(f : A -> B -> A) n (v : Vec n B)(a : A),
  to_list (ecScanl (TCNum n) A B f a v) = scanl f (to_list v) a.

  induction v; intros.
  simpl. reflexivity.

  simpl.
  rewrite toList_cons.
  f_equal.
  eapply IHv.

Qed.

Theorem ecAtBack_0_equiv : forall n A (inh : Inhabited A)(def : A) r (v : seq (TCNum n) A),
  (@ecAtBack (TCNum n) A inh _ r v 0) = List.hd def (List.rev (to_list v)).
    
  intros.
  unfold ecAtBack.

Abort.

Fixpoint scanl_fix (A C : Type)(f : A -> A)(f1 f2 : A -> C) n a := 
  match n with
  | 0 => List.nil
  | 1 => (f1 a) :: (f2 a) :: List.nil
  | S n' => (f1 a) :: (scanl_fix f f1 f2 n' (f a))
  end.

From Top Require Import GroupMulWNAF.
Require Import ZArith.BinInt.
Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.

Definition fiat_mul_scalar_rwnaf_odd_gen wsize numWindows s :=
  List.map (fun x : bitvector 16 * bitvector 384 => fst x)
  (scanl
     (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize (snd __p2)) (toN_int numWindows)
     (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize s)) ++
[drop Bool 368%nat 16%nat
   (snd
      (hd (inhabitant (Inhabited_prod (bitvector 16) (bitvector 384)))
         (rev
            (scanl
               (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
                fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize (snd __p2)) 
               (toN_int numWindows) (fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize s)))))].


Local Open Scope Z_scope.

Definition recode_rwnaf_odd_scanl_fix_body wsize n :=
      let k_i := (n mod (Z.double (twoToWsize wsize))) - (twoToWsize wsize) in
      let n' := (n - k_i) / (twoToWsize wsize) in
      (k_i, n').

Theorem recode_rwnaf_odd_scanl_equiv : forall wsize nw (n : Z),
  recode_rwnaf_odd wsize (S nw) n = 
  scanl_fix 
    (fun p => recode_rwnaf_odd_scanl_fix_body wsize (snd p))
    (fun p => fst p)
    (fun p => snd p)
    (S nw) (recode_rwnaf_odd_scanl_fix_body wsize n).

  induction nw; intros; simpl in *.
  reflexivity.
  rewrite IHnw.
  reflexivity.
Qed.


Theorem hd_app_eq : forall (A : Type)(defA: A)(ls1 ls2 : list A),
  length ls1 <> O ->
  hd defA (ls1 ++ ls2) = hd defA ls1.

  intros.
  destruct ls1; simpl in *.
  intuition.
  trivial.
Qed.

Theorem scanl_length : forall (A B : Type)(ls : list A)(f : B -> A -> B)(b : B),
  Datatypes.length (scanl f ls b) <> O.

  intros.
  destruct ls; simpl; intuition.

Qed.


Theorem scanl_fix_equiv : forall (A B C: Type) (defA : A) (f : A -> A) (ls : list B) (n : nat) (f1 f2 : A -> C) a,
  List.length ls = n ->  
  (List.map f1 (scanl (fun x y => f x) ls a)) ++ (f2 (List.hd defA (List.rev (scanl (fun x y => f x) ls a))))::List.nil = 
  scanl_fix f f1 f2 (S n) a.

  induction ls; destruct n; intros; simpl in *.
  reflexivity.
  discriminate.
  discriminate.
  
  f_equal.

  rewrite hd_app_eq.
  eapply IHls.
  lia.

  rewrite rev_length.
  eapply scanl_length.
Qed.


Theorem ecCat_equiv : forall s1 s2 t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (ecCat (TCNum s1) (TCNum s2) t a b) = (append a b).

  intros.
  reflexivity.
Qed.


Theorem to_list_ecCAt_equiv : forall (s1 s2 : nat) t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (to_list (ecCat (TCNum s1) (TCNum s2) t a b)) = (List.app (to_list a) (to_list b)).

  intros.
  rewrite ecCat_equiv.
  apply toList_append_equiv.

Qed.

Theorem sawAt_nth_equiv : forall (A : Type)(inh : Inhabited A)(n1 : nat)(ls : Vec n1 A)(n2 : nat),
   (n2 < n1)%nat ->
   (sawAt _ _ ls n2) = (nth n2 (to_list ls) (inhabitant inh)).

  induction ls; intros; simpl in *.
  lia.

  destruct n2; simpl in *.
  trivial.

  unfold sawAt in *. simpl.
  rewrite IHls.
  reflexivity.
  lia.
Qed.

Theorem toList_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (reverse ls) = rev (to_list ls).


  induction ls; intros; simpl in *.
  trivial.
Admitted.

Theorem nth_0_hd_equiv : forall (A : Type)(defA : A)(ls : list A),
  nth 0 ls defA = hd defA ls.

  destruct ls; trivial.

Qed.

Theorem scanl_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    (scanl f1 ls a) = (scanl f2 ls a).

  induction ls; intuition idtac; simpl in *.
  f_equal.
  rewrite H.
  eapply IHls.
  eauto.

Qed.

Require Import Coq.ZArith.Zdigits.

(*
Theorem recode_rwnaf_odd_scanl_fix_body_equiv : forall wsize (s : bitvector 384),
  fiat_mul_scalar_rwnaf_odd_loop_body_gen wsize s
  = recode_rwnaf_odd_scanl_fix_body wsize (binary_value _ s).
*)

(* Take a gen function an simplify to it. Then prove that equivalent to the model *)
Theorem fiat_mul_scalar_rwnaf_odd_gen_equiv : forall s,
  to_list (fiat_mul_scalar_rwnaf_odd s) = (fiat_mul_scalar_rwnaf_odd_gen 7 52 s).

  intros.
  unfold fiat_mul_scalar_rwnaf_odd.
  repeat removeCoerce.

  Local Opaque append of_list ecFromTo.
  simpl.

  match goal with
  | [|- context[to_list (append ?v1 ?v2 )]] =>
    replace (to_list (append v1 v2 )) with (List.app (to_list v1) (to_list v2)); [idtac | symmetry; apply toList_append_equiv]
  end.

  rewrite toList_map_equiv.
  match goal with
  | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
    replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
  end.

  rewrite to_list_of_list_opp.
  rewrite ecFromTo_0_n_equiv.
  rewrite sawAt_nth_equiv.
  rewrite toList_reverse_equiv.
  rewrite nth_0_hd_equiv.
  match goal with
  | [|- context[to_list (SAWCoreVectorsAsCoqVectors.scanl ?t1 ?t2 ?n ?f ?a ?v)]] =>
    replace (to_list (SAWCoreVectorsAsCoqVectors.scanl t1 t2 n f a v)) with (scanl f (to_list v) a); [idtac | symmetry; apply toList_scanl_equiv]
  end.

  rewrite <- fiat_mul_scalar_rwnaf_odd_loop_body_gen_equiv.
  rewrite (scanl_ext _ (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      fiat_mul_scalar_rwnaf_odd_loop_body_gen 7 (snd __p2))).

  rewrite ecFromTo_0_n_equiv.
  trivial.

  intros.
  symmetry.
  apply fiat_mul_scalar_rwnaf_odd_loop_body_gen_equiv.

  lia.

Qed.

Theorem to_list_cons : forall (A : Type)(n : Nat)(ls : Vec n A) x,
  to_list (VectorDef.cons x ls) = List.cons x (to_list ls).
Admitted.

Definition fiat_mul_scalar_rwnaf_gen wsize nw s := 
  fiat_mul_scalar_rwnaf_odd_gen wsize nw
    (bvOr s (intToBv 384%nat 1)).

Theorem fiat_mul_scalar_rwnaf_equiv : forall s,
  to_list (fiat_mul_scalar_rwnaf s) = fiat_mul_scalar_rwnaf_gen 7 52 s.

  intros.
  unfold fiat_mul_scalar_rwnaf.
  rewrite fiat_mul_scalar_rwnaf_odd_gen_equiv.
  Local Opaque fiat_mul_scalar_rwnaf_odd_gen.
  simpl.
  reflexivity.

Qed.

Theorem sawAt_3_equiv : forall A (inh : Inhabited A) (v : Vector.t A 3),
  Vector.cons (sawAt 3%nat A v 0%nat)
    (Vector.cons (sawAt 3%nat A v 1%nat)
      (Vector.cons (sawAt 3%nat A v 2%nat) (Vector.nil A)))
  = v.
Admitted.

Theorem sawAt_3_equiv_gen : forall A (inh : Inhabited A) (v1 v2 : Vector.t A 3),
  v1 = v2 ->
  Vector.cons (sawAt 3%nat A v1 0%nat)
    (Vector.cons (sawAt 3%nat A v1 1%nat)
      (Vector.cons (sawAt 3%nat A v1 2%nat) (Vector.nil A)))
  = v2.
  
  intros.
  subst.
  apply sawAt_3_equiv.

Qed.

Theorem ecFoldl_foldl_equiv : forall (A B : Type)(inhB : Inhabited B)(f : A -> B -> A) n ls a,
    ecFoldl (TCNum n) _ _ f a ls = fold_left f (to_list ls) a.

Admitted.

Theorem toList_ecReverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (ecReverse (TCNum n) _ ls) = rev (to_list ls).
    
  intros.
  simpl.
  apply toList_reverse_equiv.
Qed.

Theorem toList_zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb: Inhabited B) n (lsa: Vec n A) (lsb : Vec n B),
  to_list (zip (TCNum n) _ _ lsa lsb) = List.combine (to_list lsa) (to_list lsb).

Admitted.

Theorem ecAt_equiv : forall A s (ls : Vec s A) (n : Z) def,
    (Z.to_nat n < s)%nat ->
    ecAt (TCNum s) A _ PIntegralInteger ls n = nth (Z.to_nat n) (to_list ls) def.

Admitted.

Definition fiat_select_point_ct_gen x t :=
  fold_left
  (fun acc p =>
   fiat_select_point_loop_body x acc (fst p) (snd p))
  (combine (toN_excl_bv 64%nat (length t)) t) (of_list [zero_felem; zero_felem; zero_felem]).

Theorem to_list_length : forall (A : Type)(n : nat)(x : Vector.t A n),
  (List.length (to_list x)) = n.

  induction x; intros. 
  simpl in *; trivial.
  rewrite to_list_cons.
  simpl.
  rewrite IHx.
  trivial.

Qed.


Theorem fiat_select_point_ct_gen_equiv : forall x t,
  fiat_select_point_ct x t = fiat_select_point_ct_gen x (to_list t).

  intros.
  unfold fiat_select_point_ct, fiat_select_point_ct_gen.
  removeCoerce.
  rewrite ecFoldl_foldl_equiv.
  rewrite toList_zip_equiv. 

  replace ((to_list
        (ecFromTo 0%nat 63%nat (CryptolPrimitivesForSAWCore.seq 64%nat Bool)
           (PLiteralSeqBool 64%nat))))
  with (toN_excl_bv 64%nat (length (to_list t))).
  reflexivity.
  rewrite to_list_length.
  symmetry.
  apply (@ecFromTo_0_n_bv_excl_equiv 64%nat 63%nat).
Qed.

Theorem fold_left_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    fold_left f1 ls a = fold_left f2 ls a.

  induction ls; intuition idtac; simpl in *.
  rewrite H.
  apply IHls.
  intuition idtac.  
Qed.

Theorem toList_drop_equiv : forall A (inh : Inhabited A) n1 n2 ls,
  to_list (drop A n1 n2 ls) = skipn n1 (to_list ls).

Admitted.

Section PointMul.

  Definition felem := Vector.t (bitvector 64) 6.
  Definition prodPoint := (felem * felem * felem)%type.
  Definition point := Vector.t felem 3.
  Variable field_square : felem -> felem.
  Variable field_mul field_sub field_add : felem -> felem -> felem.
  Variable field_opp : felem -> felem.

  Definition fiat_point_opp (p : point) : point :=
    Vector.cons (sawAt _ _ p 0%nat) 
      (Vector.cons (field_opp (sawAt _ _ p 1%nat) ) 
        (Vector.cons (sawAt _ _ p 2%nat)  (Vector.nil felem))).

  Definition fiat_point_mul := fiat_point_mul field_square field_mul field_sub field_add field_opp.
 
  Definition conditional_subtract_if_even_ct := 
    conditional_subtract_if_even_ct field_square field_mul field_sub field_add field_opp.

  Definition fiat_point_add := 
    fiat_point_add field_square field_mul field_sub field_add.

  Theorem conditional_subtract_if_even_ct_equiv : forall (p1 : point) n (p2 : point),
    conditional_subtract_if_even_ct p1 n p2 = 
    if (even (bvToNat _ n)) then (fiat_point_add false p1 (fiat_point_opp p2)) else p1.

    intros.
    unfold conditional_subtract_if_even_ct, EC_fiat_P384_7.conditional_subtract_if_even_ct.
    unfold fiat_field_cmovznz.
    match goal with
    | [|- context[of_list [if ?a then _ else _; _; _]]] =>
      case_eq a; intros
    end.
    unfold ecEq, ecAnd, ecZero, byte_to_limb in H. simpl in H.
    case_eq (even (bvToNat 384%nat n)); intros.
    (* both even *)
    simpl.
    Local Transparent of_list.
    unfold of_list.
    apply sawAt_3_equiv.

    (* contradiction *)
    admit.

    case_eq (even (bvToNat 384%nat n)); intros.
    (* contradiction *)
    admit.

    (* both odd. *)
    unfold of_list. 
    apply sawAt_3_equiv.

  Admitted.

  Definition fiat_pre_comp_table := fiat_pre_comp_table field_square field_mul field_sub field_add .

  Definition fiat_pre_comp_table_gen pred_tsize p :=
    scanl
  (fun
     (z : CryptolPrimitivesForSAWCore.seq 3%nat
            (CryptolPrimitivesForSAWCore.seq 6%nat
               (CryptolPrimitivesForSAWCore.seq 64%nat Bool))) 
     (_ : Integer) =>
   EC_fiat_P384_7.fiat_point_add field_square field_mul field_sub field_add
     (ecNumber 0%nat Bool PLiteralBit)
     (fiat_point_double field_square field_mul field_sub field_add p) z)
  (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int pred_tsize)) p .

  Theorem fiat_pre_comp_table_gen_equiv : forall p,
    to_list (fiat_pre_comp_table p) = fiat_pre_comp_table_gen 62%nat p.

    intros. 
    unfold fiat_pre_comp_table_gen, fiat_pre_comp_table, EC_fiat_P384_7.fiat_pre_comp_table.
    removeCoerce.
    removeCoerce.
    rewrite toList_scanl_equiv.
    Check ecFromTo_m_n_equiv.
    replace (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int 62))
      with (to_list (ecFromTo (TCNum 1%nat) (TCNum 63%nat) Integer PLiteralInteger)).
    reflexivity.
    apply ecFromTo_m_n_equiv.
  Qed.

  
  Definition fiat_double_add_body := 
    fiat_double_add_body field_square field_mul field_sub field_add field_opp.
  

  Definition conditional_point_opp (t : bitvector 64) (p : point): point :=
    Vector.cons (sawAt _ _ p 0%nat) (Vector.cons (fiat_field_cmovznz t (sawAt _ _ p 1%nat) (field_opp (sawAt _ _ p 1%nat))) (Vector.cons (sawAt _ _ p 2%nat) (Vector.nil _))).

  Definition fiat_double_add_body_gen pred_wsize t p id :=
    EC_fiat_P384_7.fiat_point_add field_square field_mul field_sub
  field_add false
  (fold_left
     (fun
        (x : CryptolPrimitivesForSAWCore.seq 3%nat
               (CryptolPrimitivesForSAWCore.seq 6%nat
                  (CryptolPrimitivesForSAWCore.seq 64%nat Bool)))
        (_ : Integer) =>
      fiat_point_double field_square field_mul field_sub field_add x)
     (toN_int pred_wsize) p)
  (conditional_point_opp
     (point_id_to_limb
        (bvAnd (shiftR 16 bool false id (S pred_wsize)) (bvNat 16%nat 1%nat)))
     (fiat_select_point_ct_gen
        (sign_extend_16_64
           (bvSShr 15%nat
              (bvAdd 16
                 (bvXor 16%nat id
                    (bvNeg 16
                       (bvAnd (shiftR 16 bool false id (S pred_wsize))
                          (bvNat 16%nat 1%nat))))
                 (bvAnd (shiftR 16 bool false id (S pred_wsize))
                    (bvNat 16%nat 1%nat))) 1%nat)) t)).

  Theorem fiat_double_add_body_gen_equiv : forall t p id,
    fiat_double_add_body t p id = fiat_double_add_body_gen 6 (to_list t) p id.

    intros.
    unfold fiat_double_add_body, EC_fiat_P384_7.fiat_double_add_body.
    removeCoerce.
    rewrite ecFoldl_foldl_equiv.
    replace (to_list (ecFromTo 0%nat 6%nat Integer PLiteralInteger))
      with (toN_int 6%nat).
    repeat rewrite fiat_select_point_ct_gen_equiv.
    reflexivity.

    symmetry.
    apply ecFromTo_0_n_equiv.

  Qed.

  Definition fiat_point_mul_gen wsize nw pred_tsize p s : point := 
    EC_fiat_P384_7.conditional_subtract_if_even_ct field_square field_mul
  field_sub field_add field_opp
  (fold_left
     (fiat_double_add_body_gen (pred wsize) (fiat_pre_comp_table_gen pred_tsize p))
     (skipn 1 (rev (fiat_mul_scalar_rwnaf_gen wsize nw s)))
     (fiat_select_point_ct_gen
        (sign_extend_16_64
           (bvSShr 15
              (nth (S (S nw)) (fiat_mul_scalar_rwnaf_gen wsize nw s)
                 (bvNat 16%nat 0%nat))
              1%nat) )
        (fiat_pre_comp_table_gen pred_tsize p))) s
  (nth 0 (fiat_pre_comp_table_gen pred_tsize p)
     (inhabitant (ecNumber 0%nat Integer PLiteralInteger))).

  Theorem fiat_point_mul_gen_equiv : forall p s,
    fiat_point_mul p s = fiat_point_mul_gen 7 52 62 p s.

    intros.
    unfold fiat_point_mul, EC_fiat_P384_7.fiat_point_mul.

    rewrite ecFoldl_foldl_equiv.

    Local Opaque fold_left.
    simpl.
    rewrite (fold_left_ext _
      (fiat_double_add_body_gen 6%nat
        (fiat_pre_comp_table_gen 62%nat p))
    ).
    rewrite toList_drop_equiv.
    rewrite toList_reverse_equiv.
    rewrite fiat_mul_scalar_rwnaf_equiv.

    rewrite fiat_select_point_ct_gen_equiv.
    rewrite fiat_pre_comp_table_gen_equiv.

    unfold fiat_point_mul_gen.
    rewrite sawAt_nth_equiv.
    rewrite fiat_mul_scalar_rwnaf_equiv.

    rewrite sawAt_nth_equiv.
    rewrite fiat_pre_comp_table_gen_equiv.

    reflexivity.

    lia.
    lia.

    intros.
    rewrite <- fiat_pre_comp_table_gen_equiv.
    unfold fiat_pre_comp_table.
  
    rewrite <- fiat_double_add_body_gen_equiv.
    reflexivity.

  Qed.

End PointMul.

(*
Definition fiat_mul_scalar_rwnaf_odd_loop_body_gen (wsize : nat)(s : CryptolPrimitivesForSAWCore.seq (CryptolPrimitivesForSAWCore.TCNum 384) SAWCoreScaffolding.Bool) (i : CryptolPrimitivesForSAWCore.seq (CryptolPrimitivesForSAWCore.TCNum 64) SAWCoreScaffolding.Bool)  :=
    let var__0   := CryptolPrimitivesForSAWCore.TCNum 1 in
    let var__1   := PZeroBit in let var__2   := PIntegralInteger in
    let var__3   := PLiteralInteger in
    let var__4   := CryptolPrimitivesForSAWCore.TCNum 7 in
    let var__5   := CryptolPrimitivesForSAWCore.TCNum 384 in
    let var__6   := CryptolPrimitivesForSAWCore.seq var__5 SAWCoreScaffolding.Bool in
    let var__7   := CryptolPrimitivesForSAWCore.TCNum 32 in
    let var__8   := CryptolPrimitivesForSAWCore.seq var__7 SAWCoreScaffolding.Bool in
    let var__9   := CryptolPrimitivesForSAWCore.TCNum 16 in
    let var__10   := CryptolPrimitivesForSAWCore.ecNumber var__4 SAWCoreScaffolding.Integer var__3 in
    let var__11   := CryptolPrimitivesForSAWCore.ecNumber var__0 var__6 (CryptolPrimitivesForSAWCore.PLiteralSeqBool var__5) in
    let var__12   := CryptolPrimitivesForSAWCore.PRingSeqBool var__5 in
    let var__13   := CryptolPrimitivesForSAWCore.ecMinus var__6 var__12 (CryptolPrimitivesForSAWCore.ecAnd var__6 (CryptolPrimitivesForSAWCore.PLogicSeqBool var__5) s (CryptolPrimitivesForSAWCore.ecMinus var__6 var__12 (CryptolPrimitivesForSAWCore.ecShiftL var__5 SAWCoreScaffolding.Integer SAWCoreScaffolding.Bool var__2 var__1 var__11 (CryptolPrimitivesForSAWCore.ecPlus SAWCoreScaffolding.Integer PRingInteger var__10 (CryptolPrimitivesForSAWCore.ecNumber var__0 SAWCoreScaffolding.Integer var__3))) var__11)) (CryptolPrimitivesForSAWCore.ecShiftL var__5 SAWCoreScaffolding.Integer SAWCoreScaffolding.Bool var__2 var__1 var__11 var__10) in
    let var__14   := CryptolPrimitivesForSAWCore.TCNum 368 in
    let var__15   := CryptolPrimitivesForSAWCore.tcAdd var__14 var__9 in
    pair 
      (CryptolPrimitivesForSAWCore.ecDrop var__14 var__9 SAWCoreScaffolding.Bool 
        var__13
        
      ) 
      (shiftR _ _ false
        (bvSub 
          s 
          (bvSub
            (bvAnd
              s 
              (bvSub
                (shiftL _ _ false
                  var__11 
                  (wsize + 1)
                ) 
                var__11
              )
            ) 
            (CryptolPrimitivesForSAWCore.ecShiftL var__5 SAWCoreScaffolding.Integer SAWCoreScaffolding.Bool var__2 var__1 
              var__11 
              var__10
            )
          )
        ) 
        wsize
      ).

Theorem fiat_mul_scalar_rwnaf_odd_loop_body_0_gen_equiv : forall s i,
  fiat_mul_scalar_rwnaf_odd_loop_body_gen_0 7 s i = fiat_mul_scalar_rwnaf_odd_loop_body_gen 7 s i.

  intros.
  reflexivity.

Qed.

Definition fiat_mul_scalar_rwnaf_odd_loop_body_gen (wsize : nat)
(s : seq 384 bool) (i : seq 64 bool)  :=
    let var__0   := CryptolPrimitivesForSAWCore.TCNum 1 in
    let var__1   := PZeroBit in let var__2   := PIntegralInteger in
    let var__3   := PLiteralInteger in
    let var__4   := CryptolPrimitivesForSAWCore.TCNum 7 in
    let var__5   := CryptolPrimitivesForSAWCore.TCNum 384 in
    let var__6   := CryptolPrimitivesForSAWCore.seq var__5 SAWCoreScaffolding.Bool in
    let var__7   := CryptolPrimitivesForSAWCore.TCNum 32 in
    let var__8   := CryptolPrimitivesForSAWCore.seq var__7 SAWCoreScaffolding.Bool in
    let var__9   := CryptolPrimitivesForSAWCore.TCNum 16 in
    let var__10   := CryptolPrimitivesForSAWCore.seq var__9 SAWCoreScaffolding.Bool in
    let var__11   := CryptolPrimitivesForSAWCore.ecNumber var__0 var__10 (CryptolPrimitivesForSAWCore.PLiteralSeqBool var__9) in
    let var__12   := CryptolPrimitivesForSAWCore.ecNumber var__4 SAWCoreScaffolding.Integer var__3 in
    let var__13   := CryptolPrimitivesForSAWCore.PRingSeqBool var__9 in
    let var__14   := CryptolPrimitivesForSAWCore.TCNum 368 in
    let var__15   := CryptolPrimitivesForSAWCore.tcAdd var__14 var__9 in
    let var__16   := CryptolPrimitivesForSAWCore.ecMinus var__10 var__13 (CryptolPrimitivesForSAWCore.ecAnd var__10 (CryptolPrimitivesForSAWCore.PLogicSeqBool var__9) (CryptolPrimitivesForSAWCore.ecDrop var__14 var__9 SAWCoreScaffolding.Bool (SAWCoreScaffolding.coerce var__6 (CryptolPrimitivesForSAWCore.seq var__15 SAWCoreScaffolding.Bool) (CryptolPrimitivesForSAWCore.seq_cong1 var__5 var__15 SAWCoreScaffolding.Bool ltac:(solveUnsafeAssert)) s)) (CryptolPrimitivesForSAWCore.ecMinus var__10 var__13 (CryptolPrimitivesForSAWCore.ecShiftL var__9 SAWCoreScaffolding.Integer SAWCoreScaffolding.Bool var__2 var__1 var__11 (CryptolPrimitivesForSAWCore.ecPlus SAWCoreScaffolding.Integer PRingInteger var__12 (CryptolPrimitivesForSAWCore.ecNumber var__0 SAWCoreScaffolding.Integer var__3))) var__11)) (CryptolPrimitivesForSAWCore.ecShiftL var__9 SAWCoreScaffolding.Integer SAWCoreScaffolding.Bool var__2 var__1 var__11 var__12) in
    
let var__17   := CryptolPrimitivesForSAWCore.tcAdd var__9 var__14 in
    pair var__16 
      (shiftR _ _ false
        (bvSub
          s 
          (sign_extend _ 368 
            (CryptolPrimitivesForSAWCore.ecMinus _ var__13 
              (bvAnd
                (drop _ 368 _ s) 
                (bvSub
                  (shiftL _ _ false var__11 (wsize + 1)) 
                  (bvNat _ 1)
                )
              ) 
              (shiftL _ _ false (bvNat _ 1) wsize) 
            )  
          )
        ) 
        7
      ).

Theorem fiat_mul_scalar_rwnaf_odd_loop_body_gen_equiv : forall s i,
  fiat_mul_scalar_rwnaf_odd_loop_body_gen 7 s i = fiat_mul_scalar_rwnaf_odd_loop_body s i.

  intros.
  reflexivity.

Qed.
  


Print fiat_mul_scalar_rwnaf_odd_loop_body.

(* Simplify fiat_mul_scalar_rwnaf_odd_loop_body. First remove all the SAW definitions. This is done in two steps to reduce
the time required for reflexivity to complete. *)

Definition fiat_mul_scalar_rwnaf_loop_body_gen_7 
  (s : seq 384 Bool)(window : seq 16 Bool)(i : seq 64 Bool) : (seq 16 Bool * seq 16 Bool) :=

    let var__0   := CryptolPrimitivesForSAWCore.TCNum 1 in
    let var__1   := PZeroBit in 
    let var__2   := PIntegralInteger in
    let var__3   := PLiteralInteger in
    let var__4   := TCNum 7 in
    let var__5   := TCNum 64 in
    let var__6   := seq var__5 Bool in
    let var__7   := TCNum 32 in
    let var__8   := seq var__7 Bool in
    let var__9   := TCNum 48 in
    let var__10   := PLiteralSeqBool var__7 in
    let var__11   := TCNum 16 in
    let var__12   := seq var__11 Bool in
    let var__13   := tcAdd var__9 var__11 in
    let var__14   := ecNumber var__0 var__12 (PLiteralSeqBool var__11) in
    let var__15   := ecNumber var__4 Integer var__3 in
    let var__16   := PRingSeqBool var__11 in
    let var__17   := 
      ecMinus var__12 var__16 (ecAnd var__12 (PLogicSeqBool var__11) window (ecMinus var__12 var__16 (ecShiftL var__11 Integer Bool var__2 var__1 var__14 (ecPlus Integer PRingInteger var__15 (ecNumber var__0 Integer var__3))) var__14)) (ecShiftL var__11 Integer Bool var__2 var__1 var__14 var__15) in
    
    
    pair 
      (bvSub 
        (bvAnd window (bvSub (shiftL _ _ false var__14 (7 + 1)) var__14)) 
        (shiftL _ _ false var__14 7)
      )
      (drop Bool 48 16 
      (coerce (Vec 64 Bool) (Vec 64 Bool) 
        (seq_cong1 var__5 var__13 Bool ltac:(solveUnsafeAssert)) 
          (ecFoldl var__4 var__6 var__8 
            (fun (a : var__6) (j : var__8) => 
            bvAdd _ 
              a 
              (shiftL _ _ false 
                (fiat_get_bit s 
                  (bvAdd _ 
                    (bvMul _ 
                      (drop Bool 32 32 i) 
                      (bvNat 32 7) 
                    ) 
                    (bvAdd _ (bvNat 32 7) j)
                  )
                ) 
                (bvToNat _ j)
              )
            ) 
          (bvAnd 
            (shiftR _ _ false (bvSub (sign_extend_16_64 window) (sign_extend_16_64 var__17)) 7) 
            (ecNumber (TCNum (Z.to_nat 33554431%Z)) var__6 (PLiteralSeqBool var__5))
          ) 
          (ecFromTo var__0 var__4 var__8 var__10)
        ))).

Theorem fiat_mul_scalar_rwnaf_loop_body_equiv_gen_7 : forall s w i,
  fiat_mul_scalar_rwnaf_loop_body_gen_7 s w i = fiat_mul_scalar_rwnaf_loop_body s w i.

  intros.
  reflexivity.

Qed.

Definition bv16_1 := (Vector.append (Vector.const false 15) (Vector.cons true (Vector.nil _))).
Definition wsize_mask wsize := (bvSub (shiftL _ _ false bv16_1 (wsize + 1)) bv16_1).

Definition fiat_mul_scalar_rwnaf_loop_body_gen 
  (wsize : nat)(s : seq 384 Bool)(window : seq 16 Bool)(i : seq 64 Bool) : (seq 16 Bool * seq 16 Bool) :=    
    pair 
      (bvSub 
        (bvAnd window (bvSub (shiftL _ _ false bv16_1 (wsize + 1)) bv16_1)) 
        (shiftL _ _ false bv16_1 wsize)
      )
      (drop Bool 48 16 
        (foldl _ _ _
          (fun (a : _) (j : _) => 
            bvAdd _ 
              a 
              (shiftL _ _ false 
                (fiat_get_bit s 
                  (bvAdd _ 
                    (bvMul _ 
                      (drop Bool 32 32 i) 
                      (bvNat 32 wsize) 
                    ) 
                    (bvAdd _ (bvNat 32 wsize) j)
                  )
                ) 
                (bvToNat _ j)
              )
            ) 
          (bvAnd 
            (shiftR _ _ false 
              (bvSub 
                (sign_extend_16_64 window) 
                (sign_extend_16_64 (bvSub  (bvAnd window (wsize_mask wsize)) (shiftL _ _ false bv16_1 wsize)))
              ) 
              wsize
            ) 
            (bvNat 64 (Z.to_nat 33554431%Z))
          ) 
          (gen (addNat 1 (subNat wsize 1)) _ (fun i : Nat => bvNat 32 (addNat i 1)))
        )
    ).


Theorem fiat_mul_scalar_rwnaf_loop_body_gen_1_equiv : forall s w i,
  fiat_mul_scalar_rwnaf_loop_body_gen_7 s w i = fiat_mul_scalar_rwnaf_loop_body_gen 7 s w i.
  intros.
  reflexivity.

Qed.

Definition bv64_bit b :=
    (Vector.append (Vector.const false 63) (Vector.cons b (Vector.nil _))).

(*
Theorem foldl_get_bit_simpl : forall wsize i s1 s2 (ls : Vec 384 _) a,
    (foldl _ _ _
          (fun (a : _) (j : _) => 
            bvAdd _ 
              a 
              (shiftL _ _ false 
                (fiat_get_bit ls 
                  (bvAdd _ 
                    (bvMul _ 
                      (drop Bool 32 32 i) 
                      (bvNat 32 wsize) 
                    ) 
                    (bvAdd _ (bvNat 32 wsize) j)
                  )
                ) 
                (bvToNat _ j)
              )
            ) 
          a
          (gen wsize _ (fun i : Nat => bvNat 32 (addNat i 1)))
        ) = 
        bvAdd _ a (fst (splitat ((bvToNat _ i) * wsize) (snd (splitat 1 ls)))).

*)
    

Definition fiat_mul_scalar_rwnaf_gen (pred_numwindows : nat) (wsize : nat) (n : bitvector 384) :=

  let xs := scanl (bitvector 64) (bitvector 16 * bitvector 16) pred_numwindows
             (fun x => fiat_mul_scalar_rwnaf_loop_body_gen wsize n (snd x))
             (intToBv 16 0,
             append (intToBv 8 0)
               (bvOr (bvAnd (drop Bool 376 8 n) (intToBv 8 255))
                  (intToBv 8 1)))
             (gen pred_numwindows (bitvector 64)
                (fun i => intToBv 64 (Z.of_nat (addNat i 0)))) in

  drop (bitvector 16) 1 (S pred_numwindows)
    (append_comm
       (SAWCorePrelude.map fst _ xs)
       (cons 
          (snd
             (sawAt _ (bitvector 16 * bitvector 16)
                (reverse xs)
                0)) (nil (bitvector 16)))).

Theorem scanl_ext : forall (A B : Type)(n : Nat)(f1 f2 : B -> A -> B) (ls : Vec n A) b,
  (forall x y, (f1 x y) = (f2 x y)) ->
  scanl _ _ n f1 b ls = scanl _ _ n f2 b ls.

  induction ls; intuition; simpl in *.
  f_equal.
  rewrite H.
  eauto.

Qed.

Theorem fiat_mul_scalar_rwnaf_equiv_gen : forall n,
    fiat_mul_scalar_rwnaf_gen 54 7 n = fiat_mul_scalar_rwnaf n.
Proof.
  intro n.
  Local Opaque scanl gen.
  unfold fiat_mul_scalar_rwnaf_gen, fiat_mul_scalar_rwnaf.
  rewrite (@scanl_ext _ _ _ 
    (fun x : bitvector 16 * bitvector 16 =>
            fiat_mul_scalar_rwnaf_loop_body_gen 7 n (snd x))
    (fun __p0 : seq 16 Bool * seq 16 Bool =>
                  fiat_mul_scalar_rwnaf_loop_body n (snd __p0))).
  reflexivity.

  intros.
  rewrite <- fiat_mul_scalar_rwnaf_loop_body_gen_1_equiv.
  eapply fiat_mul_scalar_rwnaf_loop_body_equiv_gen_7.
Qed.


Local Transparent scanl gen.

Theorem drop1_cons_eq : forall (A : Type)(n : Nat)(ls : Vec n A) x,
  (drop A 1 _ (cons x ls)) = ls.

Admitted.

Theorem sawAt0_cons_eq : forall (A : Type)(pf : Inhabited A)(n : Nat)(ls : Vec n A) x,
  (@sawAt (S n) A pf (cons x ls) 0) = x.

  intros.
  unfold sawAt. trivial.

Qed.


Theorem sawAtS_cons_eq : forall (A : Type)(pf : Inhabited A)(n n' : Nat)(ls : Vec n A) x,
  (@sawAt (S n) A pf (cons x ls) (S n')) = (@sawAt _ A pf ls n').

  intros.
  unfold sawAt. trivial.

Qed.

Theorem sawAt0_scanl_acc : forall (A C : Type)(pf : Inhabited A) f n ls acc,
  (@sawAt (S n) A pf (scanl C A n f acc ls) 0) = acc.

  intros.
  unfold scanl.
  destruct ls; simpl; rewrite sawAt0_cons_eq; trivial.

Qed. 
  

Theorem drop_1_tl : forall (A : Type)(pf : Inhabited A)(n : Nat)(ls : Vec (S n) A),
  (@drop _ pf 1 _ ls) = tl ls.

Admitted.

Theorem to_list_tl : forall (A : Type)(n : Nat)(ls : Vec (S n) A),
  to_list (tl ls) = List.tl (to_list ls).
Admitted.

Theorem to_list_append_comm : forall (A : Type)(pf : Inhabited A)(n1 n2 : Nat)(ls1 : Vec n1 A)(ls2 : Vec n2 A),
  @to_list A (addNat n2 n1) (@append_comm n1 n2 A pf ls1 ls2) = List.app (@to_list A n1 ls1) (@to_list A n2 ls2).
Admitted.


Theorem to_list_saw_map : forall (A B : Type)(pf : Inhabited A)(f : A -> B)(n : Nat)(ls : Vec n A),
  to_list (SAWCorePrelude.map f n ls) = List.map f (to_list ls).
Admitted.

Theorem to_list_nil : forall (A : Type),
  to_list (@nil A) = List.nil.
Admitted.


Theorem sawAt_eq_nth_list : forall (A : Type)(pf : Inhabited A)(n n' : Nat)(ls : Vec n A),
  sawAt n A ls n' = List.nth n' (to_list ls) (inhabitant pf).

Admitted.

Theorem to_list_reverse : forall (A : Type)(pf : Inhabited A)(n : nat)(ls : Vec n A),
  to_list (reverse ls) = List.rev (to_list ls).

Admitted.

Theorem last_eq_nth : forall (A : Type)(def : A)(ls : list A),
  List.last ls def = List.nth (Datatypes.length ls - 1) ls def.

  induction ls using rev_ind; intuition; simpl in *.
  rewrite List.app_length; simpl.
  rewrite app_nth2.
  replace (Datatypes.length ls + 1 - 1 - Datatypes.length ls) with 0.
  rewrite last_last.
  trivial.
  lia.
  lia.

Qed.


Theorem nth_0_rev_eq_last : forall (A : Type)(def : A)(ls : list A),
  List.nth 0 (List.rev ls) def = List.last ls def.

  intros.
  destruct ls. simpl; trivial.

  rewrite rev_nth.
  symmetry.
  apply last_eq_nth.
  simpl.
  lia.

Qed.

Theorem scanl_cons : forall (A C : Type)(n : Nat)(ls : Vec n C) h f acc,
  (scanl C A (S n) f acc (VectorDef.cons h ls)) =
  VectorDef.cons acc (scanl C A n f (f acc h) ls) . 

  intros. simpl in *. trivial.

Qed.

Fixpoint fold_list (A  C: Type)(f : A -> C -> (A * A))(ls : list C)(a : A) : list A :=
  match ls with
  | List.nil => a :: List.nil
  | c :: ls' => let (x, a') := (f a c) in x :: (fold_list f ls' a')
  end.

Theorem fold_list_not_nil : forall (A C : Type)(f : A -> C -> (A * A))(ls : list C)(a : A),
  fold_list f ls a <> List.nil.

  induction ls; intuition; simpl in *.
  discriminate.
  remember (f a0 a) as z. destruct z.
  discriminate.

Qed.

Theorem map_fst_scanl_pair : forall (A C : Type)(f : A -> C -> (A*A))(n : Nat) (ls : Vec n C) p,
  List.map fst (to_list (scanl _ _ _ (fun x => f (snd x)) p ls)) = 
  (fst p) :: (List.tl (List.map fst (to_list (scanl _ _ _ (fun x => f (snd x)) p ls)))).

  induction ls; intuition.

Qed.

Theorem scanl_pair_eq_list :forall (A C : Type)(defA : A * A)(f : A -> C -> (A*A))(n : Nat) (ls : Vec n C) p,
  List.tl
  (List.map fst (to_list (scanl _ _ _ (fun x => f (snd x)) p ls)) ++
   [snd (List.last (to_list (scanl _ _ _ (fun x => f (snd x)) p ls)) defA)]) =
  fold_list f (to_list ls) (snd p).

  induction ls.
  intuition.

  intros.
  rewrite scanl_cons.
  repeat rewrite to_list_cons.
  simpl.
  rewrite map_fst_scanl_pair.

  specialize (IHls (f (snd p) h)).
  destruct (to_list
       (scanl C (A * A) n (fun x : A * A => f (snd x)) (f (snd p) h) ls)).
  simpl in *.
  exfalso.
  eapply fold_list_not_nil.
  symmetry. eauto.
  remember (f (snd p) h) as z. destruct z.
  simpl in *.
  erewrite <- IHls.
  reflexivity.

Qed.

Theorem scanl_pair_eq : 
  forall (A C : Type)(pf : Inhabited A)(f : A -> C -> (A*A))(n : Nat) (ls : Vec n C) p,
    to_list (drop _ 1 _ 
      (append_comm 
        (SAWCorePrelude.map fst _ (scanl _ _ _ (fun x => f (snd x)) p ls) ) 
        (cons (snd (sawAt _ _ (reverse (scanl _ _ _ (fun x => f (snd x)) p ls) ) 0 )) (nil _))))
    =   fold_list f (to_list ls) (snd p).

  intros.
  rewrite drop_1_tl.
  rewrite to_list_tl.
  match goal with
  | [|- context[@to_list ?A ?n3 (@append_comm ?n1 ?n2 ?A ?pf ?ls1 ?ls2)]] =>
    replace (@to_list A n3 (@append_comm n1 n2 A pf ls1 ls2)) 
      with (List.app (@to_list A n1 ls1) (@to_list A n2 ls2)) ;
    [idtac | symmetry ; eapply (@to_list_append_comm A pf n1 n2 ls1 ls2)]
  end.
  rewrite to_list_saw_map.
  rewrite to_list_cons.
  rewrite to_list_nil.
  rewrite sawAt_eq_nth_list.
  rewrite to_list_reverse.
  rewrite nth_0_rev_eq_last.
  eapply scanl_pair_eq_list.

Qed.

*)
