
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
From CryptolToCoq Require Import Everything.

From Bits Require Import operations.
From Bits Require Import operations.properties.

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
  to_list (SAWCorePrelude.append _ _ _ v1 v2) = 
  List.app (to_list v1) (to_list v2).

Admitted.

Theorem toList_map_equiv : forall A (inh : Inhabited A) B n (v : Vec n A) (f : A -> B),
  to_list (SAWCorePrelude.map _ _ f _ v) = List.map f (to_list v).

Admitted.

Theorem toList_cons : forall A n (v : Vec n A) a,
  to_list (Vector.cons A a n v) = List.cons a (to_list v).

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

Theorem hd_app_eq : forall (A : Type)(defA: A)(ls1 ls2 : list A),
  List.length ls1 <> O ->
  List.hd defA (ls1 ++ ls2) = List.hd defA ls1.

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

Require Import ZArith.BinInt.

Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Zdigits.


Theorem ecCat_equiv : forall s1 s2 t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (ecCat (TCNum s1) (TCNum s2) t a b) = (SAWCorePrelude.append _ _ _ a b).

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

Theorem to_list_cons : forall (A : Type)(n : Nat)(ls : Vec n A) x,
  to_list (VectorDef.cons _ x _ ls) = List.cons x (to_list ls).
Admitted.

Theorem toList_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (SAWCorePrelude.reverse _ _ ls) = rev (to_list ls).


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

Theorem sawAt_3_equiv : forall A (inh : Inhabited A) (v : Vector.t A 3),
  Vector.cons _ (sawAt 3%nat A v 0%nat) _
    (Vector.cons _ (sawAt 3%nat A v 1%nat) _
      (Vector.cons _ (sawAt 3%nat A v 2%nat) _ (Vector.nil A)))
  = v.
Admitted.

Theorem sawAt_3_equiv_gen : forall A (inh : Inhabited A) (v1 v2 : Vector.t A 3),
  v1 = v2 ->
  Vector.cons _ (sawAt 3%nat A v1 0%nat) _
    (Vector.cons _ (sawAt 3%nat A v1 1%nat) _
      (Vector.cons _ (sawAt 3%nat A v1 2%nat) _ (Vector.nil A)))
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

(* zip is in the generated code. It is reproduced here to allow us to reason about it without importing
generated code. *)

Definition zip (n : CryptolPrimitivesForSAWCore.Num) (a : Type) {Inh_a : SAWCoreScaffolding.Inhabited a} (b : Type) {Inh_b : SAWCoreScaffolding.Inhabited b} (xs : CryptolPrimitivesForSAWCore.seq n a) (ys : CryptolPrimitivesForSAWCore.seq n b)  :=
  let var__0   := prod a b in
  CryptolPrimitivesForSAWCore.seqMap var__0 var__0 n (SAWCorePrelude.uncurry a b var__0 (fun (x : a) (y : b) => pair x y)) (CryptolPrimitivesForSAWCore.seqZipSame a b n xs ys).

Theorem zip_cons_equiv : forall A B (inha : Inhabited A)(inhb : Inhabited B) n (lsa: Vec n A) (lsb: Vec n B) h h0,
  (@zip (TCNum (S n)) A inha B inhb (VectorDef.cons A h n lsa)
     (VectorDef.cons B h0 n lsb)) = VectorDef.cons _ (h, h0) _ (@zip (TCNum n) A inha B inhb lsa lsb).

  intros.
  reflexivity.

Qed.

Theorem Vec_0_nil : forall (A : Type)(v : Vec O A),
  v = @Vector.nil A.

  intros.
  eapply (@case0 _ (fun v => v = Vector.nil A)).
  reflexivity.

Qed.

Theorem Vec_S_cons : forall (A : Type) n (v : Vec (S n) A),
  exists x y, v = @Vector.cons A x n y.

  intros.
  eapply (@VectorDef.caseS' _ _ _ (fun v => exists x y, v = Vector.cons A x n y)).
  intros.
  econstructor.
  econstructor.
  reflexivity.

Qed.

Theorem toList_zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb: Inhabited B) n (lsa: Vec n A) (lsb : Vec n B),
  to_list (zip (TCNum n) lsa lsb) = List.combine (to_list lsa) (to_list lsb).

  induction lsa; intros.
  rewrite (@Vec_0_nil _ lsb0).
  simpl.
  reflexivity.
  destruct (Vec_S_cons lsb0).
  destruct H. subst.
  rewrite zip_cons_equiv.
  repeat rewrite to_list_cons.
  rewrite IHlsa.
  reflexivity. 
Qed.

Theorem ecAt_equiv : forall A s (ls : Vec s A) (n : Z) def,
    (Z.to_nat n < s)%nat ->
    ecAt (TCNum s) A _ PIntegralInteger ls n = nth (Z.to_nat n) (to_list ls) def.

Admitted.

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

Theorem nth_order_S_cons : forall (A : Type) a n (v : Vec n A) n' (pf : (S n' < S n)%nat)(pf' : (n' < n)%nat),
  nth_order (Vector.cons _ a _ v) pf = nth_order v pf'.

  intros.
  unfold nth_order.
  simpl.
  eapply Vector.eq_nth_iff; trivial.
  apply Fin.of_nat_ext.
Qed.

Theorem ssr_addn_even : forall n1 n2,
  even n1 = true ->
  even n2 = true ->
  even (ssrnat.addn n1 n2) = true.
Admitted.

Theorem ssr_double_even : forall n,
  even (ssrnat.double n) = true.
Admitted.

Theorem nth_order_0_cons : forall (A : Type) a n (v : Vec n A) (pf : (0 < S n)%nat),
  nth_order (Vector.cons _ a _ v) pf = a.

  intros.
  reflexivity.
Qed.

Theorem lsb_0_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (Vector.fold_left bvToNatFolder acc v)  = true.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  unfold bvToNatFolder.
  simpl.
  (* double anything is even, 0 is even, even plus even is even*)
  apply ssr_addn_even.
  reflexivity.
  apply ssr_double_even.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_0_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (bvToNat _ v) = true.

  intros. 
  eapply lsb_0_even_h; eauto.

Qed.

Theorem lsb_1_not_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (Vector.fold_left bvToNatFolder acc v)  = false.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  case_eq (ssrnat.double acc); intros; trivial.
  rewrite <- Nat.negb_odd.
  rewrite <- Nat.even_succ.
  rewrite <- H.
  rewrite ssr_double_even.
  reflexivity.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_1_not_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (bvToNat _ v) = false.

  intros. 
  eapply lsb_1_not_even_h; eauto.

Qed.


Theorem bvAnd_cons : forall n a1 a2 (v1 v2 : Vec n _),
  bvAnd _ (Vector.cons _ a1 _ v1) (Vector.cons _ a2 _ v2) = 
  Vector.cons _ (andb a1 a2) _ (bvAnd _ v1 v2).
Admitted.

Theorem addNat_equiv : forall n1 n2,
  (n1 + n2)%nat = addNat n1 n2.

  induction n1; intros; simpl in *; trivial.
  rewrite IHn1.
  reflexivity.
Qed.

Theorem drop_0_equiv : forall (A : Type)(inh : Inhabited A) n2 (v : Vector.t A (addNat O n2)),
  drop _ O n2 v = v.

Admitted.

Theorem append_nil_eq : forall (A : Type)(inh : Inhabited A) n (v : Vec n A),
  SAWCorePrelude.append _ _ _ (@Vector.nil A) v = v.

Admitted.

Theorem bvZipWith_cons : forall f n2 a b (v2a v2b : Vec n2 _),
  bvZipWith f _ (Vector.cons _ a _ v2a) (Vector.cons _ b _ v2b) = 
  Vector.cons _ (f a b) _ (bvZipWith f _ v2a v2b).

  intros.
  reflexivity.

Qed.

Local Arguments Vector.cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.



Theorem bvZipWith_append : forall f n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvZipWith f _ (append v1a v2a) (append v1b v2b) = 
  append (bvZipWith f _ v1a v1b) (bvZipWith f _ v2a v2b).

  induction n1; intros; simpl in *.
  rewrite (@Vec_0_nil _ v1a).
  rewrite (@Vec_0_nil _ v1b).
  repeat rewrite append_nil_eq.
  reflexivity.

  destruct (Vec_S_cons v1a).
  destruct H.
  destruct (Vec_S_cons v1b).
  destruct H0.
  subst.
  repeat rewrite SAWCorePrelude_proofs.append_cons.
  unfold Succ.
  repeat rewrite bvZipWith_cons.
  rewrite IHn1.
  rewrite SAWCorePrelude_proofs.append_cons.
  reflexivity.
Qed.

Theorem bvAnd_append : forall n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvAnd (append v1a v2a) (append v1b v2b) = 
  append (bvAnd v1a v1b) (bvAnd v2a v2b).

  intros.
  apply bvZipWith_append.
Qed.

Theorem Vec_addNat_append : forall (A : Type)(inh : Inhabited A) n1 n2 (v : Vec (addNat n1 n2) A),
  exists v1 v2,
  v = append v1 v2.

  induction n1; intros; simpl in *.
  exists (@Vector.nil A).
  exists v.
  symmetry.
  apply append_nil_eq.
  destruct (Vec_S_cons v).
  destruct H.
  subst.
  destruct (IHn1 _ x0).
  destruct H.
  subst.
  exists (Vector.cons x x1).
  exists x2.
  rewrite SAWCorePrelude_proofs.append_cons.
  reflexivity.

Qed.

Theorem drop_S_cons : forall (A : Type)(inh : Inhabited A) a n1 n2 (v : Vec (addNat n1 n2) A),
  drop _ (S n1) n2 (Vector.cons a v) = drop _ n1 n2 v.

  intros.
  reflexivity.

Qed.

Theorem drop_append_eq : forall (A : Type)(inh : Inhabited A) n1 n2 (v1 : Vec n1 A)(v2 : Vec n2 A),
  drop _ n1 n2 (append v1 v2) = v2.

  induction n1; intros; simpl in *.
  rewrite drop_0_equiv.
  rewrite (@Vec_0_nil _ v1).
  rewrite append_nil_eq.
  reflexivity.
  destruct (Vec_S_cons v1).
  destruct H.
  subst.
  rewrite SAWCorePrelude_proofs.append_cons.
  rewrite drop_S_cons.
  eauto.  
Qed.

Theorem bvAnd_drop_equiv: forall n1 n2 v1 v2,
  (bvAnd (drop _ n1 n2 v1) (drop _ n1 n2 v2)) = 
  drop _ _ _ (bvAnd v1 v2).

  intros.
  destruct (Vec_addNat_append _ _ _ v1).
  destruct H.
  destruct (Vec_addNat_append _ _ _ v2).
  destruct H0.
  subst.
  rewrite bvAnd_append.
  repeat rewrite drop_append_eq.
  reflexivity.

Qed.

Theorem intToBv_1_append_eq : forall n1 n2,
  (n1 > 0)%nat ->
  append (intToBv n2 0) (intToBv n1 1) = intToBv (addNat n2 n1) 1.
Admitted.

Theorem empty_Vec_eq : forall (A : Type)(v1 v2 : Vec O A),
  v1 = v2.

  intros.
  rewrite (@Vec_0_nil _ v1).
  rewrite (@Vec_0_nil _ v2).
  reflexivity.
Qed.

Theorem bvAnd_lsb_drop_equiv: forall n1 n2 v,
  (bvAnd (@drop _ _ n2 n1 v) (intToBv _ 1)) = 
  drop _ _ _ (bvAnd v (intToBv _ 1)).

  intros.
  replace (intToBv n1 1) with (drop _ n2 n1 (append (intToBv n2 0) (intToBv n1 1))).
  rewrite bvAnd_drop_equiv.
  destruct n1.
  apply empty_Vec_eq.
  f_equal.
  f_equal.
  apply intToBv_1_append_eq.
  lia.
  rewrite drop_append_eq.
  trivial.

Qed.


Theorem bvAnd_0 : forall n (v : Vec n _),
  bvAnd v (intToBv n 0) = (intToBv n 0).
Admitted.

Theorem bvAnd_lsb_drop_append_equiv: forall n1 n2 v,
  (n1 > 0)%nat ->
  (bvAnd v (intToBv _ 1)) = 
  (append (intToBv _ 0) (bvAnd (@drop _ _ n2 n1 v) (intToBv _ 1))).

  intros.
  destruct (Vec_addNat_append _ _ _ v).
  destruct H0.
  subst.
  rewrite <- intToBv_1_append_eq; trivial.
  rewrite bvAnd_append.
  f_equal.
  apply bvAnd_0.
  rewrite drop_append_eq.
  reflexivity.

Qed.

Theorem bvEq_append_same : forall n1 n2 (v1 : Vec n1 _) (v2a v2b : Vec n2 _),
  bvEq _ (append v1 v2a) (append v1 v2b) = bvEq _ v2a v2b.

Admitted.

Theorem append_0_320_56 : forall n3 (v : Vec n3 _),
  (append (intToBv 320%nat 0)
       (append (intToBv 56%nat 0) v)) = append (intToBv 376%nat 0) v.

Admitted.

Theorem bvEq_nth_order : forall n (v1 v2 : Vec n _),
  bvEq _ v1 v2 = true ->
  forall n' (pf : (n' < n)%nat),
  nth_order v1 pf = nth_order v2 pf.
Admitted.

Theorem nth_order_append_eq : forall (A : Type)(inh : Inhabited A) n1 (v1 : Vec n1 A) 
  n2 (v2 : Vec n2 A)  n' (nlt2 : (addNat n' n2 < addNat n2 n1)%nat) (nlt1 : (n' < n1)%nat),
  nth_order (append v2 v1) nlt2 = nth_order v1 nlt1.
Admitted.

Theorem nth_order_append_l_eq : forall (A : Type)(inh : Inhabited A) n1 (v1 : Vec n1 A) 
  n2 (v2 : Vec n2 A)  n' (nlt2 : (n' < addNat n2 n1)%nat) (nlt1 : (n' < n2)%nat),
  nth_order (append v2 v1) nlt2 = nth_order v2 nlt1.
Admitted.

Theorem nth_order_drop_eq : forall (A : Type)(inh : Inhabited A) n1 n2 (v : Vec (addNat n1 n2) A)
  n' (lt1 : (addNat n1 n' < addNat n1 n2)%nat)(lt2 : (n' < n2)%nat),
  nth_order (drop _ n1 n2 v) lt2 = nth_order v lt1.

Admitted.

Theorem nth_order_bvAnd_eq : forall n (v : Vec n _)(plt : (pred n < n)%nat),
  nth_order (bvAnd v (intToBv n 1)) plt = nth_order v plt.
Admitted.

Theorem nth_order_bvAnd_l_eq : forall n (v : Vec n _) n' (plt : (n' < n)%nat),
  (n' < pred n)%nat ->
  nth_order (bvAnd v (intToBv n 1)) plt = false.
Admitted.

Theorem nth_order_ext : forall (A : Type) n1 n2 (v : Vec n1 A)(lt1 lt2 : (n2 < n1)%nat),
  nth_order v lt1 = nth_order v lt2.

  intros.
  unfold nth_order.
  f_equal.
  apply Fin.of_nat_ext.
Qed.

Theorem nth_order_0 : forall n1 n2 (nlt : (n2 < n1)%nat),
  nth_order (intToBv n1 0) nlt = false.
Admitted.

Theorem bvEq_false_ne : forall n (v1 v2 : Vec n _ ),
  bvEq _ v1 v2 = false -> 
  exists n' (nlt : (n' < n)%nat),
  nth_order v1 nlt <> nth_order v2 nlt.

Admitted.

Theorem ne_false_impl_true : forall a,
  a <> false ->   
  a = true.

  intros.
  destruct a; trivial.
  intuition idtac.

Qed.

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
  ecFoldl n1 (CryptolPrimitivesForSAWCore.seq n2 Bool) (CryptolPrimitivesForSAWCore.seq n2 Bool) (ecOr (CryptolPrimitivesForSAWCore.seq n2 Bool) (PLogicSeqBool n2))
     y x = intToBv n2 0 ->
  (x = (replicate n1 _ (replicate n2 _ false)) /\ y = (replicate n2 _ false)).

  induction n1; intros; simpl in *.
  unfold replicate. simpl in *.
  generalize H.
  eapply (case0 (fun x => foldl (bitvector n2) (bitvector n2) 0%nat (ecOr (bitvector n2) (PLogicWord n2)) y x = intToBv n2 0 ->
x = @Vector.nil (Vec n2 bool) /\ y = gen n2 bool (fun _ : Nat => false))); eauto; intuition.
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

Theorem scanl_gen_equiv : forall A n f1 f2 z1 x,
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f1))
  = 
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f2)).

  induction n; intuition; simpl in *.
  f_equal.
  apply IHn.
Qed.

Fixpoint bv64Nats_h (n : nat) v :=
  match n with
  | 0%nat => List.nil
  | S n' => (intToBv 64%nat (Z.of_nat v)) :: (bv64Nats_h n' (S v))
  end.

Definition bv64Nats n := bv64Nats_h n 0.

Theorem gen_nat_seq_eq_h : forall n v,
  (to_list
      (gen n (bitvector 64)
         (fun i : nat => intToBv 64%nat (Z.of_nat (addNat i v%nat)))))
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
         (fun i : nat => intToBv 64%nat (Z.of_nat (addNat i 0%nat)))))
  = bv64Nats n.

  intros.
  apply gen_nat_seq_eq_h.    
Qed.

Fixpoint nats_h n v :=
  match n with
  | 0%nat => List.nil
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


Theorem mod_drop_equiv : forall s1 m a,
  (Z.modulo (bvToInt _ a) (Z.shiftl 1 (Z.of_nat m))) =
  (bvToInt _ (drop Bool s1 m a)).

  intros.
  

Admitted.


Theorem bvToInt_sbvToInt_equiv : forall n v,
  (n > 0)%nat ->
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
  (s > 0)%nat ->
  (VectorDef.hd (shiftR (S n) bool false x s) = false).

Admitted.



Theorem bvToInt_drop_equiv : forall n1 n2 x,
  ((bvToInt _ x) < Z.pow 2 (Z.of_nat n2))%Z ->
  bvToInt _ (drop _ n1 n2 x) = bvToInt _ x.

Admitted.


Theorem sbvToInt_drop_equiv_h : forall n1 n2 x,
  (-(Z.pow 2 (Z.of_nat (n2))) <= (sbvToInt _ x) < Z.pow 2 (Z.of_nat (n2)))%Z ->
  spec.toZ (bvToBITS (drop _ n1 (S n2) x)) = sbvToInt _ x.

Admitted.

Theorem sbvToInt_drop_equiv : forall n1 n2 x,
  (n2 > 0)%nat -> 
  (-(Z.pow 2 (Z.of_nat (pred n2))) <= (sbvToInt _ x) < Z.pow 2 (Z.of_nat (pred n2)))%Z ->
  sbvToInt _ (drop _ n1 n2 x) = sbvToInt _ x.

  intros.
  destruct n2.
  lia.
  unfold sbvToInt.
  simpl in *.
  rewrite sbvToInt_drop_equiv_h; trivial.

Qed.

Theorem sbvToInt_bvSub_equiv : forall n (v1 v2 : Vec n _),
  (n > 1)%nat -> 
    (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v1) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
   (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v2) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
  sbvToInt _ (bvSub v1 v2) = ((sbvToInt _ v1) - (sbvToInt _ v2))%Z.

Admitted.

Theorem bvToInt_intToBv_id : forall n v,
  bvToInt n (intToBv n v) = v.

Admitted.

Theorem sbvToInt_intToBv_id : forall n v,
  (-Z.pow 2 (Z.of_nat (pred n)) <= v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
  sbvToInt n (intToBv n v) = v.

Admitted.

Theorem sbvToInt_bvURem_equiv : forall n v1 v2,
  (n > 0)%nat ->
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
  (s < n)%nat ->
  bvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
  Z.shiftl 1 (Z.of_nat s).
Admitted.

Theorem sbvToInt_shiftL_1_equiv : forall n s,
  (n > 0)%nat ->
  (s < pred n)%nat ->
  sbvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
  Z.shiftl 1 (Z.of_nat s).
Admitted.

Theorem bvToInt_bvSub_nonneg_equiv : forall n v1 v2,
  (bvToInt _ v2 <= bvToInt _ v1)%Z ->
  (bvToInt n (bvSub v1 v2)) =
  ((bvToInt _ v1) - (bvToInt _ v2))%Z.
Admitted.

Theorem bvToBITS_bitsToBv_id : forall n v,
  bvToBITS (@bitsToBv n v) = v.
Admitted.

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
  (bvToInt n (bvSub v1 v2)) =
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


Theorem bvToInt_shiftR_lt : forall n v s b,
  ((bvToInt n v) < (Z.pow 2 (Z.of_nat s + b)))%Z ->
  ((bvToInt n (shiftR _ _ false v s)) < Z.pow 2 b)%Z.

Admitted.

Theorem bvToInt_nonneg : forall n v,
  (0 <= bvToInt n v)%Z.
Admitted.

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

Theorem bvOr_bvToInt_equiv : forall n x y,
  bvToInt n (bvOr x y) =
  BinInt.Z.lor (bvToInt n x) (bvToInt n y).
Admitted.

Theorem bvSShr_intToBv_equiv : forall n z v,
  bvSShr _ (intToBv (S n) z) v = intToBv (S n) (Z.shiftr z (Z.of_nat v)).
Admitted.

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

Theorem hd_rev_eq_last : forall (A : Type)(ls : list A)(def : A),
  List.hd def (List.rev ls) = List.last ls def.

  induction ls using rev_ind; intros; simpl in *; trivial.
  rewrite rev_unit.
  simpl.
  rewrite last_last.
  reflexivity.
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
  CryptoToCoq_equiv.scanl f ls a.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  rewrite fold_left_scanl_app_equiv.
  reflexivity.
  congruence.
Qed.

Theorem Forall2_scanl : forall (A1 A2 B1 B2 : Type)(PA : A1 -> A2 -> Prop)(PB : B1 -> B2 -> Prop)
  (f1 : A1 -> B1 -> A1)(f2 : A2 -> B2 -> A2) ls1 ls2 a1 a2,
  List.Forall2 PB ls1 ls2 ->
  (forall a1 a2 b1 b2, PA a1 a2 -> PB b1 b2 -> PA (f1 a1 b1) (f2 a2 b2)) ->
  PA a1 a2 ->
  List.Forall2 PA (scanl f1 ls1 a1) (scanl f2 ls2 a2).

  induction ls1; destruct ls2; simpl in *; intros.
  econstructor; eauto.
  inversion H.
  inversion H.
  inversion H; clear H; subst.
  econstructor; eauto.

Qed.

Theorem Forall2_I : forall (A B : Type)(ls1 : list A)(ls2 : list B),
  List.length ls1 = List.length ls2 ->
  List.Forall2 (fun a b => True) ls1 ls2.

  induction ls1; destruct ls2; intros; simpl in *; try lia.
  econstructor.
  econstructor; eauto; econstructor.

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

Theorem bvToNat_Z_to_nat_equiv : forall n x z,
  (0 <= z)%Z ->
  sbvToInt n x = z ->
  bvToNat n x = Z.to_nat z.

Admitted.

Theorem bvSShr_Z_shiftr_equiv : forall n x1 x2 y1 y2,
  Z.of_nat y1 = y2 ->
  sbvToInt _ x1 = x2 ->
  sbvToInt _ (bvSShr n x1 y1) = Z.shiftr x2 y2.
Admitted.

Theorem sbvToInt_shiftR_equiv:
  forall [n s : nat] x,
  (s >= 0)%nat ->
  sbvToInt n (shiftR n bool false x s) =
  BinInt.Z.shiftr (sbvToInt _ x) (BinInt.Z.of_nat s).

Admitted.


Theorem bvToInt_sbvToInt_range : forall n v x,
  (bvToInt n v < 2^(1 + x) ->
  -2^x <= sbvToInt _ v < 2^x)%Z.
Admitted.

Theorem bvToInt_shiftR_equiv
   : forall (n s : nat) (x : Vector.t bool n),
     (s >= 0)%nat ->
     bvToInt n (shiftR n bool false x s) =
     BinInt.Z.shiftr (bvToInt n x)
       (BinInt.Z.of_nat s).

Admitted.

Theorem bvToInt_bound : forall n v,
    (0 <= bvToInt n v < 2^(Z.of_nat n))%Z.

Admitted.


