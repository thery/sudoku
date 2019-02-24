(**********************************************************************
     Aux.v                                                                                           
                                                                                                          
     Auxillary functions & theorems for lists                                             
                                                                                                          
                                                                                                          
                                    Laurent.Thery@inria.fr (2006)                  
  **********************************************************************)
Require Export List.
Require Export Arith.
Require Export Tactic.
Require Import Inverse_Image.
Require Import Wf_nat.

(************************************** 
   Some properties on list operators: app, map,...
**************************************)
 
Section List.

Variables (A : Set) (B : Set) (C : Set).
Variable f : A ->  B.

Implicit Type l : list A.

(************************************** 
  An induction theorem for list based on length 
**************************************)
 
Theorem list_length_ind (P : list A ->  Prop) :
 (forall l1,
  (forall l2, length l2 < length l1 ->  P l2) ->  P l1) ->
 forall l,  P l.
Proof.
intros H l;
 apply well_founded_ind with (R := fun x y => length x < length y);
 auto.
apply wf_inverse_image with (R := lt); auto.
apply lt_wf.
Qed.
 
Definition list_length_induction (P : list A ->  Set) :
 (forall l1,
  (forall l2, length l2 < length l1 ->  P l2) ->  P l1) ->
 forall l,  P l.
Proof.
intros H l;
 apply well_founded_induction
      with (R := fun x y  => length x < length y ); auto.
apply wf_inverse_image with (R := lt); auto.
apply lt_wf.
Qed.
 
Theorem in_ex_app a l :
 In a l -> exists l1, exists l2 : list A , l = l1 ++ (a :: l2).
Proof.
elim l; clear l; simpl; auto.
intros H; case H.
intros a1 l H [H1|H1]; auto.
  exists (nil (A:=A)); exists l; simpl; auto.
  eq_tac; auto.
case H; auto; intros l1 [l2 Hl2]; exists (a1 :: l1); exists l2; simpl; auto.
eq_tac; auto.
Qed.

(**************************************
 Properties of nth 
**************************************)

Theorem nth_nil n (a : A) : nth n nil a = a.
Proof.
elim n; simpl; auto.
Qed.

Theorem in_ex_nth (a b : A) l :
  In a l <-> exists n, n < length l /\ a = nth n l b.
Proof.
elim l; simpl; auto; clear l.
  split; [intros H; case H | intros (k, (H, _))]; 
  contradict H; auto with arith.
intros c l (Rec1, Rec2); split.
  intros [H1 | H1]; subst.
  exists 0; auto with arith.
  case Rec1; auto.
  intros n (H2, H3); exists (S n); auto with arith.
intros tmp; case tmp; clear tmp.
intros n; case n; auto.
  intros (H1, H2); auto.
intros n1 (H1, H2); right; apply Rec2.
exists n1; auto with arith.
Qed.

Theorem nth_app_l i r l1 l2 : i < length l1 -> nth i (l1 ++ l2) r = nth i l1 r.
Proof.
revert i l2; elim l1; simpl; auto; clear l1.
  intros i l2 H; contradict H; auto with arith.
intros a l Rec i; case i; simpl; auto with arith.
Qed.

Theorem nth_app_r i r l1 l2 : length l1 <= i -> nth i (l1 ++ l2) r = nth (i - length l1) l2 r.
Proof.
revert i l2; elim l1; simpl; auto; clear l1.
  intros; rewrite <- minus_n_O; auto.
  intros a l Rec i; case i; simpl; auto with arith.
intros l2 HH; contradict HH; auto with arith.
Qed.

Theorem nth_default i r l : length l <= i -> nth i l r = r.
Proof.
revert i; elim l; clear l; simpl; auto.
  intros i; case i; auto.
intros a l Rec i; case i; auto with arith.
intros HH; contradict HH; auto with arith.
Qed.

Theorem list_nth_eq r l1 l2 : 
  length l1 = length l2 ->
  (forall n, nth n l1 r = nth n l2 r) -> l1 = l2.
Proof.
revert l2; elim l1; simpl; auto; clear l1.
  intros l2; case l2; clear l2; auto.
  intros b l2 H; discriminate.
intros a l1 Rec l2; case l2; auto; clear l2.
  intros H; discriminate.
intros b l2 H1 H2; eq_tac; auto; simpl in H1.
  apply (H2 0); auto.
apply Rec; auto with arith.
intros n; generalize (H2 (S n)); simpl; auto.
Qed.

(**************************************
 Properties on app 
**************************************)
 
Theorem length_app l1 l2 : length (l1 ++ l2) = length l1 + length l2.
Proof.
elim l1; simpl; auto.
Qed.
 
Theorem app_inv_head l1 l2 l3 : l1 ++ l2 = l1 ++ l3 ->  l2 = l3.
Proof.
elim l1; simpl; auto.
intros a l H H0; apply H; injection H0; auto.
Qed.
 
Theorem app_inv_tail l1 l2 l3 : l2 ++ l1 = l3 ++ l1 ->  l2 = l3.
Proof.
revert l3; elim l2; simpl.
  intro l3; case l3; auto.
  intros b l H; absurd (length ((b :: l) ++ l1) <= length l1).
    simpl; rewrite length_app; auto with arith.
  rewrite <- H; auto with arith.
intros a l H l3; case l3.
  simpl; intros H1; absurd (length (a :: (l ++ l1)) <= length l1).
    simpl; rewrite length_app; auto with arith.
  rewrite H1; auto with arith.
simpl; intros b l0 H0; injection H0.
intros H1 H2; eq_tac; auto.
Qed.
 
Theorem app_inv_app l1 l2 l3 l4 a :
 l1 ++ l2 = l3 ++ (a :: l4) ->
  (exists l5 : list A , l1 = l3 ++ (a :: l5) ) \/
  (exists l5 , l2 = l5 ++ (a :: l4) ).
Proof.
revert l3; elim l1; simpl; auto.
  intros l3 H; right; exists l3; auto.
intros b l H l3; case l3; simpl.
  intros H0; left; exists l; eq_tac; injection H0; auto.
intros c l0 H0; case (H l0); auto.
  injection H0; auto.
intros [l5 H1].
left; exists l5; eq_tac; injection H0; auto.
Qed.
 
Theorem app_inv_app2 l1 l2 l3 l4 a b :
 l1 ++ l2 = l3 ++ (a :: (b :: l4)) ->
  (exists l5 : list A , l1 = l3 ++ (a :: (b :: l5)) ) \/
  ((exists l5 , l2 = l5 ++ (a :: (b :: l4)) ) \/
   l1 = l3 ++ (a :: nil) /\ l2 = b :: l4).
Proof.
revert l3; elim l1; simpl; auto.
  intros l3 H; right; left; exists l3; auto.
intros a1 l H l3; case l3; simpl.
  case l; simpl.
    intros H0; right; right; injection H0; split; auto.
    eq_tac; auto.
  intros b0 l0 H0; left; exists l0; injection H0; intros; (repeat eq_tac); auto.
intros b0 l0 H0; case (H l0); auto.
- injection H0; auto.
- intros [l5 HH1]; left; exists l5; eq_tac; auto; injection H0; auto.
- intros [H1|[H1 H2]]; auto.
  right; right; split; auto; eq_tac; auto; injection H0; auto.
Qed.
 
Theorem same_length_ex a l1 l2 (l3 : list B) :
 length (l1 ++ (a :: l2)) = length l3 ->
  (exists (l4 : list B),
   exists (l5 : list B) ,
   exists b : B ,
   length l1 = length l4 /\ (length l2 = length l5 /\ l3 = l4 ++ (b :: l5))   ).
Proof.
revert l3; elim l1; simpl; auto.
  intro l3; case l3; simpl; (try (intros; discriminate)).
  intros b l H; exists (nil (A:=B)); exists l; exists b; (repeat (split; auto)).
intros a0 l H l3; case l3; simpl; (try (intros; discriminate)).
intros b l0 H0.
case (H l0); auto.
intros l4 [l5 [b1 [HH1 [HH2 HH3]]]].
exists (b :: l4); exists l5; exists b1; (repeat (simpl; split; auto)).
eq_tac; auto.
Qed.

(************************************** 
  Properties on map 
**************************************)
 
Theorem in_map_inv (b : B) l :
 In b (map f l) ->  (exists a : A , In a l /\ b = f a ).
Proof.
elim l; simpl; auto.
  intros tmp; case tmp.
intros a0 l0 H [H1|H1]; auto.
  exists a0; auto.
case (H H1); intros a1 [H2 H3]; exists a1; auto.
Qed.
 
Theorem in_map_fst_inv a (l : list (B * C)) :
 In a (map (fst (B:=_)) l) ->  (exists c , In (a, c) l ).
Proof.
elim l; simpl; auto.
  intros H; case H.
intros a0 l0 H [H0|H0]; auto.
exists (snd a0); left; rewrite <- H0; case a0; simpl; auto.
case H; auto; intros l1 Hl1; exists l1; auto.
Qed.
 
Theorem length_map l :  length (map f l) = length l.
Proof.
elim l; simpl; auto.
Qed.
 
Theorem map_app l1 l2 :  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
elim l1; simpl; auto.
intros a l0 H; eq_tac; auto.
Qed.
 
Theorem map_length_decompose l1 (l2 : list B) l3 (l4 : list B) :
 length l1 = length l2 ->
 map f (app l1 l3) = app l2 l4 ->  map f l1 = l2 /\ map f l3 = l4.
Proof.
revert l2; elim l1; simpl; auto; clear l1.
  intros l2; case l2; simpl; auto.
  intros; discriminate.
intros a l1 Rec l2; case l2; simpl; clear l2; auto.
  intros; discriminate.
intros b l2 H1 H2.
injection H2; clear H2; intros H2 H3.
case (Rec l2); auto.
intros H4 H5; split; auto.
eq_tac; auto.
Qed.

(************************************** 
  Properties of flat_map 
**************************************)
 
Theorem in_flat_map (l : list B) (f1 : B ->  list C) a b :
 In a (f1 b) -> In b l ->  In a (flat_map f1 l).
Proof.
elim l; simpl; auto.
intros a0 l0 H H0 [H1|H1]; apply in_or_app; auto.
left; rewrite H1; auto.
Qed.
 
Theorem in_flat_map_ex (l : list B) (f1 : B ->  list C) a :
 In a (flat_map f1 l) -> exists b , In b l /\ In a (f1 b).
Proof.
elim l; simpl; auto.
  intros H; case H.
intros a0 l0 H H0; case in_app_or with ( 1 := H0 ); simpl; auto.
  intros H1; exists a0; auto.
intros H1; case H with ( 1 := H1 ).
intros b [H2 H3]; exists b; simpl; auto.
Qed.
 
End List.


(************************************** 
  Propertie of list_prod
**************************************)
 
Theorem length_list_prod (A : Set) (l1 l2 : list A) :
  length (list_prod l1 l2) = length l1 * length l2.
Proof.
elim l1; simpl; auto.
intros a l H; rewrite length_app; rewrite length_map; rewrite H; auto.
Qed.
 
Theorem in_list_prod_inv (A B : Set) a l1 l2 :
 In a (list_prod l1 l2) ->
  (exists b : A , exists c : B , a = (b, c) /\ (In b l1 /\ In c l2)  ).
Proof.
elim l1; simpl; auto; clear l1.
intros H; case H.
intros a1 l1 H1 H2.
case in_app_or with ( 1 := H2 ); intros H3; auto.
  case in_map_inv with ( 1 := H3 ); intros b1 [Hb1 Hb2]; auto.
  exists a1; exists b1; split; auto.
case H1; auto; intros b1 [c1 [Hb1 [Hb2 Hb3]]].
exists b1; exists c1; split; auto.
Qed.

Definition list_eq_dec (A : Set) :
       (forall x y : A, {x = y} + {x <> y}) ->
       forall x y : list A, {x = y} + {x <> y}.
Proof.
intros dec; fix list_eq_dec 2; intros x y; case x; case y.
- left; auto.
- intros; right; discriminate.
- intros; right; discriminate.
- intros b y1 a x1.
  case (dec a b); intros H.
  case (list_eq_dec x1 y1); intros H1.
  left; apply f_equal2 with (f := @cons A); auto.
  intros; right; contradict H1; injection H1; auto.
  intros; right; contradict H; injection H; auto.
Defined.

Arguments list_eq_dec [A].

Definition In_dec (A : Set) :
       (forall x y : A, {x = y} + {x <> y}) ->
       forall (a : A) (l : list A), {In a l} + {~ In a l}.
Proof.
intros dec; fix In_dec 2; intros a l; case l.
  right; simpl; intros H; case H.
intros b l1.
case (In_dec a l1); intros H1.
  left; auto with datatypes.
case (dec a b); intros H2.
left; subst; auto with datatypes.
right; simpl; intros [H3|H3]; auto.
Defined.

Arguments In_dec [A].

Definition In_dec1 (A : Set) :
 (forall x y : A, {x = y} + {x <> y}) -> 
 forall (a : A) (l : list A), 
   {ll : list A * list A| l = fst ll ++ (a :: snd ll)} + {~ In a l}.
Proof.
intros dec; fix In_dec1 2; intros a l; case l.
right; simpl; intros tmp; case tmp.
  intros b l1; case (In_dec1 a l1); intros H.
  left; case H; intros ll HH; exists ((b :: fst ll), snd ll).
  rewrite HH; auto with datatypes.
case (dec a b); intros H1.
left; exists (@nil A, l1); subst; auto.
right; simpl; intros [H2 | H2]; auto.
Defined.

Arguments In_dec1 [A].

Theorem in_fold_map (A : Set) (f : nat -> nat -> A) p l1 l2 :
  In p
    (fold_right
       (fun x l =>
          map (f x) l1 ++ l) nil l2) <->
    (exists x, (exists y , In x l2 /\ In y l1 /\ p = f x y)).
Proof.
elim l2; simpl; auto; clear l2.
  split; auto.
    intros H; case H.
  intros (x, (y, (H, _))); auto.
intros a l2 (Rec1, Rec2); split; intros H.
  case in_app_or with (1 := H); clear H; intros H.
    case (in_map_inv _ _ (f a) p l1); auto.
    intros y (H1, H2).
    exists a; exists y; repeat split; auto.
  case Rec1; auto; clear Rec1 Rec2.
  intros x (y, (U1, (U2, U3))); exists x; exists y; repeat split;
  auto with arith.
case H; intros x (y, ([U1 | U1], (U2, U3))); subst; auto; clear H.
  apply in_or_app; left; auto.
  apply in_map; auto.
apply in_or_app; right; auto.
apply Rec2; auto; clear Rec1 Rec2.
exists x; exists y; repeat split; auto with arith.
Qed.
