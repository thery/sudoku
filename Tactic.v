
(**********************************************************************
       Tactic.v                                                                                    
                                                                                                         
          Useful tactics                                                                       
                                                                                                         
                                                                                                         
                                      Laurent.Thery@inria.fr (2006)               
 **********************************************************************)

(**************************************
  A simple tactic to end a proof 
**************************************)
Ltac  finish := intros; auto; trivial; discriminate.


(**************************************
 A tactic for proof by contradiction
     with contradict H 
         H: ~A |-   B      gives           |-   A
         H: ~A |- ~ B     gives  H: B |-   A
         H:   A |-   B      gives           |- ~ A
         H:   A |-   B      gives           |- ~ A
         H:   A |- ~ B     gives  H: A |- ~ A
**************************************)

Ltac  contradict name := 
     let term := type of name in (
     match term with 
       (~_) => 
          match goal with 
            |- ~ _  => let x := fresh in
                     (intros x; case name; 
                      generalize x; clear x name;
                      intro name)
          | |- _    => case name; clear name
          end
     | _ => 
          match goal with 
            |- ~ _  => let x := fresh in
                    (intros x;  absurd term;
                       [idtac | exact name]; generalize x; clear x name;
                       intros name)
          | |- _    => generalize name; absurd term;
                       [idtac | exact name]; clear name
          end
     end).


(**************************************
  A tactic to do case analysis keeping the equality
**************************************)

Ltac case_eq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.


(**************************************
 A tactic to use f_equal? theorems 
**************************************)

Ltac eq_tac := 
 match goal with
      |-  (?f _ = ?f _) => apply (f_equal f)
 |     |-  (?f ?X _ = ?f  ?X _) => apply (f_equal (f  X))
 |     |-  (?f _ _ = ?f  _ _) => apply (f_equal2 f)
 |     |-  (?f ?X ?Y _ = ?f ?X ?Y _) => apply (f_equal  (f X Y))
 |     |-  (?f ?X _ _ = ?f ?X _ _) => apply (f_equal2 (f X))
 |     |-  (?f _ _ _ = ?f _ _ _) => apply (f_equal3 f)
 |     |-  (?f ?X ?Y ?Z _ = ?f ?X ?Y ?Z _) => apply (f_equal (f X Y Z))
 |     |-  (?f ?X ?Y _ _ = ?f ?X ?Y _ _) => apply (f_equal2 (f X Y))
 |     |-  (?f ?X _ _ _ = ?f ?X _ _ _) => apply (f_equal3 (f X))
 |     |-  (?f _ _ _ _ _ = ?f _ _ _ _) => apply (f_equal4 f)
 end.

(************************************** 
 A stupid tactic that tries auto also after applying sym_equal
**************************************)

Ltac sauto := (intros; apply sym_equal; auto; fail) || auto.
