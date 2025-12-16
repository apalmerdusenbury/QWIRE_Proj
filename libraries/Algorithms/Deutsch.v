Require Import QuantumLib.Prelim.
Require Import QWIRE.Base.Monad.
Require Import QuantumLib.Matrix.
Require Import QWIRE.Syntax.HOAS.HOASCircuits.
(* Require Import QWIRE.Examples.HOASExamples. Moved deutsch circuit out of HOASExamples.v a library shouldn't depend on an example. *)
Require Import QWIRE.Syntax.HOAS.HOASLib. (* Remove HOASExamples import *)
Require Import QWIRE.Base.Contexts.
Require Import QuantumLib.Complex.
Require Import QWIRE.Typing.TypeChecking.
Require Import QWIRE.Semantics.Denotation.
Require Import QWIRE.Semantics.Composition.
Require Import QWIRE.Syntax.DB.DBCircuits.

Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.

Delimit Scope circ_scope with qc.
Open Scope circ_scope. 
Open Scope matrix_scope.
Open Scope C_scope.

(*************************************)
(* Variations on Deutsch's Algorithm *)
(*************************************)

Definition U_deutsch (U__f : Unitary (Qubit ⊗ Qubit)%qc) : Box One Bit :=
  box_ () ⇒ 
    let_ x     ← init0 $();
    let_ x     ← _H $x;
    let_ y     ← init1 $();
    let_ y     ← _H $y;
    let_ (x,y) ← U__f $(x,y);
    let_ x     ← _H $x; (* found through verification! *)
    let_ y     ← meas $y;
    let_ ()    ← discard $y;
    meas $x.

Lemma U_deutsch_WT : forall U__f, Typed_Box (U_deutsch U__f).
Proof. type_check. Qed.

Definition lift_deutsch (U__f : Square_Box (Qubit ⊗ Qubit)%qc) : Box One Bit :=
  box_ () ⇒
    let_ x     ← init0 $();
    let_ x     ← _H $x;
    let_ y     ← init1 $();
    let_ y     ← _H $y;
    let_ (x,y) ← U__f $ (x,y);
    let_ y     ← meas $y;
    let_ x     ← _H $x;
    lift_ _    ← y;
    meas $x.
    
Lemma lift_deutsch_WT : forall U__f, Typed_Box U__f -> Typed_Box (lift_deutsch U__f).
Proof. type_check. Qed.

(* basic notation *)
Definition deutsch_basic (U__f : Square_Box (Qubit ⊗ Qubit)%qc) : Box One Bit :=
  box_ () ⇒ 
    gate_ x    ← init0   @ ();
    gate_ x    ← _H      @ x;
    gate_ y    ← init1   @ ();
    gate_ y    ← _H      @ y;
    let_ (x,y) ← unbox U__f (x,,y);
    gate_ y    ← meas    @ y;
    gate_ ()   ← discard @ y;
    gate_ x    ← _H      @ x;
    gate_ x    ← meas    @ x;
    output x.

Definition deutsch (U__f : Square_Box (Qubit ⊗ Qubit)%qc) : Box One Bit :=
  box_ () ⇒ 
    let_ x     ← _H $ init0 $ ();
    let_ y     ← _H $ init1 $ ();
    let_ (x,y) ← U__f $ (x,y);
    let_ ()    ← discard $ meas $ y;
    meas $ _H $ x.
Lemma deutsch_WF : forall U__f, Typed_Box U__f -> Typed_Box (deutsch U__f).
Proof. type_check. Qed.

Lemma deutsch_basic_eq : forall U__f, deutsch_basic U__f = deutsch U__f.
Proof.
  intros U__f.
  unfold deutsch, deutsch_basic. 
  unfold apply_box. 
  simpl.
  easy.
Qed.


Definition Deutsch_Jozsa (n : nat) (U : Box ((S n ⨂ Qubit)%qc) ((S n ⨂ Qubit)%qc)) : Box One (n ⨂ Bit)%qc := 
  box_ () ⇒
    let_ qs     ← _H #n $ init0 #n $ (());
    let_ q      ← _H $ init1 $ (); 
    let_ (q,qs) ← U $ (q,qs);   
    let_ ()      ← discard $ meas $q; 
    meas #n $ _H #n $ qs.
Lemma Deutsch_Jozsa_WT : forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
  intros n U__f U_WT.
  induction n.
  + type_check.
  + specialize (inParMany_WT) as WT_Par.
    specialize types_units as WT_units.
    type_check.
    apply WT_Par. 
    all: try apply WT_Par. 
    all: type_check.
    apply types_units.
Qed.

Definition Deutsch_Jozsa' (n : nat) (U : Box (((n ⨂ Qubit)%qc ⊗ Qubit)%qc) (((n ⨂ Qubit)%qc ⊗ Qubit)%qc)) : Box One (n ⨂ Bit)%qc := 
  box_ () ⇒
    let_ qs     ← _H #n $ init0 #n $ (());
    let_ q      ← _H $ init1 $ (); 
    let_ (qs,q) ← U $ (qs,q);   
    let_ ()      ← discard $ meas $q; 
    meas #n $ _H #n $ qs.
Lemma Deutsch_Jozsa_WT' : forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
  intros n U__f U_WT.
  induction n.
  + type_check.
  + specialize (inParMany_WT) as WT_Par.
    specialize types_units as WT_units.
    type_check.
    apply WT_Par. 
    all: try apply WT_Par. 
    all: type_check.
    apply types_units.
Qed.

Lemma size_octx_0 : forall Γ, Γ = ∅ -> size_octx Γ = 0%nat.
Proof.
  intros. 
  subst.
  reflexivity.
Qed.

(* With edge cases that break monoid *)
Ltac solve_merge' :=
  match goal with
  | [ |- ?Γ == ∅ ∙ ?Γ2] => split; [validate|rewrite merge_nil_l; easy]
  | [ |- ?Γ == ?Γ1 ∙ ∅] => split; [validate|rewrite merge_nil_r; easy]
  | _                  => solve_merge
  end.

Ltac compose_denotations :=
  match goal with
  | [ |- context[denote_db_circuit ?safe ?n_Γ0 ?n_Γ1' (hoas_to_db ?Γ1' (HOASCircuits.compose ?c ?f))] ]  
         => let Γ1 := fresh "Γ1" in evar (Γ1 : Ctx);
            (* instantiate Γ1 *)
            assert (pf_f : Γ1 ⊢ f :Fun) by (unfold Γ1; type_check);
            let Γ := fresh "Γ" in evar (Γ : Ctx);
            (* instantiate Γ *)
            assert (pf_merge : Valid Γ1' == Γ1 ∙ Γ) by (unfold Γ, Γ1; solve_merge');
            let pf_c := fresh "pf_c" in
            assert (pf_c : Γ ⊢ c :Circ); [ | 
            let Γ0 := fresh "Γ0" in evar (Γ0 : Ctx);
            let Γ01 := fresh "Γ01" in evar (Γ01 : Ctx);
            let DC := fresh "DC" in
            specialize (@denote_compose safe _ c Γ pf_c _ f Γ0 Γ1 Γ1' Γ01 
                                        pf_f pf_merge) as DC;
            unfold denote_circuit in DC;
            assert (size_Γ0 : size_ctx Γ0 = n_Γ0);
            unfold Γ1, Γ, Γ0 in *
            ]
  end.

(*
Ltac compose_denotations :=
  match goal with
  | [ |- context[denote_db_circuit ?safe ?n_Γ0 ?n_Γ1' (hoas_to_db ?Γ1' (compose ?c ?f))] ]  
         => let Γ1 := fresh "Γ1" in evar (Γ1 : OCtx);
            (* instantiate Γ1 *)
            assert (pf_f : Γ1 ⊢ f :Fun) by (unfold Γ1; type_check);
            let Γ := fresh "Γ" in evar (Γ : OCtx);
            (* instantiate Γ *)
            assert (pf_merge : Γ1' == Γ1 ∙ Γ) by (unfold Γ, Γ1; solve_merge);
            let pf_c := fresh "pf_c" in
            assert (pf_c : Γ ⊢ c :Circ); [ | 
            let Γ0 := fresh "Γ0" in evar (Γ0 : OCtx);
            let DC := fresh "DC" in
            specialize (@denote_compose safe _ c Γ pf_c _ f Γ0 Γ1 Γ1' pf_f  pf_merge)
              as DC;
            unfold denote_circuit in DC;
            assert (size_Γ0 : size_octx Γ0 = n_Γ0);
            unfold Γ1, Γ, Γ0 in *
            ]
  end.
*)

(* U (|x⟩⊗|y⟩) = |x⟩⊗|f x ⊕ y⟩ 
  If f is constant, deutsch U returns 0 
  If f is balanced, deutsch U returns 1 
*)
Section Deutsch.

Definition M_balanced_neg : Matrix 4 4 := 
  list2D_to_matrix [[C0;C1;C0;C0]
                   ;[C1;C0;C0;C0]
                   ;[C0;C0;C1;C0]
                   ;[C0;C0;C0;C1]].
Definition toUnitary (f : bool -> bool) : Matrix 4 4 :=
  match f true, f false with
  | true, true => (* constant true *) I 2 ⊗ σx
  | false, false => (* constant false *) I 4
  | true, false  => (* balanced id *)    cnot
  | false, true  => (* balanced flip *) M_balanced_neg
  end.

Lemma toUnitary_unitary : forall f, WF_Unitary (toUnitary f).
Proof.
  intros. 
  unfold toUnitary, WF_Unitary.
  destruct (f true), (f false); restore_dims; Qsimpl.
  all: split; auto with wf_db.
  replace (σx × σx) with (I 2) by solve_matrix. rewrite id_kron. reflexivity.
  solve_matrix.
  unfold M_balanced_neg.
  apply WF_list2D_to_matrix.
  easy.
  intros li H.
  repeat (destruct H; subst; trivial). 
  unfold M_balanced_neg.  
  solve_matrix.
Qed.  

Hint Unfold apply_box : den_db.

Lemma deutsch_constant : forall (f : bool -> bool) 
                                (U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc),
      Typed_Box U ->
      (f = fun _ => true) \/ (f = fun _ => false) -> 
      (forall ρ, ⟦U⟧ ρ = (toUnitary f) × ρ × (toUnitary f)†) ->
      ⟦deutsch U⟧ (I 1) = ∣0⟩⟨0∣.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
  repeat (simpl; autounfold with den_db).
  Msimpl.
  compose_denotations.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - instantiate (1:=[]). easy.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    2: unfold Γ01; solve_merge'. 
    unfold Γ01. simpl.

    (* rewrite by the semantics of U *)
    rewrite denote_db_unbox in H_U. simpl in H_U.

    repeat (simpl in H_U; autounfold with den_db in H_U).
    unfold denote_circuit in H_U. simpl in H_U.
    rewrite H_U.

    (* simplify the goal *)
    destruct (toUnitary_unitary f) as [WFU UU]; simpl in WFU.
    Qsimpl.

    (* if f is constant, then it is either always true or false *)
    destruct pf_constant as [pf_true | pf_false].
    + (* f = fun _ => true *)
      subst. unfold toUnitary. 
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      C_field. 
   + (* f = fun _ => false *)
     subst. unfold toUnitary.
     solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
     C_field.
Qed.



Lemma deutsch_balanced : forall (f : bool -> bool) (U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc),
      Typed_Box U ->
      (f = fun x => x) \/ (f = fun x => negb x) ->
      (forall ρ, ⟦U⟧ ρ = (toUnitary f) × ρ × (toUnitary f)†) ->
      ⟦deutsch U⟧ (I 1) = ∣1⟩⟨1∣.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
    matrix_denote.
    Qsimpl.

  compose_denotations.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - instantiate (1:=[]). easy.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    2: unfold Γ01; solve_merge'. 
    unfold Γ01. simpl.
    
    (* rewrite by the semantics of U *)
    rewrite denote_db_unbox in H_U. simpl in H_U.

    repeat (simpl in H_U; autounfold with den_db in H_U).
    unfold denote_circuit in H_U. simpl in H_U.
    rewrite H_U.

    (* simplify the goal *)
    destruct (toUnitary_unitary f) as [WFU UU]; simpl in WFU.
    Qsimpl.

    (* if f is balanced, then it is either always identity or negation *)
    destruct pf_constant as [pf_id | pf_neg].
    + (* f = fun x => x *)
      subst. unfold toUnitary. 
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      C_field. 
   + (* f = fun x => ¬ x *)
     subst. unfold toUnitary. simpl. unfold M_balanced_neg, list2D_to_matrix. simpl.
     solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
     C_field.
Qed.        

End Deutsch.
