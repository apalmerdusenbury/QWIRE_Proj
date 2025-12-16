Require Import QWIRE.Syntax.HOAS.HOASLib.
Require Import QWIRE.Typing.TypeChecking.
Require Import Properties.Algorithms.Arithmetic.

Open Scope circ_scope.
Definition add_one_plus_one : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    (* Initialize: x=1, y=1, cin=0 (computing 1+1+0) *)
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init1 @() ;
    gate_ y0   ← init1 @() ;
    gate_ z0   ← init0 @() ;
    gate_ cout ← init0 @() ;
    
    (* Apply the adder *)
    let_ result ← unbox (adder_circ_n 1) 
         (pair cout (pair z0 (pair y0 (pair x0 (pair cin unit))))) ;
   
   (* Extract carry-out and sum bit (should be 1,0 representing "10" = 2) *)
       let_ (cout', (z0', _)) ← output result ;
       (cout', z0').

   (* Type check: prove the circuit is well-typed *)
   Lemma add_one_plus_one_typed : Typed_Box add_one_plus_one.
   Proof.
     unfold add_one_plus_one.
     type_check.
     (* Need to prove adder_circ_n 1 is well-typed *)
     apply adder_circ_n_WT.
   Qed.
   
Close Scope circ_scope.