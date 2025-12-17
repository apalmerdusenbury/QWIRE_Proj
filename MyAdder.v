Require Import QWIRE.Syntax.HOAS.HOASLib.
Require Import QWIRE.Typing.TypeChecking.
Require Import QWIRE.Libraries.algorithms.Arithmetic.

Open Scope circ_scope.

Definition simple_adder : Box ((2 + 3 * 1) ⨂ Qubit) ((2 + 3 * 1) ⨂ Qubit) :=
  adder_circ_n 1.

Lemma simple_adder_typed : Typed_Box simple_adder.
Proof.
  unfold simple_adder.
  apply adder_circ_n_WT.
Qed.

Close Scope circ_scope.