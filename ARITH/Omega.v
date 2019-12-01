(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Acc_and_Inf.

Section Arithmetic_with_an_explicit_infinity.

CoInductive Nat : Set :=
  | Z : Nat
  | SUCC : Nat -> Nat.

Theorem Nat_unfold :
 forall x : Nat, x = match x return Nat with
                     | Z => Z
                     | SUCC x => SUCC x
                     end.
intros.
case x.
trivial.
intros.
trivial.
Qed.

CoInductive EqNat : Nat -> Nat -> Prop :=
  | eqZ : EqNat Z Z
  | eqSUCC : forall n m : Nat, EqNat n m -> EqNat (SUCC n) (SUCC m). 

Lemma EqNat_reflex : forall x : Nat, EqNat x x.
cofix u.
simple destruct x.
apply eqZ.
 
intros.
apply eqSUCC.
apply u.
Qed.

Lemma EqNat_inj : forall x y : Nat, x = y -> EqNat x y.
intros.
rewrite H.
apply EqNat_reflex.
Qed.

Inductive Le (n : Nat) : Nat -> Prop :=
  | Le_n : Le n (SUCC n)
  | Le_S : forall m : Nat, Le n m -> Le n (SUCC m).


Lemma Nat_Induction :
 forall x : Nat,
 Acc Le x ->
 forall P : Nat -> Prop, P Z -> (forall x : Nat, P x -> P (SUCC x)) -> P x.
intros x H.
elim H.
intros x0.
case x0.
intros.
assumption.
intros.
apply H3.
apply (H1 n).
apply Le_n.
assumption.
assumption.
Qed.


Lemma is_definitional_for_finite_numbers :
 forall x : Nat, Acc Le x -> forall y : Nat, EqNat x y -> x = y.
intros x H.
apply (Nat_Induction x H).
intros.
inversion_clear H0.
trivial.
intros.
inversion_clear H1.
cut (x0 = m).
intros.
rewrite H1.
trivial.
apply H0.
assumption.
Qed.

(*
CoFixpoint Plus  : Nat->Nat->Nat :=
 [n,m:Nat]<Nat>Case n of
		    m
		    [p:Nat](SUCC (Plus p m))
	       end.
*)
CoFixpoint Plus  : Nat -> Nat -> Nat :=
  fun n m : Nat => match n with
                   | Z => m
                   | SUCC p => SUCC (Plus p m)
                   end.

(*
Fixpoint ntoN [n:nat] : Nat :=
  <Nat>Case n of
	    Z
	    [m:nat](SUCC (ntoN m))
	end.
*)

Fixpoint ntoN (n : nat) : Nat :=
  match n with
  | O => Z
  | S m => SUCC (ntoN m)
  end.

Lemma natInj : forall n m : nat, ntoN n = ntoN m -> n = m.
fix natInj 1.
intro n.
case n.
simple destruct m.
trivial.
 
simpl in |- *.
intros.
cut (Z <> SUCC (ntoN n0)).
intros.
case H0.
assumption.
discriminate.
 
simple destruct m.
simpl in |- *.
intros.
cut (SUCC (ntoN n0) <> Z).
intros.
case H0.
assumption.
discriminate.
 
simpl in |- *.
intros.
cut (n0 = n1).
intros.
rewrite H0.
trivial.
apply (natInj n0 n1).
injection H; trivial.
Qed.


Section The_Infinity.

CoFixpoint OO  : Nat := SUCC OO.

Definition OO_unfold : OO = SUCC OO := Nat_unfold OO.


Lemma Plus_Idemp : forall x : Nat, EqNat (Plus OO x) OO.
cofix u.
intros.
rewrite OO_unfold.
rewrite (Nat_unfold (Plus (SUCC OO) x)).
simpl in |- *.
apply eqSUCC.
apply u.
Qed.


Lemma OO_is_infinite : Inf Nat Le OO.
cofix u.
rewrite OO_unfold.
apply (inf Nat Le (SUCC OO) OO).
apply (Le_n OO).
apply u.
Qed.


Lemma OO_is_not_Acc : ~ Acc Le OO.
red in |- *.
intros.
apply (NotBoth Nat Le OO).
assumption.
apply OO_is_infinite.
Qed.

Lemma only_OO_expands_forever : forall x : Nat, x = SUCC x -> EqNat x OO.
cofix u.
intros.
rewrite H.
rewrite OO_unfold.
apply eqSUCC.
apply u.
assumption.
Qed.

Lemma Z_is_minimum : forall x : Nat, Acc Le x -> Le Z (SUCC x).
intros.
apply (Nat_Induction x H).
apply Le_n.
intros.
apply Le_S.
assumption.
Qed.

(* 

This lemma is not true if we take Le as being Inductive :

Lemma OO_is_maximum : (x:Nat)(Acc Nat Le x)->(Le x OO).

*)


Lemma only_OO_is_grater_than_OO : forall y : Nat, Le OO y -> EqNat OO y.
cofix u.
intros y H.
case H.
apply EqNat_inj.
apply OO_unfold.
intros.
rewrite OO_unfold.
apply eqSUCC.
apply u.
assumption.
Qed.


Lemma all_infinite_is_OO : forall x : Nat, Inf Nat Le x -> EqNat x OO.
cofix u.
rewrite OO_unfold.
intros.
case H.
intros.
inversion_clear H0.
apply eqSUCC.
apply u.
assumption.
apply eqSUCC.
apply u.
apply (inf Nat Le m y).
assumption.
assumption.
Qed.

(* Strange phenomena *)

Lemma OO_is_infiniteII : Inf Nat (fun x y : Nat => Le y x) OO.
cofix u.
apply (inf Nat (fun x y : Nat => Le y x) OO OO).
pattern OO at 2 in |- *.
rewrite OO_unfold.
apply Le_n.
apply u.
Qed.


End The_Infinity.

End Arithmetic_with_an_explicit_infinity.




