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

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10.14                              *)
(*                                 April 1995                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Streams.v                                 *)
(****************************************************************************)
(*       An example of the new implementation of co-inductive types         *)
(*                       by Eduardo Gimenez                                 *)
(****************************************************************************)

Set Asymmetric Patterns.

Require Import Plus.
Require Import Streams.


Section Examples. (* Introducing some streams *)


Section Map.

Variable A B : Set.
Variable f : A -> B.

CoFixpoint map  : Stream A -> Stream B :=
  fun s : Stream A => match s with
                      | Cons a s => Cons (f a) (map s)
                      end.

End Map.


CoFixpoint zeros  : Stream nat := Cons 0 zeros.

CoFixpoint alter  : Stream nat := Cons 0 (Cons 1 alter).

CoFixpoint alter1  : Stream nat := Cons 0 alter2
 with alter2  : Stream nat := Cons 1 alter1.

CoFixpoint from  : nat -> Stream nat := fun n : nat => Cons n (from (S n)).
Definition allnats : Stream nat := from 0.


Lemma all_greater_than_m__are_here :
 forall n m : nat, Str_nth n (from m) = n + m.
simple induction n.
trivial.
intros.
rewrite plus_Snm_nSm.
unfold Str_nth in |- *.
unfold Str_nth in H.
simpl in |- *.
apply H.
Qed.

(*
CoFixpoint mapS : (Stream nat)->(Stream nat) :=
  [s:(Stream nat)]
    <(Stream nat)>Case s of
	            [n:nat][s1:(Stream nat)](Cons (S n) (mapS s1))
  	          end.
*)

CoFixpoint mapS  : Stream nat -> Stream nat :=
  fun s : Stream nat => match s with
                        | Cons n s1 => Cons (S n) (mapS s1)
                        end.


(* A different way of defining the set of streams *)

Inductive Times (A B : Set) : Set :=
    times : A -> B -> Times A B.


CoInductive St2 : Set :=
    Cons2 : Times nat St2 -> St2.

CoFixpoint mapS2  : St2 -> St2 :=
  fun x : St2 =>
  match x return St2 with
  | Cons2 (times x1 x2) => Cons2 (times nat St2 (S x1) (mapS2 x2))
  end.


(* Some examples of  wrong definitions *)
(*
(* 1: Un unguarded recursive call *)


CoFixpoint filter : (nat->bool)->(Stream nat)->(Stream nat) :=
  [p:nat->bool]
     [x:(Stream nat)] Cases x of
	              (Cons n s) =>
                          <(Stream nat)>if  (p n) then (Cons n (filter p s)) 
				       	          else (filter p s)
	               end. 

(* 2: A recursive call in the argument of a Case *)

CoFixpoint wrong : (Stream nat) := (Cons O (tl nat wrong)).

(* 3: Nested recursive calls *)


CoFixpoint nested : (Stream nat)->(Stream nat) := [s:(Stream nat)](Cons O (nested (nested s))).


(* An inductive definition on a coinductive set *)

Fixpoint wrong_mapS [s:(Stream nat)] : (Stream nat) :=
     Cases s of 
	 (Cons n s1) => (Cons (S n) (wrong_mapS s1))
      end.

(* A Cofixpoint definition defining an infinite element of an inductive set *)

CoFixpoint u:nat := (S u).


(* A recursive call in a non-recursive argument of a constructor *)

Mutual CoInductive V : Prop := Consv : (A:Prop)A->(not A)->V.
(*
Definition V_is_false := 
    [x:V]<False>Case x of 
	            [A:Prop][a:A][h:(not A)](h a)
	        end.
*)
Definition V_is_false := 
    [x:V]<False>Cases x of 
	        (Consv _ a h) => (h a)
	        end.

CoFixpoint V_is_true : V := (Consv V  V_is_true V_is_false).


(* A sound definition which does not verfy the guarded condition *)

CoFixpoint good_from : (Stream nat) := (Cons O (mapS good_from)).

*)

(* Unfolding the definition of a stream *)


Theorem zeros_unfold : zeros = Cons 0 zeros.
apply (unfold_Stream zeros).
Qed.

End Examples.



Section Stream_Equalities. 

Variable A : Set.


(* The definition given in theories/Streams.v 
   is equivalent to require the elements at each position to be equal *)

Theorem Equiv1 :
 forall s1 s2 : Stream A,
 EqSt s1 s2 -> forall n : nat, Str_nth n s1 = Str_nth n s2.
unfold Str_nth in |- *.
fix u 4.
intros s1 s2 H n.
case H.
intros.
case n.
assumption.
intros.
simpl in |- *.
apply u.
assumption.
Qed.

Theorem Equiv2 :
 forall s1 s2 : Stream A,
 (forall n : nat, Str_nth n s1 = Str_nth n s2) -> EqSt s1 s2.
unfold Str_nth in |- *.
cofix u.
intros.
apply eqst.
apply (H 0).
apply u.
intros n.
apply (H (S n)).
Qed.

Section Example.

Variable f : A -> A.

CoFixpoint iter  : A -> Stream A := fun x : A => Cons (f x) (iter (f x)).

Lemma map_iter_eq : forall x : A, EqSt (iter (f x)) (map A A f (iter x)).
cofix u.
intros.
apply eqst.
trivial.
simpl in |- *.
apply u.
Qed.

End Example.


(* Extensional Equality between two streams (opus II) *)


CoInductive EqSt2 (A : Set) : Stream A -> Stream A -> Prop :=
    eqst2 :
      forall (s1 s2 : Stream A) (a : A),
      EqSt2 A s1 s2 -> EqSt2 A (Cons a s1) (Cons a s2).



(* The proof that this description  is equivalent to the one in the
   directory theories *)

(* The proof that EqSt2 is an equivalence relation *)


Theorem EqSt2_reflex : forall s : Stream A, EqSt2 A s s.
cofix u.
intros.
case s.
intros.
apply eqst2.
apply u.
Qed.


Theorem EqSt2_sym : forall s1 s2 : Stream A, EqSt2 A s1 s2 -> EqSt2 A s2 s1.
cofix u.
intros.
case H.
intros.
apply eqst2.
apply u.
assumption.
Qed.


Theorem EqSt2_trans :
 forall s1 s2 s3 : Stream A, EqSt2 A s1 s2 -> EqSt2 A s2 s3 -> EqSt2 A s1 s3.
cofix u.
intros s1 s2 s3.
intro.
inversion_clear H.
intro.
inversion_clear H.
apply eqst2.
apply (u s0 s4 s6).
assumption.
assumption.
Qed.


Definition derived_eqst (s1 s2 : Stream A) (a : A) 
  (H : EqSt s1 s2) : EqSt (Cons a s1) (Cons a s2) :=
  eqst (Cons a s1) (Cons a s2) (refl_equal (hd (Cons a s2))) H.


Definition derived_eqst2 (s1 s2 : Stream A) :
  hd s1 = hd s2 -> EqSt2 A (tl s1) (tl s2) -> EqSt2 A s1 s2 :=
  let (x, x0) as s
      return (hd s = hd s2 -> EqSt2 A (tl s) (tl s2) -> EqSt2 A s s2) :=
      s1 in
  (let (a, s) as s
       return
         (forall (a : A) (s0 : Stream A),
          hd (Cons a s0) = hd s ->
          EqSt2 A (tl (Cons a s0)) (tl s) -> EqSt2 A (Cons a s0) s) := s2 in
   fun (a0 : A) (s0 : Stream A) (H : hd (Cons a0 s0) = hd (Cons a s))
     (H0 : EqSt2 A (tl (Cons a0 s0)) (tl (Cons a s))) =>
   match H in (_ = a1) return (EqSt2 A (Cons a0 s0) (Cons a1 s)) with
   | refl_equal => eqst2 A s0 s a0 H0
   end) x x0.

End Stream_Equalities.

(* $Id$ *)
