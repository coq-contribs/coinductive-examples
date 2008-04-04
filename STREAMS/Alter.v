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
(*                                Coq V5.10                                 *)
(*                              Nov 29th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Alter.v                                   *)
(****************************************************************************)




Section Alter_I.

(*****************************************************************)
(* A proof of the extensional equality of two different versions *)
(* of the stream that infinitely alternates the values true and  *)
(* false, using F. Leclerc and C. Paulin representation.         *)
(*****************************************************************)


Require Import Bool.

Inductive St : Set :=
    build : forall X : Set, (X -> bool * X) -> X -> St.
(*
Definition hd := 
  [H:St]
 <[_:St]bool>Case H of
    ([X:Set][p:X->bool*X][y:X](fst bool X (p y)))
    end.
*)
Definition hd (H : St) := match H with
                          | build X p y => fst (p y)
                          end.

(*
Definition tl := 
[H:St]
 <[_:St]St>Case H of
    ([X:Set][p:X->bool*X][y:X](build X p (snd bool X (p y))))
    end.
*)

Definition tl (H : St) :=
  match H with
  | build X p y => build X p (snd (p y))
  end.

(* The quality between streams is the gfp of this operator T *)

Definition T (R : St -> St -> Prop) (z1 z2 : St) :=
  hd z1 = hd z2 /\ R (tl z1) (tl z2).

Inductive EqSt : St -> St -> Prop :=
    buildeq :
      forall R : St -> St -> Prop,
      (forall x y : St, R x y -> T R x y) ->
      forall s1 s2 : St, R s1 s2 -> EqSt s1 s2.

(* Two process generating the same stream *)

Let gen1 := build bool (fun b : bool => pair b (negb b)).
Let gen2 := build bool (fun b : bool => pair (negb b) (negb b)).

Let alter1 := gen1 true.
Let alter2 := gen2 false.

(* An invariant relation in the generation *)

Definition Invariant (s1 s2 : St) :=
  exists b : bool, s1 = gen1 (negb b) /\ s2 = gen2 b.

(* The proof that both processes generate the same stream *)

Theorem eqalters_I : EqSt alter1 alter2.
apply (buildeq Invariant).

intros.
case H.
intros.
case H0.
intros.
rewrite H1; rewrite H2.
simpl in |- *.
split.
trivial.
unfold Invariant in |- *.
exists (negb x0).
unfold gen1 in |- *.
unfold gen2 in |- *.
split.
trivial.
trivial.

unfold Invariant in |- *.
exists false.
split.
trivial.
trivial.
Qed. 

(* An easier way of definig the same invariant relation presented above *)

Inductive SimplerInvariant : St -> St -> Prop :=
    makeinv : forall b : bool, SimplerInvariant (gen1 (negb b)) (gen2 b).

Theorem eqalters_I_bis : EqSt alter1 alter2.
apply (buildeq SimplerInvariant).
intros.
case H.
unfold T in |- *.
intros.
split.
trivial.
apply (makeinv (negb b)).
apply (makeinv false).
Qed. 

(***********************************************************************)
(*  A different proof using the method of translation described in the *) 
(*  paper "Codifying guarded definitions with recursive schemes"       *)
(***********************************************************************)


(* The invariant relation *)

Inductive Cls : St -> St -> Prop :=
    cls : Cls alter1 alter2.

Inductive EqSt1 : St -> St -> Prop :=
    eqst1 :
      forall z1 z2 : St,
      hd z1 = hd z2 ->
      Cls (tl z1) (tl z2) \/ EqSt1 (tl z1) (tl z2) -> EqSt1 z1 z2.


(* The streams alter1 and alter2 verify the relation EqSt1 *)

Lemma eqalters_body : EqSt1 alter1 alter2.
apply eqst1.
trivial.
right.
apply eqst1.
trivial.
left.
apply cls.
Qed.


(* EqSt1 is a  bisimulation *)

Lemma H : forall z1 z2 : St, EqSt1 z1 z2 -> T EqSt1 z1 z2. 
intros z1 z2 x.
red in |- *.
case x.
intros z3 z4 H0 H1.
split.
assumption.
case H1.
intro H2.
case H2.
apply eqalters_body.
intros.
assumption.
Qed. 

(* The proof of the extensional equality of alter1 and alter2 *)

Theorem eqalters_II : EqSt alter1 alter2.
apply (buildeq EqSt1 H).
apply eqalters_body.
Qed.


End Alter_I.


Section Alter_II. 
(* The same proof but using the new co-inductive types  *)

Require Import Streams.

CoFixpoint gen1  : bool -> Stream bool :=
  fun b : bool => Cons b (gen1 (negb b)).

CoFixpoint gen2  : bool -> Stream bool :=
  fun b : bool => Cons (negb b) (gen2 (negb b)).

Let alter1 := gen1 false.
Let alter2 := gen2 true.


Theorem eqalters_III : EqSt alter1 alter2.
cofix u.
apply eqst.
trivial.
apply eqst.
trivial.
assumption.
Qed.

End Alter_II.

