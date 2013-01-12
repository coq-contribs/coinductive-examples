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

Set Asymmetric Patterns.

Section Specified_Streams. (* The set of Specified Streams : definition *)

CoInductive SStream (A : Set) : (nat -> A -> Prop) -> Set :=
    scons :
      forall (P : nat -> A -> Prop) (a : A),
      P 0 a -> SStream A (fun n : nat => P (S n)) -> SStream A P.

Variable A : Set.

Definition shd (P : nat -> A -> Prop) (x : SStream A P) :=
  match x with
  | scons _ a _ _ => a
  end.

Definition stl (P : nat -> A -> Prop) (x : SStream A P) :=
  match x in (SStream _ P) return (SStream A (fun n : nat => P (S n))) with
  | scons _ _ _ s => s
  end.


Fixpoint snth (n : nat) : forall P : nat -> A -> Prop, SStream A P -> A :=
  fun (P : nat -> A -> Prop) (s : SStream A P) =>
  match n with
  | O => shd P s
  | S m => snth m (fun n : nat => P (S n)) (stl P s)
  end.

End Specified_Streams.
