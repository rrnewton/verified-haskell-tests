Require Import Bool Arith List.
Require Import Coq.Classes.Init.

Check eqb.

Set Implicit Arguments.

Inductive OneBool := Bot | T | F .

Inductive andState := Live (leftbit : OneBool) (rightbit : OneBool)
                    | TopErr .

(* TODO: use the nice interfaces in MathClasses, e.g. JoinSemiLattice *)
Definition bottom : andState := Live Bot Bot. 

(* Egad, there must be some way to derive this. *)
Definition eqo (a : OneBool) (b : OneBool) : bool := 
  match (a,b) with 
  | (Bot,Bot) => true
  | (T,T) => true
  | (F,F) => true
  | _     => false
  end. 

Definition eqa (a : andState) (b : andState) : bool :=
  match (a,b) with
  | (Live a b, Live c d) => andb (eqo a c) (eqo b d)
  | (TopErr,TopErr) => true
  | _ => false
  end.  


(* Define our partial order *)

(* Inductive leqo  (a : OneBool) : OneBool -> Prop :=  *)
(*   | leqo_refl : leqo a a  *)
(*   | leqo_bot  : forall x:OneBool, a = Bot -> leqo a x *)
(*   . *)

(* Definition leo (a : OneBool) (b: OneBool) : Prop :=  *)
(*   match (a,b) with *)
(*   | (Bot,T) => True *)
(*   | (Bot,F) => True *)
(*   | _       => False *)
(*   end.  *)

Definition leqo (a : OneBool) (b: OneBool) : Prop := 
  match (a,b) with
  | (Bot,_) => True
  | (F,F)   => True
  | (T,T)   => True
  | _       => False
  end. 

Definition leqa (a : andState) (b: andState) : Prop := 
  match (a,b) with
  | (Live a b, Live c d) => leqo a c /\ leqo b d
  | (Live _ _, TopErr)   => True
  | _                    => False
  end. 

Example foo: (leqa (Live Bot Bot) TopErr) = True. 
Proof. reflexivity. Qed.

(******************************************************************************)

Definition joinB (a : OneBool) (b : OneBool) : option OneBool :=
  match (a,b) with
  | (Bot, b) => Some b
  | (F, T) => None
  (* Reflexive cases *)
  | (F, F) => Some F
  | (T, T) => Some F
  (* | _  => if a = b then None else None  *)
  (* | _      => joinB b a *)
  (* Manually writing out flipped *)
  | (T, F)   => None
  | (a, Bot) => Some a
  end.

Eval compute in joinB F T . 

Definition join (a : andState) (b : andState) : andState :=
  match (a,b) with
  | (Live a b, Live c d) => 
    match (joinB a c, joinB b d) with
    | (Some x, Some y) => Live x y 
    | _                => TopErr
    end
  | _  => TopErr
  end.

(* Definition joinLeq (a : andState) (b : andState) : bool := *)
(*   match (join a b) = b with *)
(*   | _  => true *)
(*   end. *)

Definition joinLeq (a : andState) (b : andState) : Prop :=
  match (join a b) = b with
  | _  => (1=1)
  end.

Definition readAnd (a : andState) : option OneBool :=
  match a with
  | (Live F _) => Some F
  | (Live _ F) => Some F
  | (Live T T) => Some T
  | (Live Bot _) => Some Bot
  | (Live _ Bot) => Some Bot
  | TopErr       => None 
  end. 

(* SearchRewrite ((_ ++ _) ++ _).  *)

Check (readAnd (Live F F)).
Eval compute in  (readAnd (Live F F)).
Eval compute in (fst (3,5)).

(* SearchAbout bottom. *)

Check le.


(* I need to learn how to state a general property for getters. (type class?) *)
Theorem readAnd_validGetter1: 
  forall (a b : andState), 
    (leqa a b) -> (readAnd b = Some Bot -> readAnd a = Some Bot)
    (* ((leqa a b) /\ readAnd b = Some Bot) -> readAnd a = Some Bot *)
. 
Proof.
(* Could crush do this ?? *)

(* intros a.  destruct a. *)
intros a b.
induction a; induction b; auto.

  induction leftbit; induction rightbit; induction leftbit0; induction rightbit0; 
  unfold readAnd; auto;
  (* But we hit impossible cases.. *)
  unfold leqa; unfold leqo; intros; elim H; inversion H; elim H2.
  (* 10 subgoals.  Ugh the False var was the other one: *)
  elim H1. elim H1. elim H1. elim H1. elim H1. elim H1. elim H1. elim H1.

(* Down to the last two, which are old splits from our first 2 inductions above.*)
  induction leftbit; induction rightbit; unfold readAnd; unfold leqa; auto;
  intro; intro; elim H0; inversion H0.

(* Now the very last top-level case. *)
  induction leftbit; induction rightbit; unfold readAnd; unfold leqa; auto;
  intro; inversion H.
Qed.


Theorem readAnd_validGetter2: 
  forall (a b : andState), 
    (leqa a b) -> (not (readAnd a = Some Bot) -> (readAnd b = readAnd a \/ readAnd b = None))
    (* ((leqa a b) /\ readAnd b = Some Bot) -> readAnd a = Some Bot *)
. 
Proof.
induction a; induction b; auto.

  induction leftbit; induction rightbit; induction leftbit0; induction rightbit0; 
  unfold readAnd; auto;
  unfold leqa; unfold leqo; intros; elim H0; auto.

  (* This leaves a bunch that fail in the other way (True & False on top) *)
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.  (* 24 left ... *)
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H1.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H2.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.
  elim H; intros; inversion H1.

(* Back to a top-level case *)
  unfold leqa; unfold leqo; intros; inversion H.
Qed.

(* TOFIX
  Use match goal with...
    | [ H : _ |- _ ] => inversion H; fail
 *)
  
Extraction Language Haskell.
Extraction "VAsyncAnd.hs" join readAnd.
