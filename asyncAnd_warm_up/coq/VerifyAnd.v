(* Require Import Bool Arith List.*)
  (* Crush *)
Set Implicit Arguments.

Inductive andState := Bot | TrueBot | BotTrue | TrueTrue | F.

Definition join (a : andState) (b : andState) : andState :=
  (* if a = b then a else *) 
  match (a,b) with
   | (TrueBot, BotTrue) => TrueTrue
   | (TrueTrue, TrueBot) => TrueTrue
   | (TrueTrue, BotTrue) => TrueTrue
   | (Bot, x) => x
   | (F, _) => F
   (* Flipped args ... *)
   | (BotTrue, TrueBot) => TrueTrue
   | (TrueBot, TrueTrue) => TrueTrue
   | (BotTrue, TrueTrue) => TrueTrue
   | (x, Bot) => x
   | (_, F) => F
   (* Reflexive boilerplate... *)
   | (TrueBot, TrueBot) => TrueBot
   | (BotTrue, BotTrue) => BotTrue
   | (TrueTrue, TrueTrue) => TrueTrue
  end.


Theorem join_commutative : forall a b, join a b = join b a .
  intros.
  induction a;
  induction b; (* Blow up all 25 subgoals. *)
  (* crush. *) (* Turns out to be unnecessary. *)
  auto. 
Qed.

Theorem join_idempotent : forall a b, join a (join a b) = join a b .
  intros.
  induction a;
  induction b; (* Blow up all 25 subgoals. *)
  auto. 
Qed.

Theorem join_associative : forall a b c, join a (join b c) = join (join a b) c .
  intros.
  induction a;
  induction b; 
  induction c; (* 125 subgoals *)
  auto.
Qed.

(* This couldn't be easier: *)
Extraction Language Haskell.
Extraction "VerifyAnd.hs" join.
