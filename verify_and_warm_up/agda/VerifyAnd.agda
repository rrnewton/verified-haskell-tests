

module VerifyAnd where

-- open import 

data Bool : Set where
  true : Bool
  false : Bool

data AndState : Set where
  Bot      : AndState
  TrueBot  : AndState
  BotTrue  : AndState
  TrueTrue : AndState
  F        : AndState

-- total
myjoin : AndState -> AndState -> AndState
-- Manually writing out reflexive cases too:
myjoin TrueBot  TrueBot  = TrueBot
myjoin BotTrue  BotTrue  = BotTrue 
myjoin TrueTrue TrueTrue = TrueTrue
---------------------------
myjoin TrueBot BotTrue = TrueTrue
myjoin TrueTrue TrueBot = TrueTrue
myjoin TrueTrue BotTrue = TrueTrue
myjoin Bot x = x
myjoin F  _  = F
---------------------------
myjoin x y = myjoin y x -- Yay, this works!

-- myjoin BotTrue TrueBot = TrueTrue
-- myjoin TrueBot TrueTrue  = TrueTrue
-- myjoin BotTrue TrueTrue  = TrueTrue
-- myjoin x Bot = x
-- myjoin _  F  = F

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

-- A single "-c" in the hole and then auto invocation ("C-c C-a") filled this in exhaustively:
myjoin_commutative : {a b : AndState} -> (myjoin a b) == (myjoin b a)
myjoin_commutative {Bot} {Bot} = refl
myjoin_commutative {Bot} {TrueBot} = refl
myjoin_commutative {Bot} {BotTrue} = refl
myjoin_commutative {Bot} {TrueTrue} = refl
myjoin_commutative {Bot} {F} = refl
myjoin_commutative {TrueBot} {Bot} = refl
myjoin_commutative {TrueBot} {TrueBot} = refl
myjoin_commutative {TrueBot} {BotTrue} = refl
myjoin_commutative {TrueBot} {TrueTrue} = refl
myjoin_commutative {TrueBot} {F} = refl
myjoin_commutative {BotTrue} {Bot} = refl
myjoin_commutative {BotTrue} {TrueBot} = refl
myjoin_commutative {BotTrue} {BotTrue} = refl
myjoin_commutative {BotTrue} {TrueTrue} = refl
myjoin_commutative {BotTrue} {F} = refl
myjoin_commutative {TrueTrue} {Bot} = refl
myjoin_commutative {TrueTrue} {TrueBot} = refl
myjoin_commutative {TrueTrue} {BotTrue} = refl
myjoin_commutative {TrueTrue} {TrueTrue} = refl
myjoin_commutative {TrueTrue} {F} = refl
myjoin_commutative {F} {Bot} = refl
myjoin_commutative {F} {TrueBot} = refl
myjoin_commutative {F} {BotTrue} = refl
myjoin_commutative {F} {TrueTrue} = refl
myjoin_commutative {F} {F} = refl

-- Same here:
myjoin_idempotent : {a b : AndState} -> myjoin a (myjoin a b) == myjoin a b
myjoin_idempotent {Bot} = refl
myjoin_idempotent {TrueBot} {Bot} = refl
myjoin_idempotent {TrueBot} {TrueBot} = refl
myjoin_idempotent {TrueBot} {BotTrue} = refl
myjoin_idempotent {TrueBot} {TrueTrue} = refl
myjoin_idempotent {TrueBot} {F} = refl
myjoin_idempotent {BotTrue} {Bot} = refl
myjoin_idempotent {BotTrue} {TrueBot} = refl
myjoin_idempotent {BotTrue} {BotTrue} = refl
myjoin_idempotent {BotTrue} {TrueTrue} = refl
myjoin_idempotent {BotTrue} {F} = refl
myjoin_idempotent {TrueTrue} {Bot} = refl
myjoin_idempotent {TrueTrue} {TrueBot} = refl
myjoin_idempotent {TrueTrue} {BotTrue} = refl
myjoin_idempotent {TrueTrue} {TrueTrue} = refl
myjoin_idempotent {TrueTrue} {F} = refl
myjoin_idempotent {F} = refl


-- And here:
myjoin_associative : {a b c : AndState} -> myjoin a (myjoin b c) == myjoin (myjoin a b) c
myjoin_associative {Bot} = refl
myjoin_associative {TrueBot} {Bot} = refl
myjoin_associative {TrueBot} {TrueBot} {Bot} = refl
myjoin_associative {TrueBot} {TrueBot} {TrueBot} = refl
myjoin_associative {TrueBot} {TrueBot} {BotTrue} = refl
myjoin_associative {TrueBot} {TrueBot} {TrueTrue} = refl
myjoin_associative {TrueBot} {TrueBot} {F} = refl
myjoin_associative {TrueBot} {BotTrue} {Bot} = refl
myjoin_associative {TrueBot} {BotTrue} {TrueBot} = refl
myjoin_associative {TrueBot} {BotTrue} {BotTrue} = refl
myjoin_associative {TrueBot} {BotTrue} {TrueTrue} = refl
myjoin_associative {TrueBot} {BotTrue} {F} = refl
myjoin_associative {TrueBot} {TrueTrue} {Bot} = refl
myjoin_associative {TrueBot} {TrueTrue} {TrueBot} = refl
myjoin_associative {TrueBot} {TrueTrue} {BotTrue} = refl
myjoin_associative {TrueBot} {TrueTrue} {TrueTrue} = refl
myjoin_associative {TrueBot} {TrueTrue} {F} = refl
myjoin_associative {TrueBot} {F} = refl
myjoin_associative {BotTrue} {Bot} = refl
myjoin_associative {BotTrue} {TrueBot} {Bot} = refl
myjoin_associative {BotTrue} {TrueBot} {TrueBot} = refl
myjoin_associative {BotTrue} {TrueBot} {BotTrue} = refl
myjoin_associative {BotTrue} {TrueBot} {TrueTrue} = refl
myjoin_associative {BotTrue} {TrueBot} {F} = refl
myjoin_associative {BotTrue} {BotTrue} {Bot} = refl
myjoin_associative {BotTrue} {BotTrue} {TrueBot} = refl
myjoin_associative {BotTrue} {BotTrue} {BotTrue} = refl
myjoin_associative {BotTrue} {BotTrue} {TrueTrue} = refl
myjoin_associative {BotTrue} {BotTrue} {F} = refl
myjoin_associative {BotTrue} {TrueTrue} {Bot} = refl
myjoin_associative {BotTrue} {TrueTrue} {TrueBot} = refl
myjoin_associative {BotTrue} {TrueTrue} {BotTrue} = refl
myjoin_associative {BotTrue} {TrueTrue} {TrueTrue} = refl
myjoin_associative {BotTrue} {TrueTrue} {F} = refl
myjoin_associative {BotTrue} {F} = refl
myjoin_associative {TrueTrue} {Bot} = refl
myjoin_associative {TrueTrue} {TrueBot} {Bot} = refl
myjoin_associative {TrueTrue} {TrueBot} {TrueBot} = refl
myjoin_associative {TrueTrue} {TrueBot} {BotTrue} = refl
myjoin_associative {TrueTrue} {TrueBot} {TrueTrue} = refl
myjoin_associative {TrueTrue} {TrueBot} {F} = refl
myjoin_associative {TrueTrue} {BotTrue} {Bot} = refl
myjoin_associative {TrueTrue} {BotTrue} {TrueBot} = refl
myjoin_associative {TrueTrue} {BotTrue} {BotTrue} = refl
myjoin_associative {TrueTrue} {BotTrue} {TrueTrue} = refl
myjoin_associative {TrueTrue} {BotTrue} {F} = refl
myjoin_associative {TrueTrue} {TrueTrue} {Bot} = refl
myjoin_associative {TrueTrue} {TrueTrue} {TrueBot} = refl
myjoin_associative {TrueTrue} {TrueTrue} {BotTrue} = refl
myjoin_associative {TrueTrue} {TrueTrue} {TrueTrue} = refl
myjoin_associative {TrueTrue} {TrueTrue} {F} = refl
myjoin_associative {TrueTrue} {F} = refl
myjoin_associative {F} = refl 


--------------------------------------------------------------------------------

