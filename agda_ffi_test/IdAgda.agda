
-- file IdAgda.agda
module IdAgda where

open import Agda.Builtin.String
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

idAgda : {A : Set} → A → A
idAgda x = x

{-# COMPILED_EXPORT idAgda idAgda #-}

add1 : Int → Int
add1 (pos x) = pos (x + 1)
add1 (negsuc 0) = pos 0 
add1 (negsuc x) = negsuc (x - 1)

{-# COMPILED_EXPORT add1 add1 #-}

add2 : Nat → Nat
add2 x = suc (suc x)

{-# COMPILED_EXPORT add2 add2 #-}

showInt : Int → String
showInt x = primShowInteger x

{-# COMPILED_EXPORT showInt showInt #-}

data AndState : Set where
  Bot      : AndState
  TrueBot  : AndState
  BotTrue  : AndState
  TrueTrue : AndState
  F        : AndState


-- This could be automated by a preprocessor:
{-# HASKELL

data AndState = Bot  | TrueBot | BotTrue | TrueTrue | F
  deriving Show

-- TODO: Data.Semigroup.Semigroup parent class:
class VerifiedSemiGroup a where

class Monoid a => VerifiedMonoid a where

instance Monoid AndState where
  mappend = joinStates
  mempty = Bot

#-}

{-# COMPILED_DATA AndState AndState Bot TrueBot BotTrue TrueTrue F #-}

joinStates : AndState -> AndState -> AndState
-- Manually writing out reflexive cases too:
joinStates TrueBot  TrueBot  = TrueBot
joinStates BotTrue  BotTrue  = BotTrue 
joinStates TrueTrue TrueTrue = TrueTrue
---------------------------
joinStates TrueBot BotTrue = TrueTrue
joinStates TrueTrue TrueBot = TrueTrue
joinStates TrueTrue BotTrue = TrueTrue
joinStates Bot x = x
joinStates F  _  = F
---------------------------
-- joinStates x y = joinStates y x -- Yay, this works!
 -- [2016.06.08] Nope, in 2.4.2.3 termination checking fails here.

-- Here we manually spell it out:
joinStates BotTrue TrueBot   = TrueTrue
joinStates TrueBot TrueTrue  = TrueTrue
joinStates BotTrue TrueTrue  = TrueTrue
joinStates x Bot = x
joinStates _  F  = F

{-# COMPILED_EXPORT joinStates joinStates #-}

x : AndState
x = joinStates BotTrue TrueTrue

{-# COMPILED_EXPORT x example #-}

-- If we had explicit quasiquotation of Haskell we could make a function
-- that takes a proof of associativity and returns a Haskell code snippet
-- containing "instance VerifiedSemiGroup".

data HaskellSnip : Set where
  DoesntExist : HaskellSnip

-- genAssoc : { f : AndState → AndState }
--          → { a b c : AndState }
--          → ((f a (f b c)) ‌≡ (f (f a b) c)) → HaskellSnip
-- genAssoc = ?


-- assoc : { a b c : AndState }
--       → joinStates a (joinStates b c)) ‌≡ (joinStates (joinStates a b) c)
-- assoc = ?

-- associative : {a b c : AndState} -> joinStates a (joinStates b c) ≡ joinStates (joinStates a b) c
-- associative = ?


joinStates_commutative : {a b : AndState} -> (joinStates a b) ≡ (joinStates b a)
joinStates_commutative {Bot} {Bot} = refl
joinStates_commutative {Bot} {TrueBot} = refl
joinStates_commutative {Bot} {BotTrue} = refl
joinStates_commutative {Bot} {TrueTrue} = refl
joinStates_commutative {Bot} {F} = refl
joinStates_commutative {TrueBot} {Bot} = refl
joinStates_commutative {TrueBot} {TrueBot} = refl
joinStates_commutative {TrueBot} {BotTrue} = refl
joinStates_commutative {TrueBot} {TrueTrue} = refl
joinStates_commutative {TrueBot} {F} = refl
joinStates_commutative {BotTrue} {Bot} = refl
joinStates_commutative {BotTrue} {TrueBot} = refl
joinStates_commutative {BotTrue} {BotTrue} = refl
joinStates_commutative {BotTrue} {TrueTrue} = refl
joinStates_commutative {BotTrue} {F} = refl
joinStates_commutative {TrueTrue} {Bot} = refl
joinStates_commutative {TrueTrue} {TrueBot} = refl
joinStates_commutative {TrueTrue} {BotTrue} = refl
joinStates_commutative {TrueTrue} {TrueTrue} = refl
joinStates_commutative {TrueTrue} {F} = refl
joinStates_commutative {F} {Bot} = refl
joinStates_commutative {F} {TrueBot} = refl
joinStates_commutative {F} {BotTrue} = refl
joinStates_commutative {F} {TrueTrue} = refl
joinStates_commutative {F} {F} = refl

