
-- file IdAgda.agda
module IdAgda where

open import Agda.Builtin.String
open import Agda.Builtin.Int
open import Agda.Builtin.Nat

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

{-# HASKELL
data AndState = Bot  | TrueBot | BotTrue | TrueTrue | F
  deriving Show 
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
