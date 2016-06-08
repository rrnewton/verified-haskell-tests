
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
