
-- file IdAgda.agda
module IdAgda where

idAgda : {A : Set} → A → A
idAgda x = x

{-# COMPILED_EXPORT idAgda idAgda #-}
