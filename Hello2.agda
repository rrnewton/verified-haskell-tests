module Hello2 where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

{-# IMPORT Data.Text.IO #-}

postulate putStr : String -> IO ⊤
{-# COMPILED putStr Data.Text.IO.putStr #-}

main : IO ⊤
main = putStr "Hello World!"
