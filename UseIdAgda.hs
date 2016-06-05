-- module UseIdAgda where
module Main where

import MAlonzo.Code.IdAgda (idAgda)

-- idAgda :: () → a → a

idAgdaApplied :: a -> a
idAgdaApplied = idAgda ()

main = print (idAgdaApplied 3)
