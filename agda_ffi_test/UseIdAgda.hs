-- module UseIdAgda where
module Main where

import MAlonzo.Code.IdAgda 

-- idAgda :: () → a → a

idAgdaApplied :: a -> a
idAgdaApplied = idAgda ()

main =
  do print (idAgdaApplied 3)
     print (joinStates BotTrue TrueTrue)
     print example
