-- module UseIdAgda where
module Main where

import MAlonzo.Code.IdAgda 

idAgdaApplied :: a -> a
idAgdaApplied = idAgda ()

main =
  do print (idAgdaApplied 3)
     print (joinStates BotTrue TrueTrue)
     print example
     print (TrueTrue `mappend` F `mappend` mempty)
