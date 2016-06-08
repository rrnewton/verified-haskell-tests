module VerifyAnd where

import qualified Prelude

data AndState =
   Bot
 | TrueBot
 | BotTrue
 | TrueTrue
 | F

join :: AndState -> AndState -> AndState
join a b =
  case a of {
   Bot -> b;
   TrueBot ->
    case b of {
     Bot -> a;
     BotTrue -> TrueTrue;
     x -> x};
   BotTrue ->
    case b of {
     Bot -> a;
     TrueBot -> TrueTrue;
     x -> x};
   TrueTrue ->
    case b of {
     Bot -> a;
     F -> F;
     _ -> TrueTrue};
   F -> F}

