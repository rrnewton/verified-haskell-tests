{-# LANGUAGE FlexibleInstances #-}

import Data.Maybe
import Data.LVar.Internal.Pure (verifyFiniteJoin, verifyFiniteGet)
import Algebra.Lattice
--------------------------------------------------------------------------------

-- A proper lattice for asyncAnd must track all T/F combinations and requires a more
-- general notion of thresholded read.  (It can't use the simple
-- incompatible-query-set mechanism.)

data AndState = Live OneBool OneBool | TopErr   deriving (Show,Eq)
data OneBool = Bot | T | F                      deriving (Show,Ord,Eq,Enum,Bounded)

instance JoinSemiLattice AndState where
  join = joinA
  
instance Ord AndState where
  compare a b | a == b = EQ
              | joinLeq a b = LT
              | otherwise   = GT
  
instance Enum AndState where
  fromEnum (Live Bot Bot) = 0
  fromEnum (Live Bot T)   = 1
  fromEnum (Live Bot F)   = 2
  fromEnum (Live T   Bot) = 3
  fromEnum (Live T   T)   = 4
  fromEnum (Live T   F)   = 5      
  fromEnum (Live F   Bot) = 6
  fromEnum (Live F   T)   = 7
  fromEnum (Live F   F)   = 8
  fromEnum TopErr         = 9
  toEnum 0 = (Live Bot Bot)
  toEnum 1 = (Live Bot T)   
  toEnum 2 = (Live Bot F)   
  toEnum 3 = (Live T   Bot) 
  toEnum 4 = (Live T   T)   
  toEnum 5 = (Live T   F)   
  toEnum 6 = (Live F   Bot) 
  toEnum 7 = (Live F   T)   
  toEnum 8 = (Live F   F)   
  toEnum 9 = TopErr         

instance Bounded AndState where
  minBound = toEnum 0
  maxBound = toEnum 9

--------------------------------------------------------------------------------

joinB :: OneBool -> OneBool -> Maybe OneBool
joinB x y | x == y = Just x
joinB Bot x = Just x
joinB T F = Nothing
joinB x y = joinB y x

joinA :: AndState -> AndState -> AndState
joinA (Live a b) (Live c d) = fromMaybe TopErr $ do
  x <- joinB a c
  y <- joinB b d
  return (Live x y)
joinA _ _  = TopErr

-- Here's a thresholded read.  It's safe.
-- 
-- It meet the criteria that it stays bottom until a single transition point, and its
-- value is constant thereafter.
--
-- Note: using Nothing to represent bottom here.
readAnd :: AndState -> Maybe OneBool
readAnd (Live F _) = Just F
readAnd (Live _ F) = Just F
readAnd (Live T T) = Just T
readAnd TopErr     = Nothing
readAnd _          = Just Bot

instance JoinSemiLattice (Maybe OneBool) where
  join (Just x) (Just y) = joinB x y
  join _ _ = Nothing
  
instance BoundedJoinSemiLattice (Maybe OneBool) where  
  bottom = Just Bot
  -- Top is Nothing

--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "Verifying joinA function:"
  print$ verifyFiniteJoin [minBound..maxBound] joinA
  putStrLn "Verifying joinA function:"  
--  print$ verifyFiniteGet [minBound..maxBound] (Live Bot Bot, TopErr) readAnd
  print$ verifyFiniteGet [minBound..maxBound] (bottom, Nothing) readAnd
  putStrLn "Done."  
