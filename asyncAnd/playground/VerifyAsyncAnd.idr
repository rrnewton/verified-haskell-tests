
data OneBool = Bot | T | F
data AndState = Live OneBool OneBool | TopErr   

instance Eq OneBool where
  Bot == Bot = True
  T == T = True
  F == F = True
  _ == _ = False

instance Eq AndState where
  (Live a b) == (Live c d)  = a == b && c == d
  TopErr == TopErr = True
  _ == _ = False

total
join2 : OneBool -> OneBool -> Maybe OneBool
join2 T T = Just T
join2 F F = Just F
join2 T F = Nothing
join2 F T = Nothing
join2 Bot y = Just y
join2 x Bot = Just x
join2 F y   = Just F

instance JoinSemilattice AndState where
  join (Live a b) (Live c d) =
    case (join2 a c, join2 b d) of
      (Just x, Just y) => Live x y
      _                => TopErr
  join _ _ = TopErr

instance BoundedJoinSemilattice AndState where
  bottom = Live Bot Bot

-- Returns True only if one element is under the other in the lattice.
-- If it is above OR is unrelated (remember, partial order), it
-- returns False.
joinLeq : (Eq a, JoinSemilattice a) => a -> a -> Bool
joinLeq a b = (join a b) == b

readAnd : AndState -> Maybe OneBool
readAnd (Live F _)   = Just F
readAnd (Live _ F)   = Just F
readAnd (Live T T)   = Just T
readAnd (Live Bot _) = Just Bot
readAnd (Live _ Bot) = Just Bot
readAnd TopErr       = Nothing

----------------------------------------
-- To Prove:
----------------------------------------

-- (1) These instances:
-- instance VerifiedJoinSemilattice AndState  where
-- instance VerifiedBoundedJoinSemilattice AndState where

-- (2) readAnd is a valid monotonic getter:

-- total
readAnd_validGetter1 : (a:AndState) -> (b:AndState) ->
                       (joinLeq a b = True) -> 
                       (readAnd b = Just Bot) -> 
                       (readAnd a = Just Bot)
readAnd_validGetter1 TopErr TopErr = ?finishme1

not_ : Type -> Type 
not_ a = (a -> _|_)

-- Where in the standard lib do we get negation and boolean or for proof's propositions (Type):
--
readAnd_validGetter2 : (a:AndState) -> (b:AndState) ->
                       (joinLeq a b = True) -> 
                       (not_ (readAnd a = Just Bot)) ->
                       (Either (readAnd b = Just Bot) (readAnd b = Nothing))
readAnd_validGetter2 a b = ?finishme2
