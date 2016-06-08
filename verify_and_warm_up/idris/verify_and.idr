

data AndState = Bot | TrueBot | BotTrue | TrueTrue | F
  -- How do we derive Ord?

total
myjoin : AndState -> AndState -> AndState
myjoin TrueBot BotTrue = TrueTrue
myjoin TrueTrue TrueBot = TrueTrue
myjoin TrueTrue BotTrue = TrueTrue
myjoin Bot x = x
myjoin F  _  = F
-- myjoin x y = myjoin y x
-- Manuallly writing all these out for the totality/termination checker:
myjoin BotTrue TrueBot = TrueTrue
myjoin TrueBot TrueTrue  = TrueTrue
myjoin BotTrue TrueTrue  = TrueTrue
myjoin x Bot = x
myjoin _  F  = F
-- Manually writing out reflexive cases too:
myjoin TrueBot  TrueBot  = TrueBot
myjoin BotTrue  BotTrue  = BotTrue 
myjoin TrueTrue TrueTrue = TrueTrue

-- The new :casesplit! command helps with this, but I couldn't figure
-- out how to split both, so it required 6 invoctations to generate
-- these 25 cases.
comm : (a:AndState) -> (b:AndState) -> (myjoin a b = myjoin b a)
comm Bot Bot = proof trivial
comm Bot TrueBot = proof trivial
comm Bot BotTrue = proof trivial
comm Bot TrueTrue = proof trivial
comm Bot F = proof trivial
comm TrueBot Bot = proof trivial
comm TrueBot TrueBot = proof trivial
comm TrueBot BotTrue = proof trivial
comm TrueBot TrueTrue = proof trivial
comm TrueBot F = proof trivial
comm BotTrue Bot = proof trivial
comm BotTrue TrueBot = proof trivial
comm BotTrue BotTrue = proof trivial
comm BotTrue TrueTrue = proof trivial
comm BotTrue F = proof trivial
comm TrueTrue Bot = proof trivial
comm TrueTrue TrueBot = proof trivial
comm TrueTrue BotTrue = proof trivial
comm TrueTrue TrueTrue = proof trivial
comm TrueTrue F = proof trivial
comm F Bot = proof trivial
comm F TrueBot = proof trivial
comm F BotTrue = proof trivial
comm F TrueTrue = proof trivial
comm F F = proof trivial


---------- Proofs ----------


