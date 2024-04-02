{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Factors where

import Snarkl.Language.Prelude
import Prelude (($))

factors :: Comp 'TField k
factors = do
  a <- fresh_public_input
  b <- fresh_public_input
  c <- fresh_public_input
  return $ a * b * c