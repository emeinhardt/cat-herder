{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Unsized.Semigroupoid.Instances
  (
  ) where

import Prelude hiding  ((.))
import Prelude.Unicode ((∘))


import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid ((.)) )


instance Semigroupoid (->) where
  (.) = (∘)
