{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Zero.Instances
  (
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zipWith
  )
import Prelude.Unicode ((∘))


import Cat.Sized.Semigroupoid.Class
  ( Sized (Sized)
  )
import Cat.Sized.Monoidal.Instances ()
import Cat.Sized.Zero.Class

import Cat.Orthotope
  ( R1
  )

import Data.Vector.Sized qualified as VS



instance HasZero VS.Vector (Sized (->)) where
  pointer = Sized ∘ const


instance HasZero R1 (Sized (->)) where
  pointer = Sized ∘ const
