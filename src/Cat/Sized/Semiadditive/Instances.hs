{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Semiadditive.Instances
  (
  ) where

import Cat.Sized.Semiadditive.Class (Semiadditive)

import Cat.Sized.Semicartesian.Instances   ()
import Cat.Sized.Semicocartesian.Instances ()

import Cat.Sized.Profunctor
  ( SizedPro
  )

import Data.Vector.Sized qualified as VS
import Cat.Orthotope
  (R1)


instance Semiadditive VS.Vector (SizedPro (->))
instance Semiadditive R1        (SizedPro (->))
