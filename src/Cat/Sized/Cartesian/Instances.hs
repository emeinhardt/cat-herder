{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Cartesian.Instances
  (
  ) where

import Cat.Sized.Semigroupoid.Class (Sized)
import Cat.Sized.Cartesian.Class    (Cartesian)

import Cat.Sized.Semigroupoid.Instances  ()
import Cat.Sized.Category.Instances      ()
import Cat.Sized.Monoidal.Instances      ()
import Cat.Sized.Braided.Instances       ()
import Cat.Sized.Diagonal.Instances      ()
import Cat.Sized.Semicartesian.Instances ()

import Data.Vector.Sized qualified as VS
import Cat.Orthotope
  ( R1
  )



instance Cartesian VS.Vector (Sized (->))

instance Cartesian R1        (Sized (->))
