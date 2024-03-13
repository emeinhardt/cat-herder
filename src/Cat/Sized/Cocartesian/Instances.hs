{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Cocartesian.Instances
  (
  ) where

import Cat.Sized.Semigroupoid.Class
  ( Sized )

import Cat.Sized.Braided.Instances         ()
import Cat.Sized.Codiagonal.Instances      ()
import Cat.Sized.Semicocartesian.Instances ()
import Cat.Sized.Cocartesian.Class
  ( Cocartesian
  )

import Cat.Orthotope
 ( R1 )
import Data.Vector.Sized qualified as VS



instance Cocartesian VS.Vector (Sized (->))

instance Cocartesian R1        (Sized (->))
