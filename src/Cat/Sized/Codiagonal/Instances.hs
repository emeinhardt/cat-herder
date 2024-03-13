{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Codiagonal.Instances
  (
  ) where

import Prelude hiding
 ( (.)
 , id
 , Functor
 , fmap
 , zip
 , zipWith
 )

import Cat.Sized.Semigroupoid.Class
  ( Sized (Sized)
  )

import Cat.Sized.Codiagonal.Class
  ( Codiagonal ( JamObject
               , jam
               )
  , jamMon
  )
import Cat.Orthotope
  (R1)

import Cat.Sized.Semigroupoid.Instances ()
import Cat.Sized.Category.Instances ()
import Cat.Sized.Monoidal.Instances ()

import Data.Vector.Sized qualified as VS



-- | Objects must have a 'Monoid' instance.
instance Codiagonal VS.Vector (Sized (->)) where
  type JamObject VS.Vector (Sized (->)) n a = Monoid a

  jam = Sized jamMon



-- | Objects must have a 'Monoid' instance.
instance Codiagonal R1 (Sized (->)) where
  type JamObject R1 (Sized (->)) n a = Monoid a

  jam = Sized jamMon
