{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Semicocartesian.Instances
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
import Cat.Sized.Semicocartesian.Class
  ( Semicocartesian (InjObject, inj)
  , injMon
  , Pad (PadObject, pad)
  , padMon
  )

import Cat.Orthotope
  ( R1 (R1, unR1)
  , injA
  , padA
  )

import Data.Vector.Sized qualified as VS



instance Semicocartesian VS.Vector (Sized (->)) where
  type InjObject VS.Vector (Sized (->)) n a = Monoid a

  inj = Sized ∘ injMon

instance Pad VS.Vector (Sized (->)) where
  type PadObject VS.Vector (Sized (->)) n l a = Monoid a

  pad = Sized ∘ padMon


instance Semicocartesian R1 (Sized (->)) where
  type InjObject R1 (Sized (->)) n a = Monoid a

  inj fn = Sized
         $ R1
         ∘ injA fn
         ∘ unR1


instance Pad R1 (Sized (->)) where
  type PadObject R1 (Sized (->)) n l a = Monoid a

  pad x = Sized
        $ R1
        ∘ padA x
        ∘ unR1
