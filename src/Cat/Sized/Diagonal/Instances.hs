{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Diagonal.Instances
  (
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )

-- Module convention: use (∘) for composition in Hask
import Prelude.Unicode
  ((∘))

import Cat.Sized.Category.Class
  ( Sized ( Sized )
  )

import Cat.Sized.Diagonal.Class
  ( Diagonal ( dup
             -- , dup'
             , (&&&)
             )
  , dupRep
  )

import Cat.Sized.Category.Instances ()

import Cat.Sized.Monoidal.Instances ()


import Data.Vector.Sized qualified as VS
import Cat.VectorSized
  ( forkV
  )
import Cat.Orthotope
  ( R1 ( R1, unR1 )
  , forkA
  , dupA
  )



instance Diagonal VS.Vector (Sized (->)) where
  (Sized f) &&& (Sized g) = Sized $ f `forkV` g
  -- dup = Sized dupV
  dup = Sized dupRep




instance Diagonal R1 (Sized (->)) where
  dup = Sized $ R1 ∘ dupA ∘ unR1
  (Sized (f ∷ R1 l a → R1 n b)) &&& (Sized (g ∷ R1 l a → R1 m b)) =
      Sized
    $ R1
    ∘ forkA (unR1 ∘ f ∘ R1)
            (unR1 ∘ g ∘ R1)
    ∘ unR1
