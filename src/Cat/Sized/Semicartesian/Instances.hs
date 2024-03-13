{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Semicartesian.Instances
  (
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )

-- Module convention: use (∘) for composition in Hask
import Prelude.Unicode ((∘))

import Data.Finite
  ( Finite
  , getFinite
  )

import Cat.Sized.Category.Class
  ( Sized ( Sized )
  )

import Cat.Sized.Semicartesian.Class
  ( Semicartesian ( idx
                  )
  , idxRep
  , Delete ( del
           )
  , Select ( sel
           )
  , HasTerminal ( terminal
                )
  -- , FinRep (FinRep, unFinRep)
  )

import Cat.Sized.Category.Instances ()

import Cat.Sized.Monoidal.Instances ()


import Cat.Orthotope
  ( R1 ( R1, unR1 )
  , selA
  , delA
  )
import Cat.VectorSized
  ( selV
  , delV
  )


import Data.Vector.Sized qualified as VS
import Data.Array.Shaped qualified as A


-- TODO trickiness around type synonyms means I'll have more luck if I have some
-- other way of stipulating that φ has to be Representable *and* that
--   R.Rep (φ n) ~ Finite n
--
-- instance (
--            ∀ m. KnownNat m ⇒ (Representable (φ m))
--          -- , ∀ m. (logfm ~ R.Rep (φ m)) ⇒ logfm ~ Finite m
--          , Monoidal φ (Sized (->))
--          , ∀ m. (frn ~ R.Rep (φ m)) ⇒ frn ~ Finite m
--          )
--   ⇒ Semicartesian φ (Sized (->))
--   where

--   idx (fn ∷ Finite n) =
--       Sized
--     $ R.tabulate @(φ 1)
--     ∘ const
--     ∘ flip R.index (fn ∷ Finite n)


-- Requires undecidable instances, and does seem to actually make type inference harder
-- deriving via (FinRep (Sized (->))) instance Semicartesian VS.Vector (Sized (->))

instance Semicartesian VS.Vector (Sized (->)) where
  idx = Sized ∘ idxRep
  -- idx (fn ∷ Finite n) =
  --     Sized
  --   $ pure
  --   ∘ flip VS.index fn

instance HasTerminal VS.Vector (Sized (->)) where
  terminal = Sized ∘ const $ VS.empty

instance Delete VS.Vector (Sized (->)) where
  del = Sized ∘ delV


instance Select VS.Vector (Sized (->)) where
  sel = Sized ∘ selV





instance Semicartesian R1 (Sized (->)) where
  idx (fn ∷ Finite n) =
      Sized
    $ R1
    ∘ A.reshape
    ∘ flip A.index (fromIntegral $ getFinite fn)
    ∘ unR1

instance HasTerminal R1 (Sized (->)) where
  terminal = Sized ∘ const ∘ R1 $ A.fromList @'[0] []

instance Delete R1 (Sized (->)) where
  del (fn ∷ Finite n) =
      Sized
    $ R1
    ∘ delA fn
    ∘ unR1

instance Select R1 (Sized (->)) where
  sel (fn ∷ Finite n) =
      Sized
    $ R1
    ∘ selA fn
    ∘ unR1
