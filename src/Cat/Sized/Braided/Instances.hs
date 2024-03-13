{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Braided.Instances
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
import Data.Composition
  ( (.:)
  )



import Cat.Sized.Category.Class
  ( Sized ( Sized )
  )

import Cat.Sized.Braided.Class
  ( Braided ( swap
            -- , swap'
            )
  , Permutable ( -- Perm
                 permute
               )
  , permRep'
  )

import Cat.Sized.Category.Instances ()

import Cat.Sized.Monoidal.Instances ()

import Cat.Orthotope
  ( R1 ( R1, unR1 )
  , swapA
  , permuteA
  )
import Cat.VectorSized
  ( swapV
  )

import Data.Vector.Sized qualified as VS



instance Braided VS.Vector (Sized (->)) where
  swap = Sized .: swapV
  -- swap' pn i j = Sized $ swapV' pn i j

instance Permutable VS.Vector (Sized (->)) where
  -- type Perm VS.Vector (Sized (->)) = VS.Vector
  permute = Sized ∘ permRep'



instance Braided R1 (Sized (->)) where
  swap i j = Sized $ R1 ∘ swapA i j ∘ unR1
  -- swap' pn i j = Sized $ R1 ∘ swapA' pn i j ∘ unR1

instance Permutable R1 (Sized (->)) where
  -- type Perm R1 (Sized (->)) = R1
  -- permute (R1 t) =
  --   let p ∷ KnownNat n ⇒ Array '[n] Int → Array '[n] a → Array '[n] a
  --       p xs fa =   A.generate
  --               $   head
  --               >>> A.index xs
  --               >>> A.unScalar
  --               >>> A.index fa
  --               >>> A.unScalar
  --   in  Sized
  --    $  R1
  --    ∘  p ((fromIntegral ∘ getFinite) <$> t)
  --    ∘  unR1

  permute t = Sized
            $ R1
            ∘ permuteA t
            ∘ unR1
