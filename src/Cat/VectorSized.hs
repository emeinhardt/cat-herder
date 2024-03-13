{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{- |
'Vector' from "Data.Vector.Sized" is one of the monoidal product functors
with many instances for `->` currently.

This module exports functions on @Vector@s used to define typeclass instances
for 'Vector' and '(->)'.

-}

{- TODO

 - Continue to move scattered instance implementations into explicit functions
   and gather them here.

-}

module Cat.VectorSized
  ( -- * 'Monoidal' instance definitions
    parV
  , ithV
  , singV
  , unsingV
  , joinV
  , splitV

    -- * 'Zip' instance definitions
  , zipWithV

    -- * 'Braided' instance definitions
  , swapV

    -- * 'Diagonal' instance definitions
  , forkV

    -- * 'Select' instance definitions
  , selV

    -- * 'Delete' instance definitions
  , delV
  ) where

import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zip
  , zipWith
  , traverse
  , sequence
  , Monad
  , return
  )

-- Module convention: use (∘) for composition in Hask, use (⊙) for "sized"
-- semigroupoid composition
import Prelude.Unicode
  ((∘))
import Control.Arrow.Unicode
  ((⁂))
import Control.Arrow
  ((&&&))

import Data.Functor  qualified as F

import Data.Kind (Type)
import Data.Data (Proxy(Proxy))
import GHC.TypeNats
  ( KnownNat
  , Nat
  , pattern SNat
  , type (+)
  , type (-)
  , type (<=)
  , type (*)
  , natVal
  )
import Data.Finite
  ( Finite
  , getFinite
  , weaken
  )

import Data.Maybe (fromJust)

import Cat.Sized.Category.Instances ()


import Data.Vector       qualified as V
import Data.Vector.Sized qualified as VS



{- | Tensor product (parallel composition) implementation for @Sized (->)@. -}
parV ∷ ∀ (n ∷ Nat) (m ∷ Nat) (n' ∷ Nat) (m' ∷ Nat) (a ∷ Type) (b ∷ Type).
     ( KnownNat n )
     ⇒ (VS.Vector  n       a → VS.Vector   m       b)
     → (VS.Vector      n'  a → VS.Vector       m'  b)
     → (VS.Vector (n + n') a → VS.Vector  (m + m') b)
parV f g = uncurry (VS.++)
         ∘ (f ⁂ g)
         ∘ VS.splitAt

{- | @ith@ implementation for @Sized (->)@. -}
ithV ∷ ∀ (n ∷ Nat) (a ∷ Type).
       Finite n
     → (VS.Vector 1 a → VS.Vector 1 a)
     → (VS.Vector n a → VS.Vector n a)
ithV fi f =
  let update_ ∷ Finite n → (a → a) → VS.Vector n a → VS.Vector n a
      update_ i φ v = v VS.// [(i, φ $ v `VS.index` i)]
  in update_ fi ((flip VS.index 0) ∘ f ∘ pure)

{- | @sing@ implementation for @Sized (->)@: @pure@. -}
singV ∷ ∀ (n ∷ Nat) (a ∷ Type).
        VS.Vector n a → VS.Vector 1 (VS.Vector n a)
singV = pure

{- | Inverse of @sing@: @flip VS.index 0@. -}
unsingV ∷ ∀ (n ∷ Nat) (a ∷ Type).
          VS.Vector 1 (VS.Vector n a) → VS.Vector n a
unsingV = flip VS.index 0

{- | @join@ implementation for @Sized (->)@: @VS.concatMap id@. -}
joinV ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
        VS.Vector  n      (VS.Vector m a)
      → VS.Vector (n * m)              a
joinV = VS.concatMap P.id


{- | @split@ implementation for @Sized (->)@.

>>> abcdef = fromJust $ VS.fromList @6 "abcdef"
>>> splitV @3 @2 abcdef
Vector [Vector "ab",Vector "cd",Vector "ef"]
>>> splitV @4 @1 (fromJust $ VS.fromList @4 "abcd")
Vector [Vector "a",Vector "b",Vector "c",Vector "d"]
>>> splitV @1 @4 (fromJust $ VS.fromList @4 "abcd")
Vector [Vector "abcd"]
-}
splitV ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
      ( KnownNat n, KnownNat m, KnownNat (n * m) )
      ⇒ VS.Vector (n * m)              a
      → VS.Vector  n      (VS.Vector m a)
splitV v =
  let v' = VS.fromSized v
      m_ ∷ Int
      m_ = fromIntegral $ natVal $ SNat @m

      starts ∷ VS.Vector n (Finite ((n * m) + 1))
      starts = VS.enumFromStepN @n 0 (fromIntegral m_)

      mk_ ∷ Finite ((n * m) + 1) → VS.Vector m a
      mk_ fi = fromJust $ VS.toSized @m
             $ flip V.slice m_ (fromIntegral $ getFinite fi) v'

  in  VS.generate (\i → mk_ (starts `VS.index` i))



{- | @Cat.Sized.Functor.Monoidal.zipWith@ implementation for @Sized (->)@. -}
zipWithV ∷ ∀ (n ∷ Nat) (m ∷ Nat) a b (l ∷ Nat) .
         (KnownNat l)
         ⇒ (VS.Vector n a → VS.Vector m b)
         → (VS.Vector n (VS.Vector l a) → VS.Vector l (VS.Vector m b))
zipWithV f = F.fmap f ∘ sequenceA



swapV ∷ ∀ (n ∷ Nat) a.
        Finite n
      → Finite n
      → VS.Vector n a
      → VS.Vector n a
swapV i j v =
  v VS.// [ (i, v `VS.index` j )
          , (j, v `VS.index` i )
          ]

-- swapV' ∷ ∀ (n ∷ Nat) a prox.
--          prox n
--        → Finite n
--        → Finite n
--        → VS.Vector n a
--        → VS.Vector n a
-- swapV' _ = swapV



-- obviated by @dupRep@
-- dupV ∷ ∀ (n ∷ Nat) (s ∷ Nat) a.
--      ( KnownNat n, KnownNat s
--      , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
--      )
--      ⇒ VS.Vector n a → VS.Vector (s * n) a
-- dupV v =
--   let m' ∷ Finite (s * n)
--       m' = fromIntegral $ natVal (P.Proxy @(s * n))
--       f ∷ Finite (s * n) → a
--       f j = v `VS.index` (fromIntegral (j `div` m'))
--   in  VS.generate f

forkV ∷ ∀ (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) a b.
        (VS.Vector l a → VS.Vector  n      b)
      → (VS.Vector l a → VS.Vector      m  b)
      → (VS.Vector l a → VS.Vector (n + m) b)
forkV f g = uncurry (VS.++) ∘ (f &&& g)




selV ∷ ∀ (l ∷ Nat) (n ∷ Nat) a.
     ( KnownNat l, KnownNat n
     , l <= n                       -- GHC (unhelpfully) warns about this being redundant
     )
     ⇒ Finite ((n - l) + 1) -- ^ The starting index of the length /l/ "slice".
     → VS.Vector n a
     → VS.Vector l a
selV fn = fromJust ∘ VS.toSized
        ∘ V.slice (fromIntegral fn) (fromIntegral $ natVal (Proxy @l))
        ∘ VS.fromSized


delV ∷ ∀ (n ∷ Nat) a.
     ( KnownNat n
     , 1 <= n                       -- GHC (unhelpfully) warns about this being redundant
     )
     ⇒ Finite n
     → VS.Vector  n      a
     → VS.Vector (n - 1) a
delV (fn ∷ Finite n) v =
  let f ∷ Finite (n - 1) → a
      f (fi ∷ Finite (n - 1))
        | weaken fi < fn = VS.index v  (weaken fi)
        | otherwise      = VS.index v ( weaken fi  + 1)
  in VS.generate f
