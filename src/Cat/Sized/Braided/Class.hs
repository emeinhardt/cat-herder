{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- |

module Cat.Sized.Braided.Class
  ( Braided ( SwapObject
            , swap
            -- , swap'
            )
  , SwapObject'
  , swapRep

  , Permutable ( PermObject
               -- , Perm
               , permute
               )
  , PermObject'
  , permRep
  , permRep'

  , zipPermIdxs
  , zipPerm

  , reverse
  , rotateR
  , rotateL
  ) where

-- import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , reverse
  )
import Prelude.Unicode
  ((∘))
import Control.Arrow
  ((>>>))
import Data.Composition
  ( (.:)
  )

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained4)

import GHC.TypeNats
  ( KnownNat
  , Nat
  , pattern SNat
  , natVal
  , type (*)
  )
import Data.Finite
  ( Finite
  , finite
  , getFinite
  , finites
  )

import Data.Functor.Rep qualified as R
import Data.Functor.Rep
  ( Representable
  , Rep
  , tabulate
  )

import Cat.Operators (type (-|), type (|->))

import Cat.Sized.Semigroupoid.Class
  ( Object
  , (⊙)
  , Sub (Sub)
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( split
             , join
             )
  , Proxy
  )



{- | A braided monoidal category permits swapping (pairs of) elements in a
product.

(This module does not distinguish between braided and symmetric monoidal
categories (SMCs) via typeclasses.) -}
class (Monoidal φ k)
  ⇒ Braided (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
{-
Minimal definition if @Proxy k ~ SNat@: @swap | swap'@.
Minimal definition otherwise: @swap@.
-}

  {- | Extra constraints on whether an object @a@ can be swapped in a /φ/-structure
  of length /n/. -}
  type SwapObject φ (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type SwapObject φ k n a = Unconstrained4 φ k n a

  swap ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object φ k n a
       , SwapObject φ k n a
       )
       ⇒ Finite n  -- ^ The first of two indices to swap.
       → Finite n  -- ^ The other of two indices to swap.
       → a -| k φ n n |-> a

  -- default swap ∷ ∀ (n ∷ Nat) (a ∷ κ).
  --      ( KnownNat n
  --      , Object φ k n a
  --      , SNat ~ Proxy φ k
  --      )
  --      ⇒ Finite n
  --      → Finite n
  --      → a -| k φ n n |-> a
  -- swap (fi ∷ Finite n) (fj ∷ Finite n) = swap' @κ @φ @k @n @a (SNat @n) fi fj

  -- -- TODO @limbo-test is the proxy argument here actually needed?
  -- swap' ∷ ∀ (n ∷ Nat) (a ∷ κ).
  --       ( KnownNat n
  --       , Object φ k n a
  --       )
  --       ⇒ (Proxy φ k) n
  --       → Finite n
  --       → Finite n
  --      → a -| k φ n n |-> a
  -- swap' (_ ∷ (Proxy φ k) n) (fi ∷ Finite n) (fj ∷ Finite n) = swap @κ @φ @k @n @a fi fj

--  {-# MINIMAL swap | swap' #-}


{- | This is a "class synonym" for the type family 'SwapObject'; it's often needed to
write quantified constraints. -}
class    (SwapObject φ k n a)
  ⇒ SwapObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (SwapObject φ k n a)
  ⇒ SwapObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


instance (Braided φ k, Proxy φ k ~ Proxy φ (o `Sub` k)) ⇒ Braided φ (o `Sub` k) where
  type SwapObject φ (o `Sub` k) n a = SwapObject φ k n a
  swap     = Sub .: swap
  -- swap' = Sub .:. swap'



{- | This is a generic implementation for 'swap' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /φ/ with a
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instance for /φ n/. -}
swapRep ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
        ( Representable (φ n)
        -- , R.Rep (φ n) ~ Finite n
        , Eq (Rep (φ n))
        )
        ⇒ Rep (φ n)
        → Rep (φ n)
        -- ⇒ Finite n
        -- → Finite n
        → φ n a
        → φ n a
swapRep i j fa =
  let tab x
       | x == i    = fa `R.index` j
       | x == j    = fa `R.index` i
       | otherwise = fa `R.index` x
  in tabulate tab



{- | This variation on 'Braided' permits specifying a collection of permutations
rather than just two. -}
class (Monoidal φ k)
  ⇒ Permutable (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constraints on whether a @φ n a@ can be permuted. -}
  type PermObject φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type PermObject φ k n a = Unconstrained4 φ k n a

  -- TODO Alternative: trade this type family for a constraint on the first
  -- argument to @permute@ that the the first argument must be a (Nat-index)
  -- representable functor γ (of size n) containing @Finite n@ values?
  -- {- | A sized functor that can hold a collection of indices describing a permutation. -}
  -- type Perm φ k ∷ Nat → Type → Type

  {- | 'permute τ' defines a permutation on an /n/-product. The constraints on /τ/
  enforce that

    - Every index in an /n/-product is mapped to some index into an /n/-product.

  These constriants do not, however, statically enforce that /τ/ *only*
  expresses a permutation: it is possible to pass a "permutation" with one or
  more indices represented multiple times — and hence some input indices will
  not be represented at all.

  An alternative or complement to this typeclass without this defect could be
  based on the @transpose@ function in @orthotope@'s @Data.Array.Shaped@, which
  uses type-level size and type-level lists of indices to define a statically-
  correct permutation function. -}
  permute ∷ ∀ γ (n ∷ Nat) (a ∷ κ).
          ( KnownNat n
          , Object φ k n a
          , PermObject φ k n a
          , Representable γ
          , Rep γ ~ Finite n
          -- , Representable (Perm φ k n)
          -- , Rep (Perm φ k n) ~ Finite n
          )
          ⇒ γ (Finite n)              -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.

          -- -- ⇒ Perm φ k n (Finite n)  -- -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.
          → a -| k φ n n |-> a



{- | This is a "class synonym" for the type family 'PermObject'; it's often needed to
write quantified constraints. -}
class    (PermObject φ k n a)
  ⇒ PermObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (PermObject φ k n a)
  ⇒ PermObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


-- instance (Permutable φ k, Perm φ k ~ φ) ⇒ Permutable φ (o `Sub` (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type)) where
--   type PermObject φ (o `Sub` k) n a = PermObject φ k n a
--   type Perm       φ (o `Sub` k)     = φ
--   permute = Sub .: permute



{- | This is a generic implementation for 'permute' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /φ/ with a
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instance for /φ n/. -}
permRep ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
        ( Representable (φ n)
        )
        ⇒ φ n (Rep (φ n))  -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.
        → φ n a
        → φ n a
permRep t fa =   tabulate    -- Given an output index j to associate with a value...
             $   R.index t   -- 1. Lookup the associated input index i in t
             >>> R.index fa  -- 2. Return fa ! i



{- | This is a generic implementation for 'permute' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /γ/ with a suitable
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instance for /γ/. -}
permRep' ∷ ∀ (γ ∷ Type → Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
         ( Representable γ
         , Rep γ ~ Finite n
         , Representable (φ n)
         , Rep (φ n) ~ Finite n
         )
         ⇒ γ (Finite n)
         → φ n a
         → φ n a
permRep' t fa =   tabulate
              $   R.index t
              >>> R.index fa


{- | This defines a permutation of an /n*m/ product that represents /n/ copies of
indices into an /m/-product suitable for defining

> zip ∷ φ m a -| k φ n m |-> φ n a

from "Cat.Sized.Monoidal.Functor":

@
0  : 0, 0 + 1*m, 0 + 2*m … 0 + (n-1)*m  -- The first /n/ indices of the permutation
1  : 1, 1 + 1*m, 1 + 2*m … 1 + (n-1)*m  -- The next /n/ indices...
…  :
i  : i, i + 1*m, i + 2*m … i + (n-1)*m
…  : …
m-1: …
@

In general, permutation index @x@ ≝ @(x \`div\` n) + (x \`mod\` n)*n@. -}
zipPermIdxs ∷ ∀ (γ ∷ Type → Type) (n ∷ Nat) (m ∷ Nat).
            ( KnownNat n, KnownNat m
            , Representable γ
            , Rep γ ~ Finite (n * m)
            )
            ⇒ γ (Finite (n * m))  -- ^ A permutation of an /n * m/-length product.
zipPermIdxs =
  let f ∷ Finite (n * m) → Finite (n * m)
      f x =
        let m'  = fromIntegral $ natVal (SNat @m)
            -- n'  = fromIntegral $ natVal (SNat @n)
            x'  = fromIntegral $ getFinite x
            row = x' `div` m'
            col = x' `mod` m'
        in finite $ row + (col * m')
  in  tabulate f


{- | Definition of "Data.Functor.Monoidal"'s @zip@ for any @Permutable φ k@ and
suitable choice of functor for holding permutation data @γ@.

>>> zipPerm ≝ split ⊙ permute (zipPermIdxs @γ @n @m) ⊙ join

If you can define a @Zip@ instance that avoids the cost of flattening and
"reinflating" paid by this definition, you should consider doing so. -}
zipPerm ∷ ∀ κ
           (γ ∷ Type → Type)
           (φ ∷ Nat → κ → κ)
           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat) (m ∷ Nat)
           (a ∷ κ).
          ( Permutable φ k
          , KnownNat n
          , KnownNat m
          , KnownNat (n * m)
          , Object φ k n (φ m a)
          , Object φ k m (φ n a)
          , Object φ k (n * m) a
          , PermObject φ k (n * m) a
          , Representable γ
          , Rep γ ~ Finite (n * m)
          )
          ⇒ φ m a -| k φ n m |-> φ n a  -- ^ A /k/-morphism that zips /n/ /m/-products into an /m/-product of /n/-products.
zipPerm =
  let
    τ ∷ a -| k φ (n * m) (n * m) |-> a
    τ = permute (zipPermIdxs @γ @n @m)
  in split ⊙ τ ⊙ join


{- | A permutation that reverses the order of elements in the source product.

>>> iota8  = fromJust $ VS.fromList @8 [0..7] :: VS.Vector 8 Int
iota8 :: VS.Vector 8 Int
>>> (unSized $ reverse @Type @(VS.Vector 8)) $ iota8
Vector [7,6,5,4,3,2,1,0]
-}
reverse ∷ ∀ κ
           (γ ∷ Type → Type)
           (φ ∷ Nat → κ → κ)
           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
          ( Permutable φ k
          , KnownNat n
          , Object φ k n a
          , PermObject φ k n a
          , Representable γ
          , Rep γ ~ Finite n
          )
          ⇒ a -| k φ n n |-> a   -- ^ A /k/-morphism that reverses the order of elements in an /n/-product.
reverse = permute
        $ tabulate @γ
        $ flip subtract
        $ fromIntegral
        $ ((natVal $ SNat @n) - 1)


{- | @rotateL i@ defines a morphism that rotates elements of an /n/-product /i/
elements leftward.

>>> iota8  = fromJust $ VS.fromList @8 [0..7] :: VS.Vector 8 Int
iota8 :: VS.Vector 8 Int
>>> (unSized $ rotateL @Type @(VS.Vector 8) 1) $ iota8
Vector [1,2,3,4,5,6,7,0]
>>> (unSized $ rotateL @Type @(VS.Vector 8) 3) $ iota8
Vector [3,4,5,6,7,0,1,2]
-}
rotateL ∷ ∀ κ
           (γ ∷ Type → Type)
           (φ ∷ Nat → κ → κ)
           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
          ( Permutable φ k
          , KnownNat n
          , Object φ k n a
          , PermObject φ k n a
          , Representable γ
          , Rep γ ~ Finite n
          )
          ⇒ Finite n
          → a -| k φ n n |-> a   -- ^ A /k/-morphism that rotates the /n/ elements leftward, wrapping around.
rotateL i =
  let f' ∷ Integer → Integer → Integer → Integer
      f' n' i' x = (x + i') `mod` n'
      f ∷ Finite n → Finite n
      f = fromIntegral
        ∘ f' (fromIntegral $ natVal $ SNat @n) (fromIntegral i)
        ∘ fromIntegral
  in permute $ tabulate @γ f


{- | @rotateR i@ defines a morphism that rotates elements of an /n/-product /i/
elements rightward.

>>> iota8  = fromJust $ VS.fromList @8 [0..7] :: VS.Vector 8 Int
iota8 :: VS.Vector 8 Int
>>> (unSized $ rotateR @Type @(VS.Vector 8) 1) $ iota8
Vector [7,0,1,2,3,4,5,6]
>>> (unSized $ rotateR @Type @(VS.Vector 8) 3) $ iota8
Vector [5,6,7,0,1,2,3,4]
-}
rotateR ∷ ∀ κ
           (γ ∷ Type → Type)
           (φ ∷ Nat → κ → κ)
           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
          ( Permutable φ k
          , KnownNat n
          , Object φ k n a
          , PermObject φ k n a
          , Representable γ
          , Rep γ ~ Finite n
          )
          ⇒ Finite n
          → a -| k φ n n |-> a   -- ^ A /k/-morphism that rotates the /n/ elements rightward, wrapping around.
rotateR i =
  let f' ∷ Integer → Integer → Integer → Integer
      f' n' i' x = (x - i') `mod` n'
      f ∷ Finite n → Finite n
      f = fromIntegral
        ∘ f' (fromIntegral $ natVal $ SNat @n) (fromIntegral i)
        ∘ fromIntegral
  in permute $ tabulate @γ f
