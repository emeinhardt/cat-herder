{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Braided.Free.Data
  ( Swap ( Emb
         , Id
         , Of
         , Par
         , Mul
         , Ith
         , Ith'
         , Join
         , Split
         , Assoc
         , Sing
         , Unsing
         , Lift1
         , Bising
         , Bisplit
         , Bijoin
         , Biassoc
         , Swap
         -- , Swap'
         )
  , HasSwap (SwapObjectOf)
  -- , SwapObjectOf'
  , HasPerm (PermObjectOf)
  , foldMap

  --   -- * Recursion schemes
  , BraidedFunctor
  , SwapF ( EmbF
          , IdF
          , OfF
          , ParF
          , MulF
          , IthF
          , IthF'
          , JoinF
          , SplitF
          , AssocF
          , SingF
          , UnsingF
          , Lift1F
          , BisingF
          , BisplitF
          , BijoinF
          , BiassocF
          , SwapF
          -- , SwapF'
          -- , PermuteF
          )
  , Swap'
  , foldMap'
  , mkAlg
  , fixed
  , fixedCoalg
  , fixed'
  , unfixed
  , unfixedAlg
  , unfixed'
  ) where


import Prelude hiding
  ( id
  , (.)
  , Functor
  , fmap
  , foldMap
  )
import Data.Composition ((.:))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained4)

import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , type (+)
  , type (*)
  )

import Data.Finite (Finite)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Functor
  ( NT'
  , HFunctor ( hfmap
             , HFunctorObj
             )
  , Fix ( In
        )
  , cata
  , ana
  )

import Cat.Sized.Semigroupoid.Class
  ( Object
  , Object'
  , (⊙)
  )
import Cat.Sized.Category.Class
  ( id
  )

import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , (***)
             , mul
             , ith
             , ith'
             , join
             , split
             , assoc
             , sing
             , unsing
             , lift1
             , bising
             , bisplit
             , bijoin
             , biassoc
             )
  , (⊗)
  -- , ProdK
  )

import Cat.Sized.Braided.Class
  ( Braided ( SwapObject
            , swap
            -- , swap'
            )
  , SwapObject'
  )

import Cat.Sized.Semigroupoid.Free.Data
 ( HasObject ( ObjectOf
             )
 )

import Cat.Sized.Monoidal.Free.Data
  ( HasProxy (ProxyOf)
  )



class HasSwap (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  type SwapObjectOf (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type SwapObjectOf φ k n a = Unconstrained4 φ k n a

class HasPerm (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  type PermObjectOf (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type PermObjectOf φ k n a = Unconstrained4 φ k n a



data Swap (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   where

  Emb ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a
      , ObjectOf φ k m b
      -- TODO constrain k to be a category or monoidal?
      )
      ⇒ a -|      k φ n m |-> b  -- ^ A /k/-morphism to lift into a symmetric monoidal category.
      → a -| Swap k φ n m |-> b

  Id ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a
     )
     ⇒ Swap k φ n n a a  -- ^ The lifted identity morphism for any given size /n/.

  Of ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
           (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a
     , ObjectOf φ k m b
     , ObjectOf φ k l x
     )
     ⇒ x -| Swap k φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -| Swap k φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| Swap k φ n m |-> b

  Par ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ a -| Swap k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Swap k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Swap k φ (n + n') (m + m') |-> b

  Mul ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -| Swap k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Swap k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Swap k φ (n + n') (m + m') |-> b

  Ith ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a
      , ObjectOf φ k n a
      )
      ⇒ Finite n                 -- ^ The position to place the singleton-to-singleton morphism.
      → a -| Swap k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| Swap k φ n n |-> a

  Ith' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a
       , ObjectOf φ k n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                 -- ^ The position to place the singleton-to-singleton morphism.
       → a -| Swap k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| Swap k φ n n |-> a

  Join ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| Swap k φ n (n * m) |-> a
       ⇒ (φ m a) -| Swap k φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  Split ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a
        , ObjectOf φ k      n  (φ m a)
        )
        -- ⇒ a -| Swap k φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| Swap k φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  Assoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a)
        , ObjectOf φ k m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| Swap k φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| Swap k φ n m |-> (φ n a)  -- ^ A size-preserving morphism that swaps nesting.

  Sing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a
        , ObjectOf φ k 1 (φ n a)
        )
        ⇒ a -| Swap k φ n 1 |-> φ n a

  Unsing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a)
        , ObjectOf φ k n      a
        )
        ⇒ φ n a -| Swap k φ 1 n |-> a

  Lift1 ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a
        , ObjectOf φ k m      b
        , ObjectOf φ k n (φ 1 a)
        , ObjectOf φ k m (φ 1 b)
        )
        ⇒     a -| Swap k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| Swap k φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  Bising ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a
         , ObjectOf φ k m      b
         , ObjectOf φ k 1 (φ n a)
         , ObjectOf φ k 1 (φ m b)
         )
         ⇒     a -| Swap k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| Swap k φ 1 1 |-> φ m b

  Bisplit ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒     a -| Swap k φ (i * n) (j * m) |->     b  -- ^ A /k/ morphism whose products on either side can be factored.
    → φ i a -| Swap k φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  Bijoin ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (i ∷ Nat) (j ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒ φ i a -| Swap k φ      n       m  |-> φ j b  -- ^ A /k/ morphism with nested products.
    →     a -| Swap k φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  Biassoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n  ∷ Nat) (m  ∷ Nat)
                (i  ∷ Nat) (j  ∷ Nat)
                (n' ∷ Nat) (m' ∷ Nat)
                (i' ∷ Nat) (j' ∷ Nat)
                (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a
    , ObjectOf φ k (j' * m')      b
    )
    ⇒ φ i  a -| Swap k φ n  m  |-> φ j  b  -- ^ A /k/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| Swap k φ n' m' |-> φ j' b

  Swap ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n a
        , SwapObjectOf φ k n a
        )
        ⇒ Finite n
        → Finite n
        → a -| Swap k φ n n |-> a

  -- Swap' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --             (n ∷ Nat) (a ∷ κ).
  --        ( KnownNat n
  --        , ObjectOf φ k n a
  --        , SwapObjectOf φ k n a
  --        )
  --        ⇒ (Proxy φ k) n
  --        → Finite n
  --        → Finite n
  --        → a -| Swap k φ n n |-> a



deriving instance ( p ~ ProxyOf φ k
                  , ∀ i. Show (p i)
                  , ∀ i j x y. Show (k φ i j x y)
                  ) ⇒ Show (Swap k φ n m a b)



foldMap ∷ ∀ κ
          (φ ∷  Nat → κ → κ)
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( ObjectOf φ k n a, ObjectOf φ k m b
        , Object   φ t n a, Object   φ t m b
        , ∀ i x. ObjectOf φ k i x ⇒ Object' φ t i x
        -- , SwapObjectOf φ k n a, SwapObjectOf φ k n b
        -- , SwapObject   φ t n a, SwapObject   φ t n b
        , ∀ i x. SwapObjectOf φ k i x ⇒ SwapObject' φ t i x
        , Braided φ (Swap k), Braided φ t
        )
        ⇒ (∀ i. (ProxyOf φ k) i → (Proxy φ t) i)
        → (∀ i j x y.
           ( ObjectOf φ k i x, ObjectOf φ k j y
           , Object   φ t i x, Object   φ t j y
           -- , SwapObjectOf φ k i x, SwapObjectOf φ k j y
           -- , SwapObject   φ t i x, SwapObject   φ t j y
           )
           ⇒ x -| k φ i j |-> y
           → x -| t φ i j |-> y
        )                            -- ^ A function maps primitive morphisms into the target category.
        → a -| (Swap k) φ n m |-> b  -- ^ A path in the free symmetric monoidal category over @k@.
        → a -|  t      φ n m |-> b   -- ^ The resulting morphism in @t@.
foldMap _ α (Emb f)     = α f
foldMap _ _  Id         = id
foldMap π α (g `Of` f)  = foldMap π α g  ⊙  foldMap π α f
foldMap π α (f `Par` g) = foldMap π α f  ⊗  foldMap π α g
foldMap π α (Mul pn pm pn' pm' f g) = mul (π pn) (π pm) (π pn') (π pm')
                                          (foldMap π α f) (foldMap π α g)
foldMap π α (i `Ith` f)   = i `ith` (foldMap π α f)
foldMap π α (Ith' pn i f) = ith' (π pn) i (foldMap π α f)
foldMap _ _ Join   = join
foldMap _ _ Split  = split
foldMap _ _ Assoc  = assoc
foldMap _ _ Sing   = sing
foldMap _ _ Unsing = unsing
foldMap π α (Lift1   f) = lift1   (foldMap π α f)
foldMap π α (Bising  f) = bising  (foldMap π α f)
foldMap π α (Bisplit f) = bisplit (foldMap π α f)
foldMap π α (Bijoin  f) = bijoin  (foldMap π α f)
foldMap π α (Biassoc f) = biassoc (foldMap π α f)
foldMap _ _ (Swap i j)  = swap i j


-- TODO Permit change of tensor product in foldMap



{- | Pattern functor for 'Swap'. -}
data SwapF (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (φ ∷ Nat → κ → κ)
           (n ∷ Nat) (m ∷ Nat)
           (a ∷ κ)   (b ∷ κ)   where

  EmbF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a, ObjectOf φ k m b
      , Object   φ t n a, Object   φ t m b
      )
      ⇒ a -|       k   φ n m |-> b  -- ^ A /k/-morphism to lift into a monoidal category.
      → a -| SwapF k t φ n m |-> b

  IdF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat)
            (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a, Object φ t n a
     )
     ⇒ a -| SwapF k t φ n n |-> a  -- ^ The lifted identity morphism for any given size /n/.

  OfF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
            (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
     , Object   φ t n a, Object   φ t m b, Object   φ t l x
     )
     ⇒ x -|         t φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -|         t φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| SwapF k t φ n m |-> b

  ParF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ a -|         t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|         t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| SwapF k t φ (n + n') (m + m') |-> b

  MulF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -|         t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|         t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| SwapF k t φ (n + n') (m + m') |-> b

  IthF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a, ObjectOf φ k n a
      , Object   φ t 1 a, Object   φ t n a
      )
      ⇒ Finite n                    -- ^ The position to place the singleton-to-singleton morphism.
      → a -|         t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| SwapF k t φ n n |-> a

  IthF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a, ObjectOf φ k n a
       , Object   φ t 1 a, Object   φ t n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                    -- ^ The position to place the singleton-to-singleton morphism.
       → a -|         t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| SwapF k t φ n n |-> a

  JoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       , Object   φ t  n      (φ m a)
       , Object   φ t (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| SwapF k t φ n (n * m) |-> a
       ⇒ (φ m a) -| SwapF k t φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  SplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a , Object   φ t (m * n)      a
        , ObjectOf φ k      n  (φ m a), Object   φ t      n  (φ m a)
        )
        -- ⇒ a -| SwapF k t φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| SwapF k t φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  AssocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a), ObjectOf φ k m (φ n a)
        , Object   φ t n (φ m a), Object   φ t m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| SwapF k t φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| SwapF k t φ n m |-> (φ n a)  -- ^ A size-preserving morphism that swaps nesting.

  SingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a , Object   φ t n      a
        , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
        )
        ⇒ a -| SwapF k t φ n 1 |-> φ n a

  UnsingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
        , ObjectOf φ k n      a , Object   φ t n      a
        )
        ⇒ φ n a -| SwapF k t φ 1 n |-> a

  Lift1F ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a , Object   φ t n      a
        , ObjectOf φ k m      b , Object   φ t m      b
        , ObjectOf φ k n (φ 1 a), Object   φ t n (φ 1 a)
        , ObjectOf φ k m (φ 1 b), Object   φ t m (φ 1 b)
        )
        ⇒     a -|         t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| SwapF k t φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  BisingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a , Object   φ t n      a
         , ObjectOf φ k m      b , Object   φ t m      b
         , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
         , ObjectOf φ k 1 (φ m b), Object   φ t 1 (φ m b)
         )
         ⇒     a -|        t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| SwapF k t φ 1 1 |-> φ m b

  BisplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n ∷ Nat) (m ∷ Nat)
                 (i ∷ Nat) (j ∷ Nat)
                 (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a , Object   φ t (i * n)     a
    , ObjectOf φ k (j * m)     b , Object   φ t (j * m)     b
    , ObjectOf φ k      n (φ i a), Object   φ t      n (φ i a)
    , ObjectOf φ k      m (φ j b), Object   φ t      m (φ j b)
    )
    ⇒     a -|         t φ (i * n) (j * m) |->     b  -- ^ A /t/ morphism whose products on either side can be factored.
    → φ i a -| SwapF k t φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  BijoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a , Object   φ t (i * n)     a
    , ObjectOf φ k (j * m)     b , Object   φ t (j * m)     b
    , ObjectOf φ k      n (φ i a), Object   φ t      n (φ i a)
    , ObjectOf φ k      m (φ j b), Object   φ t      m (φ j b)
    )
    ⇒ φ i a -|         t φ      n       m  |-> φ j b  -- ^ A /t/ morphism with nested products.
    →     a -| SwapF k t φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  BiassocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n  ∷ Nat) (m  ∷ Nat)
                 (i  ∷ Nat) (j  ∷ Nat)
                 (n' ∷ Nat) (m' ∷ Nat)
                 (i' ∷ Nat) (j' ∷ Nat)
                 (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a), Object   φ t       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b), Object   φ t       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a), Object   φ t       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b), Object   φ t       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a , Object   φ t (i' * n')      a
    , ObjectOf φ k (j' * m')      b , Object   φ t (j' * m')      b
    )
    ⇒ φ i  a -|         t φ n  m  |-> φ j  b  -- ^ A /t/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| SwapF k t φ n' m' |-> φ j' b

  SwapF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n a, SwapObjectOf φ k n a
        , Object   φ t n a, SwapObject   φ t n a
        )
        ⇒ Finite n
        → Finite n
        → a -| SwapF k t φ n n |-> a  -- ^ A morphism that swaps the two selected indices in an /n/-product.

  -- SwapF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --              (n ∷ Nat) (a ∷ κ).
  --        ( KnownNat n
  --        , ObjectOf φ k n a, SwapObjectOf φ k n a
  --        , Object   φ t n a, SwapObject   φ t n a
  --        )
  --        ⇒ (Proxy φ k) n
  --        → Finite n
  --        → Finite n
  --        → a -| SwapF k t φ n n |-> a


  -- TODO Adding this requires a custom show instance def: there's no guarantee
  -- that γ (Finite n) is Showable, and adding a Show constraint here would
  -- prevent a 'Permutable' instance...
  -- Permute ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --               γ (n ∷ Nat) (a ∷ κ).
  --         ( KnownNat n
  --         , ObjectOf φ k n a
  --         , PermObjectOf φ k n a
  --         , Representable γ
  --         , Rep γ ~ Finite n
  --         -- , Representable (Perm φ k n)
  --         -- , Rep (Perm φ k n) ~ Finite n
  --         )
  --         ⇒ γ (Finite n)              -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.

  --         -- -- ⇒ Perm φ Swap k n (Finite n)  -- -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.
  --         → a -| Swap k φ n n |-> a



deriving instance ( ∀ i j x y. Show (x -| k φ i j |-> y)
                  , ∀ i j x y. Show (x -| t φ i j |-> y)
                  -- , ∀ i p. (p ~ ProxyOf φ k) ⇒ Show (p i)
                  , ProxyOf φ k ~ SNat
                  )
  ⇒ Show (a -| SwapF k t φ n m |-> b)


type Swap' k = Fix (SwapF k)


class    (∀ i x. SwapObject φ p i x ⇒ SwapObject' φ q i x) ⇒ BraidedFunctor η φ p q
instance (∀ i x. SwapObject φ p i x ⇒ SwapObject' φ q i x) ⇒ BraidedFunctor η φ p q


instance (Braided φ (η (Fix η))) ⇒ Braided φ (Fix η) where
  type SwapObject φ (Fix η) n a = SwapObject φ (η (Fix η)) n a

  swap = In .: swap


instance HFunctor (SwapF k) where
  type HFunctorObj (SwapF k) φ p q = BraidedFunctor (SwapF k) φ p q

  hfmap _ (EmbF m)    = EmbF m
  hfmap _ IdF         = IdF
  hfmap α (g `OfF`  f) = α g `OfF`  α f
  hfmap α (f `ParF` g) = α f `ParF` α g
  hfmap α (MulF pn pm pn' pm' f g) = MulF pn pm pn' pm' (α f) (α g)
  hfmap α (IthF     i f) = IthF     i (α f)
  hfmap α (IthF' pn i f) = IthF' pn i (α f)
  hfmap _ JoinF   = JoinF
  hfmap _ SplitF  = SplitF
  hfmap _ AssocF  = AssocF
  hfmap _ SingF   = SingF
  hfmap _ UnsingF = UnsingF
  hfmap α (Lift1F   f) = Lift1F   (α f)
  hfmap α (BisingF  f) = BisingF  (α f)
  hfmap α (BisplitF f) = BisplitF (α f)
  hfmap α (BijoinF  f) = BijoinF  (α f)
  hfmap α (BiassocF f) = BiassocF (α f)
  hfmap _ (SwapF i j) = SwapF i j
  -- -- hfmap _ (SwapF') =
  -- -- hfmap α (PermuteF) =


-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Swap k@ morphism to a @Swap' k@ morphism. -}
fixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf     φ       k  i x ⇒ Object'     φ (Swap  k) i x
  , ∀ i x. Object       φ (Swap k) i x ⇒ Object'     φ (Swap' k) i x
  , ∀ i x. SwapObjectOf φ       k  i x ⇒ SwapObject' φ (Swap' k) i x
  )
  ⇒ a -| Swap  k φ n m |-> b  -- ^ A 'Swap k' morphism.
  → a -| Swap' k φ n m |-> b  -- ^ An equivalent morphism in 'Fix (SwapF k)'.
fixed' Id          = In IdF
fixed' (Emb m)     = In (EmbF m)
fixed' (g `Of`  f) = In (fixed' g `OfF` fixed' f)
fixed' (f `Par` g) = In $ fixed' f `ParF` fixed' g
fixed' (Mul pn pm pn' pm' f g) = In $ MulF pn pm pn' pm' (fixed' f) (fixed' g)
fixed' (Ith     i f) = In $ IthF     i (fixed' f)
fixed' (Ith' pn i f) = In $ IthF' pn i (fixed' f)
fixed' Join   = In $ JoinF
fixed' Split  = In $ SplitF
fixed' Assoc  = In $ AssocF
fixed' Sing   = In $ SingF
fixed' Unsing = In $ UnsingF
fixed' (Lift1   f) = In $ Lift1F   (fixed' f)
fixed' (Bising  f) = In $ BisingF  (fixed' f)
fixed' (Bisplit f) = In $ BisplitF (fixed' f)
fixed' (Bijoin  f) = In $ BijoinF  (fixed' f)
fixed' (Biassoc f) = In $ BiassocF (fixed' f)
fixed' (Swap  i j) = In $ SwapF i j
-- fixed' (Swap' ) =
-- fixed' (Permute ) =


{- | Coalgebra for converting a @Swap k@ morphism to a @Swap' k@ morphism. -}
fixedCoalg ∷ ∀ φ k n m a b.
  -- Both constraints can be satisfied wherever instances from Cat.Sized.Braided.Free.Instances are in scope.
  ( ∀ j x. ObjectOf     φ k j x ⇒ Object'     φ (Swap k) j x
  , ∀ i x. SwapObjectOf φ k i x ⇒ SwapObject' φ (Swap k) i x
  )
  ⇒ a -|          (Swap k)  φ n m |-> b
  → a -| (SwapF k (Swap k)) φ n m |-> b
fixedCoalg Id          = IdF
fixedCoalg (Emb m)     = EmbF m
fixedCoalg (g `Of`  f) = g `OfF` f
fixedCoalg (f `Par` g) = f `ParF` g
fixedCoalg (Mul pn pm pn' pm' f g) = MulF pn pm pn' pm' f g
fixedCoalg (Ith     i f) = IthF     i f
fixedCoalg (Ith' pn i f) = IthF' pn i f
fixedCoalg Join   = JoinF
fixedCoalg Split  = SplitF
fixedCoalg Assoc  = AssocF
fixedCoalg Sing   = SingF
fixedCoalg Unsing = UnsingF
fixedCoalg (Lift1   f) = Lift1F   f
fixedCoalg (Bising  f) = BisingF  f
fixedCoalg (Bisplit f) = BisplitF f
fixedCoalg (Bijoin  f) = BijoinF  f
fixedCoalg (Biassoc f) = BiassocF f
fixedCoalg (Swap  i j) = SwapF i j
-- fixedCoalg (Swap' ) =
-- fixedCoalg (Permute ) =


{- | Convert a @Swap k@ morphism to a @Swap' k@ morphism. -}
fixed ∷ ∀ k φ n m a b.
  ( -- ∀ i x. ObjectOf φ k i x ⇒ Object' φ (SwapF k (Swap k)) i x  -- Only this Constraint is necessary wherever instances from Cat.Sized.Braided.Free.Instances are in scope.
    ∀ i x. ObjectOf φ       k  i x ⇒ Object' φ (Swap  k) i x
  , ∀ i x. Object   φ (Swap k) i x ⇒ Object' φ (Swap' k) i x
  , ∀ i x. SwapObjectOf   φ k  i x ⇒ SwapObject' φ (Swap k) i x
  , HFunctorObj (SwapF k) φ (Swap k) (Swap' k)
  )
  ⇒ a -| Swap  k φ n m |-> b  -- ^ A @Swap k@ morphism.
  → a -| Swap' k φ n m |-> b  -- ^ A @Fix (SwapF k)@ morphism.
fixed = ana fixedCoalg



-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Swap' k@ morphism to a @Swap k@ morphism. -}
unfixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ k i x ⇒ Object' φ (Swap k) i x
  , ∀ i x. Object φ (Swap k) i x ⇒ Object' φ (Swap' k) i x
  )
  ⇒ a -| Swap' k φ n m |-> b  -- ^ A 'Fix (SwapF k)' morphism.
  → a -| Swap  k φ n m |-> b  -- ^ An equivalent 'Swap k' morphism.
unfixed' (In IdF)         = Id
unfixed' (In (EmbF m))    = Emb m
unfixed' (In (g `OfF`  f)) = unfixed' g `Of`  unfixed' f
unfixed' (In (f `ParF` g)) = unfixed' f `Par` unfixed' g
unfixed' (In (MulF pn pm pn' pm' f g)) = Mul pn pm pn' pm' (unfixed' f) (unfixed' g)
unfixed' (In (IthF     i f)) = Ith     i (unfixed' f)
unfixed' (In (IthF' pn i f)) = Ith' pn i (unfixed' f)
unfixed' (In (JoinF))   = Join
unfixed' (In (SplitF))  = Split
unfixed' (In (AssocF))  = Assoc
unfixed' (In (SingF))   = Sing
unfixed' (In (UnsingF)) = Unsing
unfixed' (In (Lift1F   f)) = Lift1   (unfixed' f)
unfixed' (In (BisingF  f)) = Bising  (unfixed' f)
unfixed' (In (BisplitF f)) = Bisplit (unfixed' f)
unfixed' (In (BijoinF  f)) = Bijoin  (unfixed' f)
unfixed' (In (BiassocF f)) = Biassoc (unfixed' f)
unfixed' (In (SwapF i j)) = Swap i j
-- unfixed' (In SwapF') =
-- unfixed' (In PermuteF) =


{- | Algebra for converting a @Swap' k@ morphism to a @Swap k@ morphism. -}
unfixedAlg ∷ ∀ k φ n m a b.
    a -| SwapF k (Swap k) φ n m |-> b
  → a -|         (Swap k) φ n m |-> b
unfixedAlg IdF          = Id
unfixedAlg (EmbF m)     = Emb m
unfixedAlg (g `OfF`  f) = g `Of` f
unfixedAlg (f `ParF` g) = f `Par` g
unfixedAlg (MulF pn pm pn' pm' f g) = Mul pn pm pn' pm' f g
unfixedAlg (IthF     i f) = Ith     i f
unfixedAlg (IthF' pn i f) = Ith' pn i f
unfixedAlg JoinF   = Join
unfixedAlg SplitF  = Split
unfixedAlg AssocF  = Assoc
unfixedAlg SingF   = Sing
unfixedAlg UnsingF = Unsing
unfixedAlg (Lift1F   f) = Lift1   f
unfixedAlg (BisingF  f) = Bising  f
unfixedAlg (BisplitF f) = Bisplit f
unfixedAlg (BijoinF  f) = Bijoin  f
unfixedAlg (BiassocF f) = Biassoc f
unfixedAlg (SwapF i j)  = Swap i j
-- unfixedAlg (In SwapF') =
-- unfixedAlg (In PermuteF) =


{- | Convert a @Swap' k@ morphism to a @Swap k@ morphism. -}
unfixed ∷ ∀ k φ n m a b.
   -- Both constraints can be satisfied wherever instances from Cat.Sized.Braided.Free.Instances are in scope.
  ( ∀ i x. Object     φ (Swap' k) i x ⇒ Object'     φ (Swap k) i x
  , ∀ i x. SwapObject φ (Swap' k) i x ⇒ SwapObject' φ (Swap k) i x
  )
  ⇒ a -| Swap' k φ n m |-> b  -- ^ A @Swap' k@ morphism.
  → a -| Swap  k φ n m |-> b  -- ^ An equivalent @Swap k@ morphism.
unfixed = cata unfixedAlg




-- TODO lift constraint that the Proxy be the same before and after/make an alternative version?
{- | Given a function that maps primitive morphisms to morphisms in a target
category /t/, this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type).
  ( Braided φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy φ t
  -- ∀ x. ObjectOf k x ⇒ Object' t x
  )
  ⇒ (∀ n m a b. (
              -- ∀ x. ObjectOf k x ⇒ Object' t x
              ObjectOf φ k n a
            , ObjectOf φ k m b
            , Object   φ t n a
            , Object   φ t m b
            )
     ⇒ a -| k φ n m |-> b
     → a -| t φ n m |-> b
     )                            -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → NT' φ (SwapF k t) t -- NatR
  -- → (SwapF k) t :~> t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @φ @t
mkAlg _ (g `OfF` f)      = g ⊙ f
mkAlg α (EmbF    f)      = α f
mkAlg _ (f `ParF` g) = f *** g
mkAlg _ (MulF pn pm pn' pm' f g) = mul pn pm pn' pm' f g
mkAlg _ (IthF     i f) = ith     i f
mkAlg _ (IthF' pn i f) = ith' pn i f
mkAlg _ JoinF   = join
mkAlg _ SplitF  = split
mkAlg _ AssocF  = assoc
mkAlg _ SingF   = sing
mkAlg _ UnsingF = unsing
mkAlg _ (Lift1F   f) = lift1   f
mkAlg _ (BisingF  f) = bising  f
mkAlg _ (BisplitF f) = bisplit f
mkAlg _ (BijoinF  f) = bijoin  f
mkAlg _ (BiassocF f) = biassoc f
mkAlg _ (SwapF i j) = swap i j
-- mkAlg _ SwapF' =
-- mkAlg _ PermuteF =


{- | Alternative to 'foldMap' based on 'cata'. -}
foldMap' ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (n ∷ Nat) (m ∷ Nat)
  (a ∷ κ)   (b ∷ κ).
  ( Braided φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy φ t
  , (∀ i x. Object φ (Fix (SwapF k)) i x ⇒ Object' φ t i x)
  , BraidedFunctor (SwapF k) φ (Fix (SwapF k)) t
  )
  ⇒ (∀ i j x y.
     ( ObjectOf φ k i x
     , ObjectOf φ k j y
     , Object   φ t i x
     , Object   φ t j y
     )
     ⇒ x -| k φ i j |-> y
     → x -| t φ i j |-> y
     )                                 -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → (  a -| Fix (SwapF k) φ n m |-> b
    →  a -|        t      φ n m |-> b
    )
foldMap' α = cata (mkAlg α)
