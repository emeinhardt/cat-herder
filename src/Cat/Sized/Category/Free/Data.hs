{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- |

module Cat.Sized.Category.Free.Data
  ( Cat ( Emb
        , Of
        , Id
        )
  , foldMap
  -- , foldMap_
  , P (P)
  , To (To)

   -- * Recursion schemes
  , CatF ( EmbF
         , IdF
         , OfF
         )
  , Cat'
  , foldMap'
  , mkAlg
  , fixed
  , fixedCoalg
  , fixed'
  , unfixed
  , unfixedAlg
  , unfixed'

   -- * Re-exports from "Cat.Unsized.Semigroupoid.Free.Data"
  , HasObject (ObjectOf)
  ) where

import Prelude hiding
  ( (.)
  , id
  , foldMap
  )

import GHC.TypeNats (Nat, KnownNat)
import Data.Kind (Type)

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

import Cat.Sized.Category.Class
  ( Category (id)
  , (.)
  , Object
  , Object'
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( HasObject ( ObjectOf )
  , P (P)
  , To (To)
  )



data Cat (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
         (n ∷ Nat) (m ∷ Nat)
         (a ∷ κ)   (b ∷ κ)   where
  Emb ∷ ∀ φ k n m a b.
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a, ObjectOf φ k m b
      )
      ⇒ a -|     k φ n m |-> b
      → a -| Cat k φ n m |-> b
  Of  ∷ ∀ φ k n m l a b x.
      ( KnownNat n, KnownNat m, KnownNat l
      , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
      )
      ⇒ x -| Cat k φ l m |-> b
      → a -| Cat k φ n l |-> x
      → a -| Cat k φ n m |-> b
  Id  ∷ ∀ φ k n a.
      ( KnownNat n
      , ObjectOf φ k n a
      )
      ⇒ a -| Cat k φ n n |-> a

deriving instance (∀ i j x y. Show (x -| k φ i j |-> y)) ⇒ Show (a -| Cat k φ n m |-> b)



foldMap ∷ ∀ κ
          (φ ∷  Nat → κ → κ)
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( ObjectOf φ k n a, ObjectOf φ k m b
        , Object   φ t n a, Object   φ t m b
        , ∀ i x. ObjectOf φ k i x ⇒ Object' φ t i x
        , Category φ (Cat k), Category φ t
        )
        ⇒
        (∀ i j x y.
          ( ObjectOf φ k i x, ObjectOf φ k j y
          , Object   φ t i x, Object   φ t j y
          )
          ⇒ x -| k φ i j |-> y
          → x -| t φ i j |-> y
        )                             -- ^ A function maps primitive morphisms into the target category.
        → a -| (Cat k) φ n m |-> b    -- ^ A path in the free category over @k@.
        → a -|   t     φ n m |-> b    -- ^ The resulting morphism in @t@.
foldMap α (Emb f)    = α f
foldMap _  Id        = id
foldMap α (g `Of` f) = foldMap α g . foldMap α f


-- TODO @limbo-test: Confirm that GHC can actually infer types using this, then clean up and export.
-- foldMap_ ∷ ∀ κ
--           (φ ∷  Nat → κ → κ)
--           (γ ∷  Nat → κ → κ)
--           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (n ∷ Nat) (m ∷ Nat)
--           (a ∷ κ)   (b ∷ κ).
--         ( ObjectOf φ k n a, ObjectOf φ k m b
--         , Object   γ t n a, Object   γ t m b
--         , ∀ i x. ObjectOf φ k i x ⇒ Object' γ t i x
--         , Category φ (Cat k), Category γ t
--         )
--         ⇒ (∀ i j x y.
--            ( ObjectOf φ k i x, ObjectOf φ k j y
--            , Object   γ t i x, Object   γ t j y
--            )
--            ⇒ x -| k φ i j |-> y
--            → x -| t γ i j |-> y
--         )                             -- ^ A function maps primitive morphisms into the target category.
--         → a -| (Cat k) φ n m |-> b    -- ^ A path in the free category over @k@.
--         → a -|   t     γ n m |-> b    -- ^ The resulting morphism in @t@.
-- foldMap_ α (Emb f)    = α f
-- foldMap_ _  Id        = id
-- foldMap_ α (g `Of` f) = foldMap_ α g . foldMap_ α f



{- | Pattern functor for 'Cat'. -}
data CatF (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (φ ∷ Nat → κ → κ)
          -- (γ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   where

  EmbF ∷ ∀ φ k t n m a b.
       ( KnownNat n, KnownNat m
       , ObjectOf φ k n a, ObjectOf φ k m b
       , Object   φ t n a, Object   φ t m b
       )
       ⇒ a -|      k φ     n m |-> b
       → a -| CatF k t φ   n m |-> b

  IdF ∷ ∀ φ k t n a.
      ( KnownNat n
      , ObjectOf φ k n a
      , Object   φ t n a
      )
      ⇒ a -| CatF k t φ   n n |-> a

  OfF ∷ ∀ φ k t n m l a b x.
      ( KnownNat n, KnownNat m, KnownNat l
      , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
      , Object   φ t n a, Object   φ t m b, Object   φ t l x
      )
      ⇒ x -|          t φ l m |-> b
      → a -|          t φ n l |-> x
      → a -| CatF k t φ   n m |-> b

deriving instance ( ∀ i j x y. Show (x -| k φ i j |-> y)
                  , ∀ i j x y. Show (x -| t φ i j |-> y)
                  )
  ⇒ Show (a -| CatF k t φ n m |-> b)


type Cat' k = Fix (CatF k)

instance HFunctor (CatF k) where
  hfmap _ (EmbF m)    = EmbF m
  hfmap _ IdF         = IdF
  hfmap α (g `OfF` f) = α g `OfF` α f


{- | Given a function that maps primitive morphisms to morphisms in a target
category /t/, this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type).
  ( Category φ t
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
  → NT' φ (CatF k t) t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @φ @t
mkAlg _ (g `OfF` f)      = g . f
mkAlg α (EmbF    f)      = α f


{- | Alternative to 'foldMap' based on 'cata'. -}
foldMap' ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (n ∷ Nat) (m ∷ Nat)
  (a ∷ κ)   (b ∷ κ).
  ( Category φ t
  -- , Object φ (Fix (CatF k)) n a
  -- , Object φ (Fix (CatF k)) m b
  , (∀ i x. Object φ (Fix (CatF k)) i x ⇒ Object' φ t i x)
  )
  ⇒ (∀ i j x y.
     ( ObjectOf φ k i x
     , ObjectOf φ k j y
     , Object   φ t i x
     , Object   φ t j y
     )
     ⇒ x -| k φ i j |-> y
     → x -| t φ i j |-> y
     )                                -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → (  a -| Fix (CatF k) φ n m |-> b
    →  a -|        t     φ n m |-> b
    )
foldMap' α = cata (mkAlg α)


-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ      k  i x ⇒ Object' φ (Cat  k) i x
  , ∀ i x. Object   φ (Cat k) i x ⇒ Object' φ (Cat' k) i x
  )
  ⇒ a -| Cat  k φ n m |-> b  -- ^ A @Cat k@ morphism.
  → a -| Cat' k φ n m |-> b  -- ^ An equivalent morphism in @Fix (CatF k)@.
fixed' Id         = In IdF
fixed' (Emb m)    = In (EmbF m)
fixed' (g `Of` f) = In (fixed' g `OfF` fixed' f)


{- | Coalgebra for converting a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixedCoalg ∷ ∀ φ k n m a b.
  ( ∀ j x. ObjectOf φ k j x ⇒ Object' φ (Cat k) j x)  -- Constraint can be satisfied wherever instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -|         (Cat k)  φ n m |-> b
  → a -| (CatF k (Cat k)) φ n m |-> b
fixedCoalg Id         = IdF
fixedCoalg (Emb m)    = EmbF m
fixedCoalg (g `Of` f) = g `OfF` f


{- | Convert a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixed ∷ ∀ k φ n m a b.
  ( -- ∀ i x. ObjectOf φ k i x ⇒ Object' φ (CatF k (Cat k)) i x  -- Only this Constraint is necessary wherever instances from Cat.Sized.Category.Free.Instances are in scope.
    ∀ i x. ObjectOf φ k i x ⇒ Object' φ (Cat k) i x
  , ∀ i x. Object φ (Cat k) i x ⇒ Object' φ (Cat' k) i x
  , HFunctorObj (CatF k) φ (Cat k) (Cat' k)
  )
  ⇒ a -| Cat  k φ n m |-> b  -- ^ A @Cat k@ morphism.
  → a -| Cat' k φ n m |-> b  -- ^ A @Fix (CatF k)@ morphism.
fixed = ana fixedCoalg


-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @unfixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ k i x ⇒ Object' φ (Cat k) i x
  , ∀ i x. Object φ (Cat k) i x ⇒ Object' φ (Cat' k) i x
  )
  ⇒ a -| Cat' k φ n m |-> b  -- ^ A @Fix (CatF k)@ morphism.
  → a -| Cat  k φ n m |-> b  -- ^ An equivalent @Cat k@ morphism.
unfixed' (In IdF)         = Id
unfixed' (In (EmbF m))    = Emb m
unfixed' (In (g `OfF` f)) = unfixed' g `Of` unfixed' f


{- | Algebra for converting a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixedAlg ∷ ∀ k φ n m a b.
    a -| CatF k (Cat k) φ n m |-> b
  → a -|        (Cat k) φ n m |-> b
unfixedAlg IdF         = Id
unfixedAlg (g `OfF` f) = g `Of` f
unfixedAlg (EmbF m)    = Emb m


{- | Convert a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixed ∷ ∀ k φ n m a b.
  (∀ i x. Object φ (Cat' k) i x ⇒ Object' φ (Cat k) i x)  -- Constraint can be satisfied wherever instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -| Cat' k φ n m |-> b  -- ^ A @Cat' k@ morphism.
  → a -| Cat  k φ n m |-> b  -- ^ An equivalent @Cat k@ morphism.
unfixed = cata unfixedAlg
