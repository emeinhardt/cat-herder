{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Category.Free.Data
  ( Cat ( Emb
        , Id
        , Of
        )
  , foldMap

   -- * Recursion schemes
  , CatF ( EmbF
         , IdF
         , OfF
         )
  , Cat'
  , mkAlg
  , foldMap'
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
  ( id
  , (.)
  , foldMap
  , head
  , last
  )

import Data.Kind (Type)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Functor
  ( (::~>)
  , HFunctor ( hfmap
             )
  , Fix ( In
        )
  , cata
  , ana
  )

import Cat.Unsized.Category.Class
  ( Category ( id
             )
  , (.)
  , Object
  , Object'
  )
import Cat.Unsized.Semigroupoid.Free.Data
  ( HasObject (ObjectOf)
  )


data Cat (k ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ) where
  Emb ∷ ( ObjectOf k a
        , ObjectOf k b
        )
      ⇒ a -|     k |-> b
      → a -| Cat k |-> b
  Id  ∷ ( ObjectOf k a
        )
      ⇒ a -| Cat k |-> a
  Of  ∷ ( ObjectOf k a
        , ObjectOf k b
        , ObjectOf k c
        )
      ⇒ b -| Cat k |-> c
      → a -| Cat k |-> b
      → a -| Cat k |-> c

deriving instance (∀ x y. Show (x `k` y)) ⇒ Show (a -| Cat k |-> b)




foldMap ∷ ∀ k t a b.
        ( ObjectOf k a, ObjectOf k b
        , ∀ o. ObjectOf k o ⇒ Object' t o
        , Category (Cat k), Category t
        )
        ⇒ (∀ x y.
           (x `k` y) → (x `t` y)
        )                             -- ^ A function maps primitive morphisms into the target category.
        → a -| Cat k |-> b            -- ^ A path in the free category over @k@.
        → a    `t`       b            -- ^ The resulting morphism in @t@.
foldMap α (Emb f)    = α f
foldMap _  Id        = id
foldMap α (g `Of` f) = foldMap α g . foldMap α f


-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixed' ∷ ∀ k a b.
  ( ObjectOf k a, ObjectOf k b
  , ∀ x. ObjectOf k x ⇒ Object' (Cat' k) x
  )
  ⇒ a -| Cat  k |-> b        -- ^ A @Cat k@ morphism.
  → a -| Cat' k |-> b        -- ^ An equivalent morphism in @Fix (CatF k)@.
fixed' Id         = In IdF
fixed' (Emb m)    = In (EmbF m)
fixed' (g `Of` f) = In (fixed' g `OfF` fixed' f)


{- | Coalgebra for converting a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixedCoalg ∷ ∀ k a b.
  (∀ x. ObjectOf k x ⇒ Object' (Cat k) x)
  ⇒ a -|         Cat k  |-> b
  → a -| CatF k (Cat k) |-> b
fixedCoalg Id         = IdF
fixedCoalg (Emb m)    = EmbF m
fixedCoalg (g `Of` f) = g `OfF` f


{- | Convert a @Cat k@ morphism to a @Cat' k@ morphism. -}
fixed ∷ ∀ k a b.
  ( ∀ x. ObjectOf k x ⇒ Object' (Cat k) x
  , ∀ x. Object (Cat k) x ⇒ Object' (Cat' k) x
  )
  ⇒ a -| Cat  k |-> b  -- ^ A @Cat k@ morphism.
  → a -| Cat' k |-> b  -- ^ An equivalent morphism in @Fix (CatF k)@.
fixed = ana fixedCoalg



-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @unfixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixed' ∷ ∀ k a b.
  ( ObjectOf k a, ObjectOf k b
  , ∀ x. ObjectOf k x ⇒ Object' (Cat k) x
  , ∀ x. Object (Cat k) x ⇒ Object' (Cat' k) x
  )
  ⇒ a -| Cat' k |-> b  -- ^ A @Fix (CatF k)@ morphism.
  → a -| Cat  k |-> b  -- ^ An equivalent @Cat k@ morphism.
unfixed' (In IdF)         = Id
unfixed' (In (EmbF m))    = Emb m
unfixed' (In (g `OfF` f)) = unfixed' g `Of` unfixed' f


{- | Algebra for converting a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixedAlg ∷ ∀ k a b.
    a -| CatF k (Cat k) |-> b
  → a -|         Cat k  |-> b
unfixedAlg IdF         = Id
unfixedAlg (g `OfF` f) = g `Of` f
unfixedAlg (EmbF m)    = Emb m


{- | Convert a @Cat' k@ morphism to a @Cat k@ morphism. -}
unfixed ∷ ∀ k a b.
  (∀ x. Object (Cat' k) x ⇒ Object' (Cat k) x)  -- Constraint can be satisfied wherever instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -| Cat' k |-> b  -- ^ A @Cat' k@ morphism.
  → a -| Cat  k |-> b  -- ^ An equivalent @Cat k@ morphism.
unfixed = cata unfixedAlg



{- | Pattern functor for 'Cat'. -}
data CatF (k ∷ κ → κ → Type)
          (t ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) where
  EmbF ∷ ∀ k t a b.
       ( ObjectOf k a, ObjectOf k b
       , Object   t a, Object   t b
       )
       ⇒        k a b
       → CatF k t a b

  IdF  ∷ ∀ k t a.
       ( ObjectOf k a
       , Object   t a
       )
       ⇒ CatF k t a a

  OfF  ∷ ∀ k t a b x.
       ( ObjectOf k a, ObjectOf k b, ObjectOf k x
       , Object   t a, Object   t b, Object   t x
       )
       ⇒        t x b
       →        t a x
       → CatF k t a b

deriving instance ( ∀ x y. Show (x -| k |-> y)
                  , ∀ x y. Show (x -| t |-> y)
                  )
  ⇒ Show (a -| CatF k t |-> b)


type Cat' k = Fix (CatF k)

instance HFunctor (CatF k) where
  hfmap _ (EmbF m)    = EmbF m
  hfmap _ IdF         = IdF
  hfmap α (g `OfF` f) = α g `OfF` α f


{- | Given a function that maps primitive morphisms to morphisms in a target
category /t/, this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type).
  (Category t)
  ⇒ (∀ a b. ( ObjectOf k a, Object   t a
            , ObjectOf k b, Object   t b
            )
     ⇒ a `k` b
     → a `t` b
     )               -- ^ A function mapping primitive morphisms into the target category.
  → CatF k t ::~> t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @t @a
mkAlg _ (g `OfF` f) = g . f
mkAlg α (EmbF    f) = α f


{- | Alternative to 'foldMap' based on 'cata'. -}
foldMap' ∷ ∀ κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ).
  ( Category t
  -- , Object (Fix (CatF k)) a
  -- , Object (Fix (CatF k)) b
  , (∀ x. Object (Fix (CatF k)) x ⇒ Object' t x)
  )
  ⇒ (∀ x y.
     ( ObjectOf k x, Object t x
     , ObjectOf k y, Object t y
     )
     ⇒ x `k` y
     → x `t` y
     )                         -- ^ A function mapping primitive morphisms into the target category.
  → (  a -| Fix (CatF k) |-> b
    →  a        `t`          b
    )
foldMap' α = cata (mkAlg α)
