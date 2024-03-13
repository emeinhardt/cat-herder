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

   -- * Re-exports from "Cat.Unsized.Semigroupoid.Free.Data"
  , HasObject (ObjectOf)
  ) where

import Prelude hiding
  ( id
  , (.)
  , foldMap
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
        -- , out
        )
  , cata, (:~>)
  -- , ana
  )

import Cat.Unsized.Semigroupoid.Class
  ( Object
  , Object'
  , (.)
  )
import Cat.Unsized.Category.Class
  ( Category ( id
             )
  )
import Cat.Unsized.Semigroupoid.Free.Data
  ( HasObject (ObjectOf)
  )


-- NOTE The constraints in this file are currently slightly different from those
-- of other free categories:
--
-- >  Object (Cat k) a
--
-- instead of
--
-- > ObjectOf k a
--
-- The idea is that the current design (ObjectOf) seen elsewhere couples
-- something more fundamental and likely to continue to be useful (a free
-- category type) to something more ephemeral and brittle — a particular
-- derivation path for typeclass inference.

data Cat (k ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ) where
  Emb ∷ ( Object (Cat k) a
        , Object (Cat k) b
        )
      ⇒ a -|     k |-> b
      → a -| Cat k |-> b
  Id  ∷ ( Object (Cat k) a
        )
      ⇒ Cat k a a
  Of  ∷ ( Object (Cat k) a
        , Object (Cat k) b
        , Object (Cat k) c
        )
      ⇒ b -| Cat k |-> c
      → a -| Cat k |-> b
      → a -| Cat k |-> c

deriving instance (∀ x y. Show (x `k` y)) ⇒ Show (a -| Cat k |-> b)




foldMap ∷ ∀ k t a b.
        (
        --   ObjectOf k a, ObjectOf k b
        -- , Object   t a, Object   t b
        -- , ∀ x. ObjectOf k x ⇒ Object' t x
        -- , Category (Cat k), Category t

          Object (Cat k) a , Object (Cat k) b
        , ∀ o. Object (Cat k) o ⇒ Object' t o
        , Category (Cat k), Category t
        )
        ⇒ (∀ x y.
           -- ( -- ObjectOf k x, ObjectOf k y
           --   Object   k x, Object   k y
           -- , Object   t x, Object   t y
           -- , ∀ z. Object k z ⇒ Object' t z
           -- -- , ∀ z. ObjectOf k z ⇒ Object' t z
           -- )
           -- ⇒
           (x `k` y) → (x `t` y)
        )                             -- ^ A function maps primitive morphisms into the target category.
        → a -| Cat k |-> b            -- ^ A path in the free category over @k@.
        → a    `t`       b            -- ^ The resulting morphism in @t@.
foldMap α (Emb f)    = α f
foldMap _  Id        = id
foldMap α (g `Of` f) = foldMap α g . foldMap α f


-- TODO
-- {- | Convert a 'Cat k' morphism to a 'Cat\' k' morphism. -}
-- fixed' ∷ ∀ k a b.
--   ( Object (Cat k) a, Object (Cat k) b
--   , ObjectOf k a, ObjectOf k b
--   -- , ∀ x. ObjectOf    k  x ⇒ Object' (Cat  k) x
--   , ∀ x. Object (Cat k) x ⇒ Object' (Cat' k) x
--   )
--   ⇒ a -| Cat  k |-> b
--   → a -| Cat' k |-> b
-- fixed' Id         = In IdF
-- fixed' (Emb m)    = In (EmbF m)
-- fixed' (g `Of` f) = In (fixed' g `OfF` fixed' f)

-- fixedCoalg ∷
--   Cat k ::~> CatF k (Cat k)
-- fixedCoalg Id         = IdF
-- fixedCoalg (Emb m)    = EmbF m
-- fixedCoalg (g `Of` f) = g `OfF` f


-- fixed ∷ ∀ k a b.
--   ( -- ObjectOf k a, ObjectOf k b
--     -- , ∀ x. ObjectOf k x ⇒ Object' (Cat k) x
--     ∀ x. Object (Cat k) x ⇒ Object' (Cat' k) x
--   )
--   ⇒ a -| Cat  k |-> b
--   → a -| Cat' k |-> b
-- fixed = ana fixedCoalg



{- | Pattern functor for 'Cat'. -}
data CatF (k ∷ κ → κ → Type)
          (t ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) where
  EmbF ∷ ∀ k t a b.
       ( ObjectOf k a, ObjectOf k b
       , Object   t a, Object   t b
       )
       ⇒
       -- ( Object (CatF k t) a, Object (CatF k t) b
       -- )
       -- ⇒
                k a b
       → CatF k t a b

  IdF  ∷ ∀ k t a.
       ( ObjectOf k a
       , Object   t a
       )
       ⇒
       -- ( Object (CatF k t) a
       -- )
       -- ⇒
          CatF k t a a

  OfF  ∷ ∀ k t a b x.
       ( ObjectOf k a, ObjectOf k b, ObjectOf k x
       , Object   t a, Object   t b, Object   t x
       )
       ⇒
       -- ( Object (CatF k t) a, Object (CatF k t) b, Object (CatF k t) x
       -- )
       -- ⇒
                t x b
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
category /t/, this constructs an algebra for recursion schemes. -}
mkAlg ∷ ∀ κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type).
  ( Category t
  -- ∀ x. ObjectOf k x ⇒ Object' t x
  )
  ⇒ (∀ a b. (
              -- ∀ x. ObjectOf k x ⇒ Object' t x
              ObjectOf k a
            , ObjectOf k b
            , Object   t a
            , Object   t b
            )
     ⇒ a `k` b
     → a `t` b
     )
  → CatF k t ::~> t -- NatR
  -- → (CatF k) t :~> t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @t @a
mkAlg _ (g `OfF` f) = g . f
mkAlg α (EmbF    f) = α f


foldMap' ∷ ∀ κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ).
  ( Category t
  -- , ObjectOf k a
  -- , ObjectOf k b
  -- , ∀ x. ObjectOf k x ⇒ Object' t x
  , Object (Fix (CatF k)) a
  , Object (Fix (CatF k)) b
  -- , (∀ x. Object (Fix η) x ⇒ Object' (η (Fix η)) x)
  -- , (∀ x. Object (Fix (CatF k)) x ⇒ Object' ((CatF k) t) x) -- restore
  , (∀ x. Object (Fix (CatF k)) x ⇒ Object'    t        x)
  )
  ⇒ (∀ x y. (
              -- ∀ x. ObjectOf k x ⇒ Object' t x
              ObjectOf k x
            , ObjectOf k y
            , Object   t x
            , Object   t y
            )
     ⇒ x `k` y
     → x `t` y
     )
  → (  a -| Fix (CatF k) |-> b
    →  a        `t`          b
    )
foldMap' α = cata (mkAlg α)
