{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- |

module Cat.Sized.Semigroupoid.Free.Data
  ( SG ( Emb
       , Of
       )
  , HasObject ( ObjectOf
              )
  , ObjectOf'
  , foldMap

  , P (P)
  , To (To)
  ) where

import Prelude hiding
  ( (.)
  , foldMap
  , Functor
  )

import Data.Functor qualified as F

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained4)
import GHC.TypeNats (Nat, KnownNat)

import GHC.Generics (Generic)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Object'
  )

-- import Data.Comp.Multi.HFunctor


class HasObject (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type ObjectOf (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type ObjectOf φ k n a = Unconstrained4 φ k n a

{- | This is a "class synonym" for the type family 'ObjectOf'; it's often needed
to write quantified constraints. -}
class    (ObjectOf φ k n a)
  ⇒ ObjectOf' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (ObjectOf φ k n a)
  ⇒ ObjectOf' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


data SG (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
        (n ∷ Nat) (m ∷ Nat)
        (a ∷ κ)   (b ∷ κ)   where

  Emb ∷ ∀ φ k n m a b.
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a, ObjectOf φ k m b
      )
      ⇒ a -|    k φ n m |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/ to lift into the free semigroupoid.
      → a -| SG k φ n m |-> b

  Of  ∷ ∀ φ k n m l a b x.
      ( KnownNat n, KnownNat m, KnownNat l
      , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
      )
      ⇒ x -| SG k φ l m |-> b  -- ^ A free /k/-morphism from /φ l x/ to /φ m b/.
      → a -| SG k φ n l |-> x  -- ^ A free /k/-morphism from /φ n a/ to /φ l x/.
      → a -| SG k φ n m |-> b

deriving instance (∀ i j x y. Show (x -| k φ i j |-> y)) ⇒ Show (a -| SG k φ n m |-> b)


{- | This is a sized functor where the putative payload type @a@ is phantom, hence
it may be useful for defining free semigroupoids. -}
data P (n ∷ Nat) (a ∷ κ) = P
  deriving stock (Eq, Ord, Read, Show, Generic, F.Functor, Foldable, Traversable, Enum, Bounded)

{- | This is a proxy type with two tags (and two sizes), and which hence may sometimes be useful
for defining free semigroupoids. -}
data To  (φ ∷ Nat → κ → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) = To
  deriving stock (Eq, Ord, Read, Show, Generic, F.Functor, Foldable, Traversable, Enum, Bounded)
instance HasObject P To




-- foldMap ∷ ∀ κ
--           (φ ∷  Nat → κ → κ)
--           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (n ∷ Nat) (m ∷ Nat)
--           (a ∷ κ)   (b ∷ κ).
--        -- ( Object φ (SG k) n a, Object φ (SG k) m b
--        ( ObjectOf φ k n a, ObjectOf φ k m b
--        -- , Object φ (SG k) n a, Object φ (SG k) m b
--        , Object φ  t     n a, Object φ  t     m b
--        -- , ∀ i x. Object φ (SG k) i x ⇒ Object' φ  t     i x
--        -- , ∀ i x. Object φ  t     i x ⇒ Object' φ (SG k) i x
--        -- , ∀ i x. Object' φ (SG k) i x ⇒ Object' φ  t     i x
--        -- , ∀ i x. Object' φ  t     i x ⇒ Object' φ (SG k) i x
--        , ∀ i x. ObjectOf φ     k  i x ⇒ Object' φ  t     i x
--        -- , ∀ i x. Object   φ  t     i x ⇒ ObjectOf' φ     k  i x
--        -- , ∀ i x. ObjectOf' φ     k  i x ⇒ Object' φ  t     i x
--        -- , ∀ i x. Object'   φ  t     i x ⇒ ObjectOf' φ     k  i x
--        , Semigroupoid φ (SG k), Semigroupoid φ t
--        )
--        ⇒ (∀ i j x y.
--           ( Object φ (SG k) i x, Object φ (SG k) j y
--           -- ( ObjectOf φ k    i x, ObjectOf φ k    j y
--           -- , Object φ (SG k) i x, Object φ (SG k) j y
--           , Object φ  t     i x, Object φ  t     j y
--           )
--           -- ⇒ x -|     k  φ i j |-> y
--           ⇒ x -| (SG k) φ i j |-> y
--           → x -|  t     φ i j |-> y
--          )
--        → a -| (SG k) φ n m |-> b
--        → a -|  t     φ n m |-> b
-- -- foldMap τ (g `Of` f) = undefined
-- foldMap τ (g `Of` f) = foldMap τ g . foldMap τ f

foldMap ∷ ∀ κ
          (φ ∷  Nat → κ → κ)
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        -- ( Object φ (SG k) n a, Object φ (SG k) m b
        ( ObjectOf φ k n a, ObjectOf φ k m b
        -- , Object φ (SG k) n a, Object φ (SG k) m b
        , Object φ  t     n a, Object φ  t     m b
        -- , ∀ i x. Object φ (SG k) i x ⇒ Object' φ  t     i x
        -- , ∀ i x. Object φ  t     i x ⇒ Object' φ (SG k) i x
        -- , ∀ i x. Object' φ (SG k) i x ⇒ Object' φ  t     i x
        -- , ∀ i x. Object' φ  t     i x ⇒ Object' φ (SG k) i x
        , ∀ i x. ObjectOf φ     k  i x ⇒ Object' φ  t     i x
        -- , ∀ i x. Object   φ  t     i x ⇒ ObjectOf' φ     k  i x
        -- , ∀ i x. ObjectOf' φ     k  i x ⇒ Object' φ  t     i x
        -- , ∀ i x. Object'   φ  t     i x ⇒ ObjectOf' φ     k  i x
        , Semigroupoid φ (SG k), Semigroupoid φ t
        )
        ⇒
        (∀ i j x y.
          -- ( Object φ (SG k) i x, Object φ (SG k) j y
          ( ObjectOf φ k    i x, ObjectOf φ k    j y
          -- , Object φ (SG k) i x, Object φ (SG k) j y
          , Object φ  t     i x, Object φ  t     j y
          )
          ⇒ x -|     k  φ i j |-> y
          -- ⇒ x -| (SG k) φ i j |-> y
          → x -|  t     φ i j |-> y
        )                            -- ^ A function maps primitive morphisms into the target category.
        → a -| (SG k) φ n m |-> b    -- ^ A path in the free category over @k@.
        → a -|   t    φ n m |-> b    -- ^ The resulting morphism in @t@.
foldMap α (Emb f)    = α f
foldMap α (g `Of` f) = foldMap α g . foldMap α f


-- -- TODO Confirm that GHC can actually infer types using this, then clean up and
-- -- export.
-- -- Regardless, consider a variation of @foldMap'@ here with a parameter
-- -- @nt ∷ (∀ n a. (KnownNat n) ⇒ φ n a → γ n a)@ mapping φ products to γ products
-- -- in Hask.
-- foldMap' ∷ ∀ κ
--           (φ ∷  Nat → κ → κ)
--           (γ ∷  Nat → κ → κ)
--           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (n ∷ Nat) (m ∷ Nat)
--           (a ∷ κ)   (b ∷ κ).
--         -- ( Object φ (SG k) n a, Object φ (SG k) m b
--         ( ObjectOf φ k n a, ObjectOf φ k m b
--         -- , Object φ (SG k) n a, Object φ (SG k) m b
--         , Object γ  t     n a, Object γ  t     m b
--         -- , ∀ i x. Object φ (SG k) i x ⇒ Object' φ  t     i x
--         -- , ∀ i x. Object φ  t     i x ⇒ Object' φ (SG k) i x
--         -- , ∀ i x. Object' φ (SG k) i x ⇒ Object' φ  t     i x
--         -- , ∀ i x. Object' φ  t     i x ⇒ Object' φ (SG k) i x
--         , ∀ i x. ObjectOf φ     k  i x ⇒ Object' γ  t     i x
--         -- , ∀ i x. Object   φ  t     i x ⇒ ObjectOf' φ     k  i x
--         -- , ∀ i x. ObjectOf' φ     k  i x ⇒ Object' φ  t     i x
--         -- , ∀ i x. Object'   φ  t     i x ⇒ ObjectOf' φ     k  i x
--         , Semigroupoid φ (SG k), Semigroupoid γ t
--         )
--         ⇒ (∀ i j x y.
--            -- ( Object φ (SG k) i x, Object φ (SG k) j y
--            ( ObjectOf φ k    i x, ObjectOf φ k    j y
--            -- , Object φ (SG k) i x, Object φ (SG k) j y
--            , Object γ  t     i x, Object γ  t     j y
--            )
--            ⇒ x -|     k  φ i j |-> y
--            -- ⇒ x -| (SG k) φ i j |-> y
--            → x -|  t     γ i j |-> y
--         )                            -- ^ A function maps primitive morphisms into the target category.
--         → a -| (SG k) φ n m |-> b    -- ^ A path in the free category over @k@.
--         → a -|   t    γ n m |-> b    -- ^ The resulting morphism in @t@.
-- foldMap' α (Emb f)    = α f
-- foldMap' α (g `Of` f) = foldMap' α g . foldMap' α f
