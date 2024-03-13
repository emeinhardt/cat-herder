{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- |

{- TODO

1. More polymorphic unfold:

 - First try for the special case of Semigroupoids
   where @Object k a = Unconstrained2 k a@.
 - Can proxies + pattern matching aid type inference here?
 - Consider waiting until you port a substantial fraction of @type-aligned@.

-}

module Cat.Unsized.Semigroupoid.Free.Data
  ( SG ( Emb
       , Of
       )
  , HasObject ( ObjectOf
              )
  , ObjectOf'
  , foldMap
  , unfoldMono
  , To (To)
  ) where

import Prelude hiding
  ( (.)
  , foldMap
  , Functor
  )

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained2)

import GHC.Generics (Generic)

-- import Data.Proxy (Proxy (Proxy))

import Data.Functor qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Object'
  )


class HasObject (k ∷ κ → κ → Type) where
  type ObjectOf (k ∷ κ → κ → Type) (a ∷ κ) ∷ Constraint
  type ObjectOf k a = Unconstrained2 k a

{- | This is a "class synonym" for the type family 'ObjectOf'; it's useful
for writing common quantified constraints. -}
class    (ObjectOf k a)
  ⇒ ObjectOf' (k ∷ κ → κ → Type) (a ∷ κ)
instance (ObjectOf k a)
  ⇒ ObjectOf' (k ∷ κ → κ → Type) (a ∷ κ)


data SG (k ∷ κ → κ → Type)
        (a ∷ κ) (b ∷ κ) where
  Emb ∷ ∀ k a b.
      ( ObjectOf k a, ObjectOf k b
      )
      ⇒ a      `k`    b
      → a -| SG k |-> b

  Of  ∷ ∀ k a b x.
      ( ObjectOf k a, ObjectOf k b, ObjectOf k x
      )
      ⇒ x -| SG k |-> b
      → a -| SG k |-> x
      → a -| SG k |-> b

deriving instance (∀ x y. Show (x -| k |-> y)) ⇒ Show (a -| SG k |-> b)


{- | This is a proxy type with two tags, and which hence may sometimes be useful
for defining free semigroupoids. -}
data To (a ∷ κ) (b ∷ κ) = To
  deriving stock (Eq, Ord, Read, Show, Generic, F.Functor, Foldable, Traversable, Enum, Bounded)



foldMap ∷ ∀ κ
          (k ∷ κ → κ → Type)
          (t ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ).
        ( ObjectOf k a, ObjectOf k b
        , Object   t a, Object   t b
        , ∀ x. ObjectOf k x ⇒ Object' t x
        , Semigroupoid (SG k), Semigroupoid t
        )
        ⇒
        (∀ x y.
          ( ObjectOf k x, ObjectOf k y
          , Object   t x, Object   t y
          )
          ⇒ x `k` y
          → x `t` y
        )                               -- ^ A function maps primitive morphisms into the target category.
        → a -| SG k |-> b               -- ^ A path in the free semigroupoid over @k@.
        → a    `t`      b               -- ^ The resulting morphism in @t@.
foldMap α (Emb f)    = α f
foldMap α (g `Of` f) = foldMap α g . foldMap α f


{- | Unfold for free paths into and out of one object. -}
unfoldMono ∷ ∀ κ
               q
              (k ∷ κ → κ → Type)
              (a ∷ κ).
        ( ObjectOf k a
        , Semigroupoid (SG k)
        )
        ⇒ (q → Either (a `k` a) (q, q))
        → q
        → SG k a a
unfoldMono δ z = case δ z of
  (Left   f   ) → Emb f
  (Right (l,r)) → unfoldMono δ l `Of` unfoldMono δ r
