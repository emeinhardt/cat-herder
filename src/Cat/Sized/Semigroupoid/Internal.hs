{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Sized.Semigroupoid.Internal
  ( ISemigroupoid ( IObject
                  , (.)
                  )
  , IObject'
  , (⋄)
  -- , IPoint
  , One (One, unOne)
  , one
  ) where

import Prelude hiding
  ( (.)
  , Functor
  , fmap
  )

import GHC.Generics (Generic)
import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4
  )
import GHC.TypeNats (Nat, KnownNat)

import Data.Functor qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class qualified as S



-- type family IPoint (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) ∷ κ where
--   IPoint φ (One a k) = a

-- -- type family IPoint' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (a ∷ κ) ∷ κ where
-- --   IPoint' φ k a = a

{- | A semigroupoid on one object, presumably internal to some ambient semigroupoid. -}
class ISemigroupoid (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (a ∷ κ) where
  type IObject (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (x ∷ κ) ∷ Constraint
  type IObject φ k n x = Unconstrained4 φ k n x

  infixr 9 .
  (.) ∷ ∀ (n ∷ Nat) (m ∷ Nat) (l ∷ Nat).
      ( KnownNat n, KnownNat m, KnownNat l
      , IObject φ k n a, IObject φ k m a, IObject φ k l a
      )
       ⇒ a -| k φ l m |-> a  -- ^ A morphism from @φ l a@ to @φ m a@.
       → a -| k φ n l |-> a  -- ^ A morphism from @φ n a@ to @φ l a@.
       → a -| k φ n m |-> a  -- ^ A morphism from @φ n a@ to @φ m a@.

infixr 9 ⋄
(⋄) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat) (l ∷ Nat) (a ∷ κ).
    (
      KnownNat n, KnownNat m, KnownNat l
    , IObject φ k n a, IObject φ k m a, IObject φ k l a
    , ISemigroupoid φ k a
    )
    ⇒ a -| k φ l m |-> a  -- ^ A morphism from @φ l a@ to @φ m a@.
    → a -| k φ n l |-> a  -- ^ A morphism from @φ n a@ to @φ l a@.
    → a -| k φ n m |-> a  -- ^ A morphism from @φ n a@ to @φ m a@.
(⋄) = (.)


{- | This is a "class synonym" for the type family 'IObject'; it's often needed to
write quantified constraints. -}
class    (IObject φ k n a)
  ⇒ IObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (IObject φ k n a)
  ⇒ IObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


{- | Newtype for treating an internal semigroupoid as a more semigroupoid where
constraints limit the objects of the category to exactly the single object of
the internal semigroupoid. -}
newtype One (o ∷ κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) =
  One { unOne ∷ a -| k φ n m |-> b }
-- newtype One k φ n m a b = One { unOne ∷ a -| k φ n m |-> b }
  deriving stock Generic

{- | Smart constructor for 'One'. -}
one ∷ ∀ φ k n m a. ISemigroupoid φ k a
    ⇒ a -| k φ n m |-> a → One a k φ n m a a
one = One

deriving instance (Show (k φ n m a b)) ⇒ Show (One a k φ n m a b)
deriving instance (Eq   (k φ n m a b)) ⇒ Eq   (One a k φ n m a b)
deriving instance (Ord  (k φ n m a b)) ⇒ Ord  (One a k φ n m a b)
deriving instance (F.Functor   (k φ n m a)) ⇒ F.Functor   (One a k φ n m a)
deriving instance (Foldable    (k φ n m a)) ⇒ Foldable    (One a k φ n m a)
deriving instance (Traversable (k φ n m a)) ⇒ Traversable (One a k φ n m a)

instance (ISemigroupoid φ k a) ⇒ S.Semigroupoid φ (One a k) where
  type Object φ (One a k) n x = (IObject φ k n x , x ~ a)
  -- type Object φ (One a k) n x = (IObject φ k n x , x ~ IPoint φ (One a k))
  -- type Object φ (One a k) n x = (IObject φ k n x , x ~ IPoint' φ k a)

  (One g) . (One f) = One $ g ⋄ f
