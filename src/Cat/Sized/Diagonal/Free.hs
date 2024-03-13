{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Diagonal.Free
  ( HasDup (DupObjectOf)
  , DiagonalFunctor
  ) where

import Prelude
import Data.Composition ((.:))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained6 )

import GHC.TypeNats
  ( Nat
  )

import Cat.Sized.Functor
  ( Fix (In)
  )

import Cat.Sized.Monoidal.Class
  ( Proxy
  )
import Cat.Sized.Diagonal.Class
  ( DupObject
  , DupObject'
  , Diagonal ( dup
             , dup'
             , (&&&)
             , fork
             )
  )

import Cat.Sized.Monoidal.Free.Data ()


class HasDup (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type DupObjectOf φ k (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) ∷ Constraint
  type DupObjectOf φ k n m a b = Unconstrained6 φ k n m a b

class    (∀ i j x y. DupObject φ p i j x y ⇒ DupObject' φ q i j x y) ⇒ DiagonalFunctor η φ p q
instance (∀ i j x y. DupObject φ p i j x y ⇒ DupObject' φ q i j x y) ⇒ DiagonalFunctor η φ p q


instance (Diagonal φ (η (Fix η)), Proxy φ (η (Fix η)) ~ Proxy φ (Fix η))
  ⇒ Diagonal φ (Fix η) where
  type DupObject φ (Fix η) i j x y = DupObject φ (η (Fix η)) i j x y
  dup = In dup
  dup' = In .: dup'
  (In f) &&& (In g) = In $ f &&& g
  fork l n m (In f) (In g) = In $ fork l n m f g
