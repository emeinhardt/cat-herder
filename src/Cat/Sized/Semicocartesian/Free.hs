{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Semicocartesian.Free
  ( HasInj (InjObjectOf)
  ) where

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4 )

import GHC.TypeNats
  ( Nat
  )

class HasInj (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type InjObjectOf φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type InjObjectOf φ k n a = Unconstrained4 φ k n a
