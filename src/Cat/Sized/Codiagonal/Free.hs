{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Codiagonal.Free
  ( HasJam (JamObjectOf)
  ) where

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4 )

import GHC.TypeNats
  ( Nat
  )

class HasJam (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type JamObjectOf φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type JamObjectOf φ k n a = Unconstrained4 φ k n a

