{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Semicartesian.Free
  ( HasProj   (ProjObjectOf)
  , HasDel    (DelObjectOf)
  , HasSelect (SelectObjectOf)
  , SemicartesianFunctor
  , DeleteFunctor
  , SelectFunctor
  ) where

import Prelude.Unicode ((∘))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4
  , Unconstrained5
  )

import GHC.TypeNats
  ( Nat
  )

import Cat.Sized.Functor
  ( Fix (In)
  )

import Cat.Sized.Semicartesian.Class
  ( ProjObject
  , ProjObject'
  , DelObject
  , DelObject'
  , SelectObject
  , SelectObject'
  , Semicartesian (idx)
  , Delete (del)
  , Select (sel)
  )

import Cat.Sized.Monoidal.Free.Data ()

class HasProj (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type ProjObjectOf φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type ProjObjectOf φ k n a = Unconstrained4 φ k n a

class HasDel (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type DelObjectOf φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type DelObjectOf φ k n a = Unconstrained4 φ k n a

class HasSelect (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type SelectObjectOf φ k (l ∷ Nat) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type SelectObjectOf φ k l n a = Unconstrained5 φ k l n a

class    (∀ i x. ProjObject φ p i x ⇒ ProjObject' φ q i x) ⇒ SemicartesianFunctor η φ p q
instance (∀ i x. ProjObject φ p i x ⇒ ProjObject' φ q i x) ⇒ SemicartesianFunctor η φ p q

class    (∀ i x. DelObject φ p i x ⇒ DelObject' φ q i x) ⇒ DeleteFunctor η φ p q
instance (∀ i x. DelObject φ p i x ⇒ DelObject' φ q i x) ⇒ DeleteFunctor η φ p q

class    (∀ i l x. SelectObject φ p i l x ⇒ SelectObject' φ q i l x) ⇒ SelectFunctor η φ p q
instance (∀ i l x. SelectObject φ p i l x ⇒ SelectObject' φ q i l x) ⇒ SelectFunctor η φ p q


instance (Semicartesian φ (η (Fix η))) ⇒ Semicartesian φ (Fix η) where
  type ProjObject φ (Fix η) n a = ProjObject φ (η (Fix η)) n a
  idx = In ∘ idx

instance (Delete φ (η (Fix η))) ⇒ Delete φ (Fix η) where
  type DelObject φ (Fix η) n a = DelObject φ (η (Fix η)) n a
  del = In ∘ del

instance (Select φ (η (Fix η))) ⇒ Select φ (Fix η) where
  type SelectObject φ (Fix η) i l a = SelectObject φ (η (Fix η)) i l a
  sel = In ∘ sel
