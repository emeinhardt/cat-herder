{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Zero.Class
  ( HasZero ( pointer
            )
  ) where


import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type)
import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , pattern SNat
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 )
  , Sub (Sub)
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Unit
             )
  )

{- | This typeclass reflects the expected form of a zero morphism for categories
where the initial and terminal objects coincide (i.e. have a "zero" object) and
related constructions. -}
class (Monoidal φ k)
  ⇒ HasZero (φ ∷ Nat → Type → Type) (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type)
  where

  pointer ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type).
           ( KnownNat n
           , Object φ k n a
           , Object φ k m b
           , Unit φ k m a ~ φ m a
           , Unit φ k m b ~ φ m a
           )
           ⇒ φ m b
           → a -| k φ n m |-> b


instance (HasZero φ k, Unit φ k m x ~ Unit φ (o `Sub` k) m x) ⇒ HasZero φ (o `Sub` k) where
  pointer = Sub ∘ pointer
