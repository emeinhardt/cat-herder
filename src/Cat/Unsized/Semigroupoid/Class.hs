{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid
      ( Object
      , (.)
      )
  , Object'
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)

  , Sub (Sub, unSub)
  , sub
  , unsub
  ) where

import Prelude hiding
  ( (.)
  , Functor
  )

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained2)

import Cat.Operators ( type (-|), type (|->) )


class Semigroupoid (k ∷ κ → κ → Type) where
  type Object (k ∷ κ → κ → Type) (a ∷ κ) ∷ Constraint
  type Object k a = Unconstrained2 k a

  infixr 9 .
  (.) ∷ ∀ (a ∷ κ) (b ∷ κ) (x ∷ κ).
      ( Object k a, Object k b, Object k x
      )
       ⇒ x `k` b
       → a `k` x
       → a `k` b


{- | This is a "class synonym" for the type family 'Object'; it's often needed to
write quantified constraints. -}
class    (Object k a)
  ⇒ Object' (k ∷ κ → κ → Type) (a ∷ κ)
instance (Object k a)
  ⇒ Object' (k ∷ κ → κ → Type) (a ∷ κ)


infixr 1 <<<
(<<<) ∷ ∀ κ (k ∷ κ → κ → Type)
            (a ∷ κ) (b ∷ κ) (x ∷ κ).
      ( Object k a, Object k b, Object k x
      , Semigroupoid k
      )
      ⇒ x `k` b
      → a `k` x
      → a `k` b
(<<<) = (.)


infixr 1 >>>
(>>>) ∷ ∀ κ (k ∷ κ → κ → Type)
            (a ∷ κ) (b ∷ κ) (x ∷ κ).
      ( Object k a, Object k b, Object k x
      , Semigroupoid k
      )
      ⇒ a `k` x
      → x `k` b
      → a `k` b
(>>>) = flip (.)


infixr 9 ∘
(∘) ∷ ∀ κ (k ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) (x ∷ κ).
    ( Object k a, Object k b, Object k x
    , Semigroupoid k
    )
    ⇒ x `k` b
    → a `k` x
    → a `k` b
(∘) = (.)


infixr 9 ⊙
(⊙) ∷ ∀ κ (k ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) (x ∷ κ).
    ( Object k a, Object k b, Object k x
    , Semigroupoid k
    )
    ⇒ x `k` b
    → a `k` x
    → a `k` b
(⊙) = (.)



{- | A morphism of @κ@ restricted to objects that also satisfy some constraint
@o@. -}
newtype Sub (o ∷ κ → Constraint)
            (k ∷ κ → κ → Type)
            (a ∷ κ)
            (b ∷ κ)
  = Sub { unSub ∷ a `k` b }


sub ∷ ∀ o k a b .
    ( Semigroupoid k
    , o a, o b
    )
    ⇒ a `k` b
    → a -| (o `Sub` k) |-> b
sub = Sub


unsub ∷ ∀ o k a b .
      ( Semigroupoid k
      , o a, o b
      )
      ⇒ a -| (o `Sub` k) |-> b
      → a `k` b
unsub = unSub


instance Semigroupoid k ⇒ Semigroupoid (o `Sub` k) where
  type Object (o `Sub` k) a = (Object k a, o a)
  (Sub g) . (Sub f) = Sub (g . f)

