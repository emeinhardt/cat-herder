{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Monad
  ( Monad ( return
          , bind
          , join
          , (<=<)
          )
  , Kleisli ( Kleisli
            , unKleisli
            )
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , Monad
  , return
  )
import Prelude.Unicode ((∘))

import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, Nat)
import Data.Kind (Type)

import Data.Functor    qualified as F
import Control.Monad   qualified as M

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid (Object)
  , (.)
  , (⊙)
  , Object'
  , Sized (Sized)
  , unSized
  , Sub   (Sub)
  )
import Cat.Sized.Category.Class
  ( Category
  , id
  )

import Cat.Sized.Functor
  ( Functor ( fmap
            )
  )

-- import Cat.Unsized.Functor      qualified as U
-- import Cat.Unsized.Monad        qualified as U
-- import Cat.Unsized.Semigroupoid qualified as U


class Functor γ φ φ k k ⇒ Monad γ φ k where
  return ∷ (KnownNat n, Object φ k n a, Object φ k n (γ a))
         ⇒ a -| k φ n n |-> γ a

  {- | Default implementation:

  >>> bind f ≝ join ⊙ fmap f
  -}
  bind   ∷ ( KnownNat n, KnownNat m
           , Object φ k n    a
           , Object φ k n (γ a)
           , Object φ k m (γ b)
           )
         ⇒   a -| k φ n m |-> γ b
         → γ a -| k φ n m |-> γ b

  {- | Default implementation:

  >>> join ≝ bind id
  -}
  join   ∷ ( KnownNat n
           , Object φ k n    (γ a)
           , Object φ k n (γ (γ a))
           )
         ⇒ γ (γ a) -| k φ n n |-> γ a

  default bind ∷ ( KnownNat n, KnownNat m
                 , Object φ k n       a
                 , Object φ k n    (γ a)
                 , Object φ k m    (γ b)
                 , Object φ k m (γ (γ b))
                 )
         ⇒   a -| k φ n m |-> γ b
         → γ a -| k φ n m |-> γ b
  bind f = join ⊙ fmap f

  default join ∷ ( KnownNat n
                 , Object φ k n    (γ a)
                 , Object φ k n (γ (γ a))
                 )
         ⇒ γ (γ a) -| k φ n n |-> γ a
  join = bind id

  {- | Default implementation:

  >>> g <=< f ≝ bind g ⊙ f
  -}
  (<=<) ∷ ( KnownNat n, KnownNat m, KnownNat o
          , Object φ k n    a , Object φ k m    b , Object φ k o    c
          , Object φ k n (γ a), Object φ k m (γ b), Object φ k o (γ c)
          )
          ⇒ b -| k φ m o |-> γ c
          → a -| k φ n m |-> γ b
          → a -| k φ n o |-> γ c
  g <=< f = bind g ⊙ f

  {-# MINIMAL return, (join | bind) #-}


newtype Kleisli (γ ∷ κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) =
  Kleisli { unKleisli ∷ a -| k φ n m |-> γ b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance (Monad γ φ k) ⇒ Semigroupoid φ (Kleisli γ k) where
  type Object φ (Kleisli γ k) n a = (Object φ k n a, Object φ k n (γ a))
  (Kleisli g) . (Kleisli f) = Kleisli (g <=< f)

instance (Monad γ φ k) ⇒ Category φ (Kleisli γ k) where
  id = Kleisli $ return ⊙ id


{- | This provides a /sized/ monad instance for any @base@ monad @γ@ and
sized category defined by /φ/ and @Sized (->)@. -}
instance ( ∀ i. KnownNat i ⇒ F.Functor (φ i)
         , M.Monad γ
         -- , U.Monad γ (->)
         , Functor γ φ φ (Sized (->)) (Sized (->))
         -- , ∀ i x. Object φ (Sized (->)) i x ⇒ U.Object' (->) (φ i x)
         , ∀ i x. Object φ (Sized (->)) i (γ x) ⇒ Object' φ (Sized (->)) i (γ (γ x))
         )
  ⇒ Monad γ φ (Sized (->)) where
  return ∷ ∀ n a.
         ( KnownNat n
         -- , Object φ (Sized (->)) n a
         -- , Object φ (Sized (->)) n (γ a)
         )
         ⇒ a -| Sized (->) φ n n |-> γ a
  return = Sized $ (F.fmap @(φ n)) (M.return @γ)

  bind f = join ⊙ fmap f
  -- bind = Sized ∘ M.join ∘ F.fmap ∘ unSized

  join = Sized $ F.fmap M.join


instance ( Monad γ φ k
         , ∀ i x. Object φ (o `Sub` k) i (γ x) ⇒ Object' φ (o `Sub` k) i (γ (γ x))
         , Functor γ φ φ (o `Sub` k) (o `Sub` k)
         )
  ⇒ Monad γ φ (o `Sub` k) where
  return ∷ ∀ n a.
         ( KnownNat n
         , Object φ (o `Sub` k) n a
         , Object φ (o `Sub` k) n (γ a)
         )
         ⇒ a -| (o `Sub` k) φ n n |-> γ a
  return = Sub return

  join = Sub join
