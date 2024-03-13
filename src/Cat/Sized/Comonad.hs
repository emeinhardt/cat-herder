{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Comonad
  ( Comonad ( extract
            , extend
            , duplicate
            , (=<=)
            )
  , Cokleisli ( Cokleisli
              , unCokleisli
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

import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, Nat)
import Data.Kind (Type)

import Data.Functor    qualified as F
import Control.Comonad qualified as W

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



class Functor γ φ φ k k ⇒ Comonad γ φ k where
  extract ∷ ( KnownNat n
            , Object φ k n a
            , Object φ k n (γ a)
            )
          ⇒ γ a -| k φ n n |-> a

  {- | Default implementation:

  >>> extend ≝ fmap f ⊙ duplicate
  -}
  extend ∷ ( KnownNat n
           , KnownNat m
           , Object φ k m b
           , Object φ k n (γ a)
           , Object φ k m (γ b)
           )
         ⇒ γ a -| k φ n m |-> b
         → γ a -| k φ n m |-> γ b

  {- | Default implementation:

  >>> duplicate ≝ extend id
  -}
  duplicate ∷ ( KnownNat n
              , Object φ k n (γ a)
              , Object φ k n (γ (γ a))
              )
            ⇒ γ a -| k φ n n |-> γ (γ a)

  default extend ∷ ( KnownNat n, KnownNat m
                   , Object φ k m       b
                   , Object φ k n    (γ a)
                   , Object φ k m    (γ b)
                   , Object φ k n (γ (γ a))
                   )
         ⇒ γ a -| k φ n m |-> b
         → γ a -| k φ n m |-> γ b
  extend f = fmap f ⊙ duplicate

  default duplicate ∷ ( KnownNat n
              , Object φ k n (γ a)
              , Object φ k n (γ (γ a))
              )
            ⇒ γ a -| k φ n n |-> γ (γ a)
  duplicate = extend id

  {- | Default implementation:

  >>> g =<= f ≝ g ⊙ extend f
  -}
  (=<=) ∷ ( KnownNat n, KnownNat m, KnownNat o
          , Object φ k n (γ a), Object φ k m (γ b), Object φ k o (γ c)
          , Object φ k n    a , Object φ k m    b , Object φ k o    c
          )
          ⇒ γ b -| k φ m o |-> c
          → γ a -| k φ n m |-> b
          → γ a -| k φ n o |-> c
  g =<= f = g ⊙ extend f

  {-# MINIMAL extract, (duplicate | extend) #-}


newtype Cokleisli (γ ∷ κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) =
  Cokleisli { unCokleisli ∷ γ a -| k φ n m |-> b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance (Comonad γ φ k) ⇒ Semigroupoid φ (Cokleisli γ k) where
  type Object φ (Cokleisli γ k) n a = (Object φ k n a, Object φ k n (γ a))
  (.) = (⊙)

instance (Comonad γ φ k) ⇒ Category φ (Cokleisli γ k) where
  id = Cokleisli $ id ⊙ extract



instance ( ∀ i. KnownNat i ⇒ F.Functor (φ i)
         , W.Comonad γ
         -- , U.Comonad γ (->)
         , Functor γ φ φ (Sized (->)) (Sized (->))
         -- , ∀ i x. Object φ (Sized (->)) i x ⇒ U.Object' (->) (φ i x)
         , ∀ i x. Object φ (Sized (->)) i (γ x) ⇒ Object' φ (Sized (->)) i (γ (γ x))
         )
  ⇒ Comonad γ φ (Sized (->)) where
  extract ∷ ∀ n a.
          ( KnownNat n
          -- , Object φ (Sized (->)) n a
          -- , Object φ (Sized (->)) n (γ a)
          )
          ⇒ γ a -| Sized (->) φ n n |-> a
  extract = Sized $ (F.fmap @(φ n)) W.extract

  duplicate = Sized $ F.fmap W.duplicate


instance ( Comonad γ φ k
         , ∀ i x. Object φ (o `Sub` k) i (γ x) ⇒ Object' φ (o `Sub` k) i (γ (γ x))
         , Functor γ φ φ (o `Sub` k) (o `Sub` k)
         )
  ⇒ Comonad γ φ (o `Sub` k) where
  extract ∷ ∀ n a.
         ( KnownNat n
         , Object φ (o `Sub` k) n a
         , Object φ (o `Sub` k) n (γ a)
         )
         ⇒ γ a -| (o `Sub` k) φ n n |-> a
  extract = Sub extract

  duplicate = Sub duplicate
