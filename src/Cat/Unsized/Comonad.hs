{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Comonad
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

import Data.Functor    qualified as F
import Control.Comonad qualified as W

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid (Object)
  , (.)
  , (⊙)
  , Object'
  )
import Cat.Unsized.Category.Class
  ( Category
  , id
  )

import Cat.Unsized.Functor
  ( Functor ( fmap
            )
  )



class Functor φ k k ⇒ Comonad φ k where
  extract   ∷ (Object k a, Object k (φ a))
            ⇒ φ a `k` a

  {- | Default implementation:

  >>> extend ≝ fmap f ⊙ duplicate
  -}
  extend    ∷ (Object k b, Object k (φ a), Object k (φ b))
            ⇒ φ a `k`   b
            → φ a `k` φ b

  {- | Default implementation:

  >>> duplicate ≝ extend id
  -}
  duplicate ∷ (Object k (φ a), Object k (φ (φ a)))
            ⇒ φ a `k` φ (φ a)

  default extend ∷ (Object k b, Object k (φ a), Object k (φ b)
                   , Object k (φ (φ a)))
            ⇒ φ a `k`   b
            → φ a `k` φ b
  extend f = fmap f ⊙ duplicate

  default duplicate ∷ (Object k (φ a), Object k (φ (φ a)))
            ⇒ φ a `k` φ (φ a)
  duplicate = extend id

  {- | Default implementation:

  >>> g =<= f ≝ g ⊙ extend f
  -}
  (=<=) ∷ ( Object k (φ a), Object k (φ b), Object k (φ c)
          , Object k    a , Object k    b , Object k    c
          )
      ⇒ φ b `k` c
      → φ a `k` b
      → φ a `k` c
  g =<= f = g ⊙ extend f

  {-# MINIMAL extract, (duplicate | extend) #-}

instance (Category (->), W.Comonad φ) ⇒ Comonad φ (->) where
  extract   = W.extract
  extend    = W.extend
  duplicate = W.duplicate
  (=<=)  = (W.=<=)

newtype Cokleisli φ k a b = Cokleisli { unCokleisli ∷ φ a `k` b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance (Comonad φ k) ⇒ Semigroupoid (Cokleisli φ k) where
  type Object (Cokleisli φ k) a = (Object k a, Object k (φ a))
  (.) = (⊙)

instance (Comonad φ k) ⇒ Category (Cokleisli φ k) where
  id = Cokleisli $ id ⊙ extract
