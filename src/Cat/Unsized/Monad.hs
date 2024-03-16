{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Monad
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

import GHC.Generics (Generic)

import Data.Functor    qualified as F
import Control.Monad   qualified as M

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid (Object)
  , (.)
  , (⊙)
  )
import Cat.Unsized.Category.Class
  ( Category
  , id
  )

import Cat.Unsized.Functor
  ( Functor ( fmap
            )
  )



class Functor φ k k ⇒ Monad φ k where
  return ∷ (Object k a, Object k (φ a))
         ⇒ a `k` φ a

  {- | Default implementation:

  >>> bind f ≝ join ⊙ fmap f
  -}
  bind   ∷ (Object k a, Object k (φ a), Object k (φ b))
         ⇒   a `k` φ b
         → φ a `k` φ b

  {- | Default implementation:

  >>> join ≝ bind id
  -}
  join   ∷ (Object k (φ a), Object k (φ (φ a)))
         ⇒ φ (φ a) `k` φ a

  default bind ∷ ( Object k a, Object k (φ a), Object k (φ b)
                 , Object k (φ (φ b))
                 )
         ⇒   a `k` φ b
         → φ a `k` φ b
  bind f = join ⊙ fmap f

  default join ∷ (Object k (φ a), Object k (φ (φ a)))
         ⇒ φ (φ a) `k` φ a
  join = bind id

  {- | Default implementation:

  >>> g <=< f ≝ bind g ⊙ f
  -}
  (<=<) ∷ ( Object k (φ a), Object k (φ b), Object k (φ c)
          , Object k    a , Object k    b , Object k    c
          )
          ⇒ b `k` φ c
          → a `k` φ b
          → a `k` φ c
  g <=< f = bind g ⊙ f

  {-# MINIMAL return, (join | bind) #-}


instance (Category (->), M.Monad φ) ⇒ Monad φ (->) where
  return = M.return
  bind   = (=<<)
  join   = M.join
  (<=<)  = (M.<=<)


newtype Kleisli φ k a b = Kleisli { unKleisli ∷ a `k` φ b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance (Monad φ k) ⇒ Semigroupoid (Kleisli φ k) where
  type Object (Kleisli φ k) a = (Object k a, Object k (φ a))
  (Kleisli g) . (Kleisli f) = Kleisli (g <=< f)

instance (Monad φ k) ⇒ Category (Kleisli φ k) where
  id = Kleisli $ return ⊙ id
