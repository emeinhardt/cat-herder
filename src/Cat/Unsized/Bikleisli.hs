{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Bikleisli
  ( Bikleisli ( Bikleisli
              , unBikleisli
              )
  ) where

{- TODO document bikleisli (distributivity) laws.

See e.g. Orchard's 2014 thesis @ https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-854.pdf#page=191
-}

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
  ( Distributes ( dist
                )
  )

import Cat.Unsized.Monad
  ( Monad ( return
          , bind
          )
  )

import Cat.Unsized.Comonad
  ( Comonad ( extract
            , extend
            )
  )



newtype Bikleisli φ γ k a b = Bikleisli { unBikleisli ∷ φ a `k` γ b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance ( Comonad φ k, Monad γ k
         , Distributes φ γ k
         , ∀ x. Object (Bikleisli φ γ k) x ⇒ Object' k x
         )
  ⇒ Semigroupoid (Bikleisli φ γ k) where
  (Bikleisli g) . (Bikleisli f) = Bikleisli $ bind g ⊙ dist ⊙ extend f

instance ( Comonad φ k, Monad γ k
         , Distributes φ γ k
         , ∀ x. Object (Bikleisli φ γ k) x ⇒ Object' k x
         )
         ⇒ Category (Bikleisli φ γ k) where
  id = Bikleisli $ return ⊙ extract
