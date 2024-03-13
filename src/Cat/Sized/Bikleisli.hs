{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Bikleisli
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

import Data.Kind    (Type)
import GHC.Generics (Generic)
import GHC.TypeNats
  ( Nat
  )

import Data.Functor    qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid (Object)
  , (.)
  , (⊙)
  )
import Cat.Sized.Category.Class
  ( Category
  , id
  )

import Cat.Sized.Functor
  ( Distributes ( dist
                )
  )

import Cat.Sized.Monad
  ( Monad ( return
          , bind
          )
  )

import Cat.Sized.Comonad
  ( Comonad ( extract
            , extend
            )
  )



newtype Bikleisli (γ ∷ κ → κ) (η ∷ κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) =
  Bikleisli { unBikleisli ∷ γ a -| k φ n m |-> η b }
  deriving stock (Eq, Ord, Show, Read, Bounded, Generic, F.Functor, Foldable)

instance ( Comonad γ φ k, Monad η φ k
         , Distributes γ η φ k
         )
  ⇒ Semigroupoid φ (Bikleisli γ η k) where
  type Object φ (Bikleisli γ η k) n a = ( Object φ k n a
                                        , Object φ k n    (γ a)  , Object φ k n    (η a)
                                        , Object φ k n (η (γ a)) , Object φ k n (γ (η a))
                                        )
  (Bikleisli g) . (Bikleisli f) = Bikleisli $ bind g ⊙ dist ⊙ extend f

instance ( Comonad γ φ k, Monad η φ k
         , Distributes γ η φ k
         )
         ⇒ Category φ (Bikleisli γ η k) where
  id = Bikleisli $ return ⊙ extract
