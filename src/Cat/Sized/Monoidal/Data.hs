{-# OPTIONS_HADDOCK show-extensions #-}
{- | This is an ephemeral module for package development whose current contents
will be split up elsewhere.

The module serves as a convenient namespace for concrete monoidal product
functors suitable for defining a @Monoidal@ (category) instance that don't have
any particularly good reason to be somewhere else.

-}

module Cat.Sized.Monoidal.Data
  ( N (N, unN)
  , n0
  , n1
  , To (To)
  , P (P)

  -- --   -- * Comonadic morphisms
  ) where

{- TODO Add relevant instances for (roughly in order of expected utility):
 - N
-}


-- import Prelude qualified as P
import Prelude hiding
  ( Functor
  , fmap
  , zip
  , zipWith
  )

import GHC.Generics (Generic)
import Data.Kind (Type)
import GHC.TypeNats
  ( Nat
  , SNat
  )
import Data.Finite
  ( Finite
  )

import Data.Functor     qualified as F
-- import Control.Comonad  qualified as W
-- import Data.Functor.Rep qualified as R

import Cat.Sized.Semigroupoid.Free.Data
  ( To (To)
  , P (P)
  )




{- | A functor containing a single @a@ and tagged with a @Nat@.

This can be used to permit @a@ in places that demand a @Nat@-tagged product
functor - e.g. to lift an unsized functor (@a ~ f b~ for some @f@ and @b@). -}
newtype N (n ∷ Nat) (a ∷ Type) = N { unN ∷ a }
  deriving newtype (Eq, Ord, Read, Show)
  deriving stock (Generic, F.Functor, Foldable, Traversable)

n0 ∷ a → N 0 a
n0 = N

n1 ∷ a → N 1 a
n1 = N







-- Finitary traversable representable functor workhorses

-- TODO Finish associated methods/instances when you get to a use case Also
-- consider using the (already written, debugged, etc.) representable-trie
-- package?
{- | Representable encoding of a finitary cofree traversable functor.

 - /φ/ is the finitary representable functor used to store values.
 - /n/ is the size of the bounded pool of values available for filling in the
   shape of the traversable functor /γ/.
 - /γ/ is a traversable functor — really a shape/skeleton — which contains references
   (@Finite n@) to the pool of values.
-}
data Cotra (φ ∷ Nat → Type → Type)
           (n ∷ Nat)               -- Is exposing this desirable?
           (γ ∷ Type → Type)
           (a ∷ Type)
     = Cotra { size ∷ SNat n
             , tra  ∷ γ (Finite n)
             , pool ∷ φ n a
             }
  deriving stock (Generic, F.Functor)

deriving instance (Foldable    (φ n), Foldable    γ) ⇒ Foldable    (Cotra φ n γ)
deriving instance (Traversable (φ n), Traversable γ) ⇒ Traversable (Cotra φ n γ)
