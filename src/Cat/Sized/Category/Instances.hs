{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Category.Instances
  (
  ) where

-- import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )

-- import Data.Kind (Type)
import GHC.TypeNats
  ( KnownNat
  -- , Nat
  )

import Cat.Unsized.Semigroupoid.Class qualified as U
import Cat.Unsized.Category.Class     qualified as U
import Cat.Unsized.Category.Instances ()


import Cat.Sized.Semigroupoid.Internal
  ( -- ISemigroupoid
    One (One)
  )
import Cat.Sized.Semigroupoid.Class   qualified as S
import Cat.Sized.Category.Class
  ( Category (id)
  , Sized (Sized)
  -- , Unsized (Forget)
  )

import Cat.Sized.Semigroupoid.Instances ()

import Cat.Orthotope
  ( Semiring
  , R1
  , Sr2
  , idSr2
  , SrN
  , idSrN
  )


-- Sized.Category φ k ⇒ Unsized.Category (k φ n n)

{- | This defines an /un/sized category instance for /k φ n n ∷ κ → κ → Type/
when /φ/ and /k/ define a /sized/ category. -}
instance (KnownNat n, Category φ k, U.Semigroupoid (k φ n n))
  ⇒ U.Category (k φ n n) where
  id = id



-- 'Sized' newtype

{- | This defines a sized 'Category' instance from the /un/sized category instance
and a sized semigroupoid instance. -}
instance (U.Category k, S.Semigroupoid φ (Sized k))
  ⇒ Category φ (Sized k) where
  id = Sized U.id



-- 'Unsized' newtype

-- TODO continuations?
-- instance (Category @Type φ k, U.Semigroupoid (Unsized φ k)) ⇒ U.Category (Unsized φ k) where
--   id ∷ ∀ a.
--      ( Category φ k
--      , U.Semigroupoid (Unsized φ k)
--      , U.Object (Unsized φ k) a
--      )
--      ⇒ Unsized φ k a a
--   id = Forget id


instance (Semiring a, S.Semigroupoid R1 (One a Sr2)) ⇒ Category R1 (One a Sr2) where
  id = One idSr2

instance (Semiring a, S.Semigroupoid R1 (One a (SrN a))) ⇒ Category R1 (One a (SrN a)) where
  id = One idSrN
