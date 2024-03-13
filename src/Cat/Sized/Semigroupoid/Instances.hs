{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Semigroupoid.Instances
  (
  ) where

import Prelude hiding
  ((.)
  , Functor
  , fmap
  )

import GHC.TypeNats
  ( KnownNat
  )
-- import GHC.Generics (Generic)

-- import Data.Functor qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Internal qualified as I
import Cat.Sized.Semigroupoid.Internal
  ( ISemigroupoid
  )
import Cat.Unsized.Semigroupoid.Class qualified as U
import Cat.Unsized.Semigroupoid.Instances ()

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ((.))
  , Object
  , Sized (Sized)
  , Unsized (Forget)
  )
import Cat.Orthotope
  ( Semiring
  , R1
  , Sr2
  , mulSr2
  , SrN
  , mulSrN
  )




-- Sized.Semigroupoid φ k ⇒ Unsized.Semigroupoid (k φ n n)

{- | This defines an /un/sized semigroupoid instance for /k φ n n ∷ κ → κ → Type/
when /φ/ and /k/ define a /sized/ semigroupoid. -}
instance (KnownNat n, Semigroupoid φ k) ⇒ U.Semigroupoid (k φ n n) where
  type Object (k φ n n) a = Object φ k n a
  (.) = (.)



-- 'Sized' newtype

{- | This defines a sized 'Semigroupoid' instance for 'Sized'-wrapped /k/ from the
/un/sized instance for /k/. -}
instance (U.Semigroupoid k) ⇒ Semigroupoid φ (Sized k) where
  type Object φ (Sized k) n a = U.Object k (φ n a)
  (Sized g) . (Sized f) = Sized $ g U.∘ f



-- 'Unsized' newtype

{- | This defines an /un/sized semigroupoid instance for 'Unsized'-wrapped
monoidal categories /k/ with product functor /φ/. -}
instance (Semigroupoid φ k) ⇒ U.Semigroupoid (Unsized φ k) where
  type Object (Unsized φ k) (φ n a) = Object φ k n a
  (Forget (g ∷ b -| k φ l m |-> c)) . (Forget (f ∷ a -| k φ n l |-> b)) = Forget (g . f)


instance (Semiring a) ⇒ ISemigroupoid R1 Sr2 a where
  (.) = mulSr2

instance (Semiring a) ⇒ ISemigroupoid R1 (SrN a) a where
  (.) = mulSrN
