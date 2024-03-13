{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Semiadditive.Class
  ( Semiadditive
  , HasTerminal (terminal)
  , HasZero     (pointer)
  ) where

{-

 - TODO Is there a reason why it would be *useful* to require Semiadditive to be an instance of Bimonoidal?

 - TODO Define/export more functionality related to zero objects?

 - TODO Cat.Sized.Additive = Same as Semiadditive but with the extra constraint that
   the category k is symmetric monoidal wrt φ
-}

import Data.Kind    (Type)
import GHC.TypeNats (Nat)

import Cat.Sized.Semicartesian.Class
  ( Semicartesian
  , HasTerminal (terminal)
  )
import Cat.Sized.Semicocartesian.Class
  ( Semicocartesian
  )
import Cat.Sized.Zero.Class
  ( HasZero (pointer)
  )


{- | An operation in a category that can serve both as a product and a coproduct
in a compatible way is a /biproduct/.

The expected law governing the interaction of 'Semicartesian' and
'Semicocartesian' is that embedding into an index /i/ and then projecting from
that index /i/ should be the same as doing nothing:

>>> idx i ⊙ inj i ≝ id
-}
class ( Semicartesian   φ (k φ)
      , Semicocartesian φ (k φ)
      )
  ⇒ Semiadditive
    (φ ∷  Nat → κ → κ)
    (k ∷ (Nat → κ → κ) → (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
