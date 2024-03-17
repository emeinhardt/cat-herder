{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Category.Class
  ( Category ( id )
    -- * Re-exports from "Cat.Sized.Semigroupoid"
  , Semigroupoid ( Object
                 , (.)
                 )
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)
  , Object'

  , Sub ( Sub, unSub )
  , sub
  , unsub
  , SizedCon

  , Sized ( Sized, unSized )
  -- , sized
  -- , unsized
  , Unsized (Forget)
  , remember
  ) where

import Prelude hiding
  ( id
  , (.)
  )

import GHC.TypeNats (Nat, KnownNat)
import Data.Kind (Type
                 )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)
  , Object'
  , Sub ( Sub, unSub )
  , sub
  , unsub
  , Sized ( Sized, unSized )
  -- , sized
  -- , unsized
  , Unsized (Forget)
  , remember
  , SizedCon
  )


class (Semigroupoid φ k)
  ⇒ Category (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  -- TODO @limbo: do KnownNat n,m,l as constraints add anything here?
  id ∷ ∀ (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , Object φ k n a
     )
     ⇒ a -| k φ n n |-> a


instance Category φ k ⇒ Category φ (o `Sub` k) where
  id = Sub id
