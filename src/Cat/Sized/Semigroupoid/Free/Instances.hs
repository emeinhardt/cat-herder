{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Semigroupoid.Free.Instances
  (
  ) where

import Prelude hiding ((.))
-- import Prelude.Unicode ((∘))

import GHC.TypeNats (Nat)
import Data.Kind (Type)

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  )
import Cat.Sized.Semigroupoid.Free.Data
  ( SG ( Of
       )
  , HasObject ( ObjectOf
              )
  )




instance Semigroupoid (φ ∷ Nat → κ → κ) (SG (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Object φ (SG k) n a = ObjectOf φ k n a
  (.) = Of

-- instance (Semigroupoid @Type) (N ∷ Nat → Type → Type) (Sized (->)) where
--   -- type Object N (Sized (->)) n a = Object
--   (Sized g) . (Sized f) = Sized (g ∘ f)

{-
(Emb @N $ To' @Type @1 @1 @() @Bool) . (Emb @N $ To' @Type @2 @1 @Char @()) -- ambiguous type variable
-}

-- instance Semigroupoid (φ ∷ Nat → κ → κ) (SG φ (k ∷                 Nat → Nat → κ → κ → Type)) where
--   type Object φ (SG φ k) n a = ObjectOf φ k n a
--   (.) = Of


-- instance Semigroupoid (φ ∷ Nat → κ → κ) (SG φ (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  -- type Object (φ ∷ Nat → κ → κ) (SG φ k n m) (n ∷ Nat) (a ∷ κ) = ObjectOf φ k n a
  -- type Object (φ ∷ Nat → κ → κ) (k ∷ κ → κ → Type) (n ∷ Nat) (a ∷ κ) = ObjectOf φ k n a
  -- type Object (φ ∷ Nat → κ → κ) (k ∷ κ → κ → Type) (n ∷ Nat) (a ∷ κ) = ObjectOf φ k n a
  -- (.) = Of
  -- (.) ∷ ∀ (n ∷ Nat) (m ∷ Nat) (l ∷ Nat) (a ∷ κ) (b ∷ κ) (x ∷ κ).
  --       ( Object φ k n a, Object φ k m b, Object φ k l x )
  --     ⇒ k (φ l x) (φ m b)
  --     → k (φ n a) (φ l x)
  -- (g ∷ k (φ l x) (φ m b)) . (f ∷ k (φ n a) (φ l x)) =
  --    Of @φ @k @n @m @l @a @b @x g f
  -- (.) = Of @φ @k @n @m @l @a @b @x

  -- (.) ∷ ∀ (n ∷ Nat) (m ∷ Nat) (l ∷ Nat) (a ∷ κ) (b ∷ κ) (x ∷ κ).
  --     ( Object φ k n a, Object φ k m b, Object φ k l x )
  --     ⇒ φ l x `k` φ m b → φ n a `k` φ l x
  -- (.) = Of @k @φ @l @x @m @b @n @a

  -- (.) ∷ _
  -- (.) = Of
