{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Sized.Semicocartesian.Class
  ( Semicocartesian ( InjObject
                    , inj
                    , inj'
                    )
  , InjObject'
  , injMon
  , InjMon (InjMon, unInjMon)

  , Pad ( PadObject
        , pad
        -- , pad'
        )
  , PadObject'
  , padMon
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4
  , Unconstrained5
  )
import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , pattern SNat
  , natVal
  , type (-)
  , type (+)
  )
import Data.Finite
  ( Finite
  , getFinite
  )

import Data.Functor.Rep qualified as R
import Data.Functor.Rep
  ( Representable
  , Rep
  , tabulate
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Object'
  , Sub (Sub)
  , Sized (Sized)
  )
import Cat.Sized.Category.Class
  ( Category (id)
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , Unit
             , (***)
             , mul
             , ith
             , ith'
             , sing
             , unsing
             , join
             , split
             , assoc
             , lift1
             , bisplit
             , bijoin
             , biassoc
             )
  )



{- | A semicocartesian category has injections into its coproducts.

For example, if /a/ has a monoid instance, then a likely definition of
@inj ∷ Finite n → a -| φ k 1 n |-> a@ creates a morphism that lifts an /a/ into an
/n/-length /φ/-structure at the index described by the 'Finite' value, with
'mempty' at all other locations.

Minimal definition if @Proxy k ~ SNat@: @inj | inj'@.
Minimal definition otherwise: @inj@. -}
class (Monoidal φ k)
  ⇒ Semicocartesian (φ ∷ Nat → κ → κ)
                    (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  where

  {- | Extra constraints on injecting an object into a /φ/ structure at a particular
  position, e.g.
  @InjObject φ k n a = (Representable (φ n), Representable (φ 1), Monoid a)@
  or something related. -}
  type InjObject φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type InjObject φ k n a = Unconstrained4 φ k n a

  {- | 'inj' should map an input object to a length-/n/ coproduct with the
  original object at a particular position.

  The default instance is defined in terms of 'inj''. -}
  inj ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      -- , 1 <= n
      , Object φ k 1 a
      , Object φ k n a
      , InjObject φ k n a
      )
      ⇒ Finite n            -- ^ The index to inject a value into.
      → a -| k φ 1 n |-> a

  default inj ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , Object φ k 1 a
      , Object φ k n a
      , InjObject φ k n a
      , SNat ~ Proxy φ k
      )
      ⇒ Finite n            -- ^ The index to inject a value into.
      → a -| k φ 1 n |-> a
  inj (fn ∷ Finite n) = inj' @κ @φ @k @n @a (SNat @n) fn

  {- |
  The default definition is in terms of 'inj'. -}
  inj' ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object φ k 1 a
       , Object φ k n a
       , InjObject φ k n a
       )
       ⇒ (Proxy φ k) n       -- ^ A proxy for the overall length of the coproduct.
       → Finite n            -- ^ The index to inject a value into.
       → a -| k φ 1 n |-> a

  inj' (_ ∷ (Proxy φ k) n) (fn ∷ Finite n)
    = inj @κ @φ @k @n @a fn



{- | This is a "class synonym" for the type family 'InjObject'; it's often needed
to write quantified constraints. -}
class    (InjObject φ k n a)
  ⇒ InjObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (InjObject φ k n a)
  ⇒ InjObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


instance (Semicocartesian φ k, Proxy φ k ~ Proxy φ (o `Sub` k)) ⇒ Semicocartesian φ (o `Sub` k) where
  type InjObject φ (o `Sub` k) n a = InjObject φ k n a
  inj = Sub ∘ inj
  inj' pn fn = Sub $ inj' pn fn



{- | This is a generic implementation for 'inj' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /φ/ with suitable
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instances.

This may be easier to use (require less cajoling of GHC) for defining instances
than 'InjMon'. -}
injMon ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
      ( Representable (φ n)
      , Representable (φ 1)
      , Integral (Rep (φ 1))
      , Eq (Rep (φ n))
      , Monoid a
      )
      ⇒ Rep (φ n)            -- ^ The index to inject a value into.
{-      -- ⇒ Finite n          -- -- ^ The index to inject a value into.-}
      → φ 1 a
      → φ n a
injMon x =
  let tab ∷ a → Rep (φ n) → a
      tab a y
        | y == x    = a
        | otherwise = mempty
  in tabulate ∘ tab ∘ flip R.index 0



{- | Newtype provididing a 'Semicocartesian' instance for @Sized (->)@ constrained
to objects with a 'Monoid' instance and to product functors /φ/ where

- /φ n/ is 'Representable'.
- @Rep (φ n) ~ Finite n@.

When these conditions hold, @inj fn@ is a function that takes an element @a@ and
injects it into an /n/-length product at index @fn@, with @mempty@ at every
other index. -}
newtype InjMon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (φ ∷  Nat → κ → κ)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ)
  = InjMon { unInjMon ∷ a -| k φ n m |-> b }


instance Semigroupoid φ k
  ⇒ Semigroupoid (φ ∷ Nat → Type → Type) (InjMon (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type))
  where
  type Object φ (InjMon k) n a = (Object φ k n a, Monoid a)
  (InjMon g) . (InjMon f) = InjMon (g . f)


instance ( Semigroupoid φ (InjMon k)
         , Category φ k
         , ∀ x. (Object' φ (InjMon k) n x, Monoid x) ⇒ Object' φ k n x
         ) ⇒ Category φ (InjMon k) where
  id = InjMon id


instance ( Category φ (InjMon k)
         , ∀ x. (Object' φ (InjMon k) n x, Monoid x) ⇒ Object' φ k n x
         , Monoidal φ k
         )
  ⇒ Monoidal φ (InjMon k) where
  type Proxy φ (InjMon k) = Proxy φ k

  (InjMon f) *** (InjMon g) = InjMon $ f *** g

  mul pn pm pn' pm' (InjMon f) (InjMon g) = InjMon $ mul pn pm pn' pm' f g

  ith     fn (InjMon f) = InjMon $ ith     fn f
  ith' pn fn (InjMon f) = InjMon $ ith' pn fn f

  sing     = InjMon   sing
  unsing   = InjMon   unsing
  join     = InjMon   join
  split    = InjMon   split
  assoc    = InjMon   assoc
  lift1    = InjMon ∘ lift1   ∘ unInjMon
  bisplit  = InjMon ∘ bisplit ∘ unInjMon
  bijoin   = InjMon ∘ bijoin  ∘ unInjMon
  biassoc  = InjMon ∘ biassoc ∘ unInjMon


instance ( Monoidal φ (InjMon k)
         , k ~ Sized (->)
         )
  ⇒ Semicocartesian
    (φ ∷ Nat → Type → Type)
    (InjMon (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type))
  where
  type InjObject φ (InjMon k) n a = ( Representable (φ 1)
                                    , Representable (φ n)
                                    , R.Rep (φ n) ~ Finite n
                                    , R.Rep (φ 1) ~ Finite 1
                                    , Monoid a
                                    )
  inj (fn ∷ Finite n) =
    let
       tab ∷ Monoid a ⇒ a → Finite n → a
       tab a fi
         | fi == fn  = a
         | otherwise = mempty
    in InjMon
     ∘ Sized
     $ R.tabulate
     ∘ tab
     ∘ flip R.index (0 ∷ Finite 1)


{- | This is a generalized variant of 'Semicocartesian' and a dual to @Select@
that permits injecting a coproduct into a larger coproduct. -}
class (Monoidal φ k)
  ⇒ Pad (φ ∷ Nat → κ → κ)
        (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  where

  {- | Extra constraints on injecting a product of /l/ objects into a /φ/ structure
  of length /n/ at a particular position, e.g. @PadObject φ k n a =
  (Representable (φ n), Representable (φ 1), Monoid a)@ or something related. -}
  type PadObject φ k (n ∷ Nat) (l ∷ Nat) (a ∷ κ) ∷ Constraint
  type PadObject φ k n l a = Unconstrained5 φ k n l a

  {- | 'pad' should map an input length-/l/ coproduct to a length-/n/ coproduct with
  the left edge of the original coproduct at a particular position.

  The default instance is defined in terms of 'inj''. -}
  pad ∷ ∀ (n ∷ Nat) (l ∷ Nat) (a ∷ κ).
      ( KnownNat n, KnownNat l
      , Object φ k l a
      , Object φ k n a
      , PadObject φ k n l a
      )
      ⇒ Finite ((n - l) + 1)  -- ^ The index of the /n/-coproduct where the original /l/-coproduct should start.
      → a -| k φ l n |-> a



{- | This is a "class synonym" for the type family 'PadObject'; it's often needed
to write quantified constraints. -}
class    (PadObject φ k n l a)
  ⇒ PadObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (l ∷ Nat) (a ∷ κ)
instance (PadObject φ k n l a)
  ⇒ PadObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (l ∷ Nat) (a ∷ κ)



{- | This is a generic implementation for 'pad' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /φ/ with suitable
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instances.

This may be easier to use (require less cajoling of GHC) for defining instances
than a (currently nonexistent) newtype analogous to 'injMon'. -}
padMon ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (l ∷ Nat) (a ∷ Type).
      ( KnownNat n, KnownNat l
      , Representable (φ n)
      , Representable (φ l)
      , Integral (Rep (φ n))
      , Integral (Rep (φ l))
      , Monoid a
      )
      ⇒ Finite ((n - l) + 1)            -- ^ The index to inject a slice into.
      → φ l a
      → φ n a
padMon x =
  let l' = fromIntegral $ natVal (SNat @l)
      x' = fromIntegral $ getFinite x
      tab ∷ φ l a → Rep (φ n) → a
      tab fa y
        | y >= x' || y < (x' + l') = fa `R.index` fromIntegral y
        | otherwise = mempty
  in tabulate ∘ tab
