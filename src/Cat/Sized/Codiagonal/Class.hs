{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Sized.Codiagonal.Class
  ( Codiagonal ( JamObject
               , jam
               , jam'
               )
  , JamObject'
  , (▽)
  , jamMon
  , jamMon'
  , JamMon (JamMon, unJamMon)
  ) where

import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )
import Prelude.Unicode ((∘))

import GHC.TypeNats (KnownNat, Nat)
import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained4)

import Data.Foldable (foldMap', fold)

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



{- | 'Diagonal' captures the ability to create copies, i.e. the introduction form
of a Cartesian monoidal product — @dup@; the dual of the introduction form for a
Cocartesian category is an /elimination form for the coproduct/, and this
operation defines the dual to monoidal categories with a diagonal operation. -}
class (Monoidal φ k)
  ⇒ Codiagonal (φ ∷ Nat → κ → κ)
               (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  where

  {- | Extra constraints on whether an object (or product of them) can be 'jam'd,
  e.g. @JamObject φ k n a = (Foldable (φ n), Applicative (φ 1), Monoid a)@ or
  something related. -}
  type JamObject φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type JamObject φ k n a = Unconstrained4 φ k n a

  {- | For binary coproducts, a universal property relates the two introduction
  forms to the elimination form:

  >> inL ∷ a `k` (a + b)
  >> inR ∷ b `k` (a + b)
  >> jam ∷ (c `k` a) → (b `k` a) → (c + b) `k` a
  >> ∀ h. h ≡ f `jam` g ⇔ h ∘ inL ≡ f ∧ h ∘ inR ≡ g

  Intuitively, if we have an object that is a discriminated sum @a + b@ created
  ultimately by some sum introduction form, then there must always be a way we
  can use @jam@ to eliminate the discriminated sum and recover the original
  object that was the source of the sum introduction form.

  In the setting of this module's /n/-ary coproducts, coproducts only have a
  single type parameter, but an index plays an analogous role; all
  introduction forms for an /n/-ary coproduct are given by 'inj'. What is the
  analogous universal property?

  Suppose we pick some introduction form @inj' i \@n@ to generate an /n/-ary
  coproduct. @jam@ should always permit elimination of the coproduct in such a
  way that we recover exactly whichever object that @inj i \@n@ embedded
  into the position described by @i@ of the /n/-ary coproduct:

  >> ∀ i n a. jam @n @a ∘ (inj i @n @a) ≡ id @1 @a

  Plausible circumstances for how to accomplish this (see e.g. the use of
  @Additive@ in [Elliott 2018, §15](https://arxiv.org/pdf/1804.00746.pdf))
  include when @a@ has a monoid instance: @inj i \@n \@a@ creates something
  analogous to what is known in the machine learning literature as a "one-hot"
  vector, where the /i/th index of the target of @inj i \@n \@a@ is
  identical to the source, and all other indices are identical to /mempty/.
  @jam@, in this scenario, is essentially @foldMap id@. -}
  jam ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , Object φ k n a
      , Object φ k 1 a
      , JamObject φ k n a
      )
      ⇒ a -| k φ n 1 |-> a  -- ^ A /k/-morphism that folds an /n/-length coproduct down to a single summary value.

  jam' ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object φ k n a
       , Object φ k 1 a
       , JamObject φ k n a
       )
       ⇒ (Proxy φ k) n
       → a -| k φ n 1 |-> a  -- ^ A /k/-morphism that folds an /n/-length coproduct down to a single summary value.
  jam' (_ ∷ (Proxy φ k) n) = jam @κ @φ @k @n @a


{- | This is a "class synonym" for the type family 'JamObject'; it's often needed
to write quantified constraints. -}
class    (JamObject φ k n a)
  ⇒ JamObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (JamObject φ k n a)
  ⇒ JamObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


infixr 2 ▽
{- | Synonym for 'jam'. -}
(▽) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (a ∷ κ).
    ( KnownNat n
    , Object φ k n a
    , Object φ k 1 a
    , JamObject φ k n a
    , Codiagonal φ k
    )
    ⇒ a -| k φ n 1 |-> a  -- ^ A /k/-morphism that folds an /n/-length coproduct down to a single summary value.
(▽) = jam


instance (Codiagonal φ k, Proxy φ k ~ Proxy φ (o `Sub` k)) ⇒ Codiagonal φ (o `Sub` k) where
  type JamObject φ (o `Sub` k) n a = JamObject φ k n a
  jam = Sub jam
  jam' pn = Sub $ jam' pn


{- | This is a generic implementation for 'jam' in @Sized (->)@ in terms of
'foldMap\'' and 'pure' for any sized functor /φ/ with suitable
'Foldable' and 'Applicative' instances applied to objects with a 'Monoid'
instance.

This may be easier to use (require less cajoling of GHC) than 'JamMon'. -}
jamMon ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
      ( Foldable (φ n)
      , Applicative (φ 1)
      , Monoid a
      )
      ⇒ φ n a
      → φ 1 a
jamMon = pure ∘ foldMap' P.id

{- | Variant of 'jamMon' that uses (right-associative, non-strict) @fold@
instead of (left-associative, strict) @foldMap' id@. -}
jamMon' ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
      ( Foldable (φ n)
      , Applicative (φ 1)
      , Monoid a
      )
      ⇒ φ n a
      → φ 1 a
jamMon' = pure ∘ fold



{- | Newtype provididing a 'Codiagonal' instance for 'Sized (->)' constrained
to objects with a 'Monoid' instance and product functors /φ/ where

- /φ n/ is 'Foldable'.
- /φ 1/ has an 'Applicative' instance.

When these conditions hold, 'jam' ≈ 'foldMap id' (the strict, left-associative
analog of 'fold'). -}
newtype JamMon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (φ ∷  Nat → κ → κ)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ)
  = JamMon { unJamMon ∷ a -| k φ n m |-> b }


instance Semigroupoid φ k
  ⇒ Semigroupoid (φ ∷ Nat → Type → Type) (JamMon (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type))
  where
  type Object φ (JamMon k) n a = (Object φ k n a, Monoid a)
  (JamMon g) . (JamMon f) = JamMon (g . f)


instance ( Semigroupoid φ (JamMon k)
         , Category φ k
         , ∀ x. (Object' φ (JamMon k) n x, Monoid x) ⇒ Object' φ k n x
         ) ⇒ Category φ (JamMon k) where
  id = JamMon id


instance ( Category φ (JamMon k)
         , ∀ x. (Object' φ (JamMon k) n x, Monoid x) ⇒ Object' φ k n x
         , Monoidal φ k
         )
  ⇒ Monoidal φ (JamMon k) where
  type Proxy φ (JamMon k) = Proxy φ k

  (JamMon f) *** (JamMon g) = JamMon $ f *** g

  mul pn pm pn' pm' (JamMon f) (JamMon g) = JamMon $ mul pn pm pn' pm' f g

  ith     fn (JamMon f) = JamMon $ ith     fn f
  ith' pn fn (JamMon f) = JamMon $ ith' pn fn f

  sing     = JamMon   sing
  unsing   = JamMon   unsing
  join     = JamMon   join
  split    = JamMon   split
  assoc    = JamMon   assoc
  lift1    = JamMon ∘ lift1   ∘ unJamMon
  bisplit  = JamMon ∘ bisplit ∘ unJamMon
  bijoin   = JamMon ∘ bijoin  ∘ unJamMon
  biassoc  = JamMon ∘ biassoc ∘ unJamMon


instance ( Monoidal φ (JamMon k)
         , ∀ n. Foldable (φ n)
         , Applicative (φ 1)
         , k ~ Sized (->)
         )
  ⇒ Codiagonal φ (JamMon k) where
  jam = JamMon $ Sized (pure ∘ foldMap' P.id) -- strict, left-associative
  -- jam = JamMon $ (Sized $ pure ∘ fold) -- lazy, right-associative
