{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Sized.Semigroupoid.Class
  ( Semigroupoid
      ( Object
      , (.)
      )
  , Object'
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)

    -- * Constraining an existing 'Semigroupoid'
  , Sub (Sub, unSub)
  , sub
  , unsub

    -- * Lifting an unsized morphism into a sized one
  , Sized ( Sized, unSized )

    -- * Forgetting the size structure of a sized morphism
  , Unsized ( Forget )
  , remember

    -- * Lifting a size-independent constraint to a sized one
  , SizedCon
  ) where

import Prelude hiding
  ( (.)
  , Functor
  , fmap
  )

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4
  )
import GHC.TypeNats (Nat, KnownNat)

import Data.Functor        qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )


{- | This typeclass doesn't make much sense outside of the context of the
@Monoidal@ typeclass in "Cat.Sized.Monoidal"; anything that has an instance of
'Semigroupoid' ought to be capable of have a @Monoidal@ instance as well; this
typeclass exists more for Haskell-shaped reasons. -}
class Semigroupoid (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type Object (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type Object φ k n a = Unconstrained4 φ k n a

  -- TODO @limbo: do KnownNat n,m,l as constraints add anything here?
  infixr 9 .
  (.) ∷ ∀ (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
      ( KnownNat n, KnownNat m, KnownNat l
      , Object φ k n a, Object φ k m b, Object φ k l x
      )
       ⇒ x -| k φ l m |-> b  -- ^ A morphism from @φ l x@ to @φ m b@.
       → a -| k φ n l |-> x  -- ^ A morphism from @φ n a@ to @φ l x@.
       → a -| k φ n m |-> b  -- ^ A morphism from @φ n a@ to @φ m b@.


{- | This is a "class synonym" for the type family 'Object'; it's often needed to
write quantified constraints. -}
class    (Object φ k n a)
  ⇒ Object' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (Object φ k n a)
  ⇒ Object' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


infixr 1 <<<
(<<<) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
            (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
      ( KnownNat n, KnownNat m, KnownNat l
      , Object φ k n a, Object φ k m b, Object φ k l x
      , Semigroupoid φ k
      )
      ⇒ x -| k φ l m |-> b  -- ^ A morphism from @φ l x@ to @φ m b@.
      → a -| k φ n l |-> x  -- ^ A morphism from @φ n a@ to @φ l x@.
      → a -| k φ n m |-> b  -- ^ A morphism from @φ n a@ to @φ m b@.
(<<<) = (.)


infixr 1 >>>
(>>>) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
            (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
      ( KnownNat n, KnownNat m, KnownNat l
      , Object φ k n a, Object φ k m b, Object φ k l x
      , Semigroupoid φ k
      )
      ⇒ a -| k φ n l |-> x  -- ^ A morphism from @φ n a@ to @φ l x@.
      → x -| k φ l m |-> b  -- ^ A morphism from @φ l x@ to @φ m b@.
      → a -| k φ n m |-> b  -- ^ A morphism from @φ n a@ to @φ m b@.
(>>>) = flip (.)


infixr 9 ∘
(∘) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
    (
      KnownNat n, KnownNat m, KnownNat l
    , Object φ k n a, Object φ k m b, Object φ k l x
    , Semigroupoid φ k
    )
    ⇒ x -| k φ l m |-> b  -- ^ A morphism from @φ l x@ to @φ m b@.
    → a -| k φ n l |-> x  -- ^ A morphism from @φ n a@ to @φ l x@.
    → a -| k φ n m |-> b  -- ^ A morphism from @φ n a@ to @φ m b@.
(∘) = (.)


infixr 9 ⊙
{- | Unicode synonym for '.' that avoids overlap with either '.' or '∘'.

This is frequently used internally in this package instead of '.'. -}
(⊙) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
    (
      KnownNat n, KnownNat m, KnownNat l
    , Object φ k n a, Object φ k m b, Object φ k l x
    , Semigroupoid φ k
    )
    ⇒ x -| k φ l m |-> b  -- ^ A morphism from @φ l x@ to @φ m b@.
    → a -| k φ n l |-> x  -- ^ A morphism from @φ n a@ to @φ l x@.
    → a -| k φ n m |-> b  -- ^ A morphism from @φ n a@ to @φ m b@.
(⊙) = (.)



{- | A morphism of @κ@ restricted to objects that also satisfy some constraint
@o@.

The constructor is exposed for extensibility of 'Sub', but you should use the
smart constructor that enforces that the constraint 'o' actually holds of the
source and target. -}
newtype Sub (o ∷  Nat → κ → Constraint)
            (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (φ ∷  Nat → κ → κ)
            (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ)
  = Sub { unSub ∷ a -| k φ n m |-> b }

-- | Smart constructor for 'Sub' that enforces the relevant constraint.
sub ∷ ∀ o φ k n m a b .
    ( Semigroupoid φ k
    , o n a, o m b
    )
    ⇒ a -| k φ n m |-> b
    → a -| (o `Sub` k) φ n m |-> b
sub = Sub


unsub ∷ ∀ o φ k n m a b .
      ( Semigroupoid φ k
      , o n a, o m b
      )
      ⇒ a -| (o `Sub` k) φ n m |-> b
      → a -| k φ n m |-> b
unsub = unSub


instance Semigroupoid φ k ⇒ Semigroupoid φ (o `Sub` k) where
  type Object φ (o `Sub` k) n a = (Object φ k n a, o n a)
  (Sub g) . (Sub f) = Sub (g . f)


-- TODO @limbo-test see how far you can get with Sized as a newtype rather than 'data'?
-- data Sized (k ∷ κ → κ → Type) (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) where
--   Sized ∷ (KnownNat n, KnownNat m) ⇒ φ n a `k` φ m b → Sized k φ n m a b

-- unSized ∷ (a -| (Sized k) φ n m |-> b)
--      → φ n a `k` φ m b
-- unSized (Sized f) = f


{- | In a general category /k ∷ κ → κ → Type/ where /φ/ is an /n/-ary monoidal
product functor, a value @f ∷ Sized k φ n m a b@ represents a /k/ morphism that
maps the object (type) /φ n a/ to the object (type) /φ m b/, where /a/ and /b/
are also objects of the /k/. (Note that in general, this means /a/ or /b/ could
also be products.)

Note that by wrapping such a value in this type, each part of the type of such a
morphism is more legible to typechecking. This is one motivation for the
@...Sized...@ modules in this package and why they nearly exclusively work with
morphisms of type @k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ@. -}
newtype Sized (k ∷ κ → κ → Type) (φ ∷ Nat → κ → κ)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ)   (b ∷ κ)
  = Sized { unSized ∷ φ n a `k` φ m b }

-- -- TODO @limbo Can the constraints here actually communicate useful extra
-- -- information to GHC? I.e. is there any reason to have this function around
-- -- instead of the newtype constructor?
-- sized ∷ ∀ k φ n m a b. ( KnownNat n, KnownNat m )
--       ⇒ φ n a `k` φ m b
--       → a -| (Sized k) φ n m |-> b
-- sized = Sized

-- unsized ∷ ∀ k φ n m a b. ( KnownNat n, KnownNat m )
--         ⇒ a -| (Sized k) φ n m |-> b
--         → φ n a `k` φ m b
-- unsized = unSized

deriving instance (                    F.Functor   (φ m), F.Functor   (k (φ n a))) ⇒ F.Functor  (Sized k φ n m a)
deriving instance ( Foldable    (φ n), Foldable    (φ m), Foldable    (k (φ n a))) ⇒ Foldable   (Sized k φ n m a)
deriving instance ( F.Functor   (φ n), F.Functor   (φ m), F.Functor   (k (φ n a))
                  , Foldable    (φ n), Foldable    (φ m), Foldable    (k (φ n a))
                  , Traversable (φ n), Traversable (φ m), Traversable (k (φ n a))) ⇒ Traversable (Sized k φ n m a)
deriving instance (∀ i j x y. Show (φ i x `k` φ j y)) ⇒ Show (Sized k φ n m a b)
deriving instance (∀ i j x y. Eq   (φ i x `k` φ j y)) ⇒ Eq   (Sized k φ n m a b)
deriving instance (∀ i j x y. Ord  (φ i x `k` φ j y)) ⇒ Ord  (Sized k φ n m a b)



{- | Dual to 'Sized', this is a type that can permit any sized morphism to be used
as an unsized one. -}
data Unsized (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (fna ∷ κ) (fmb ∷ κ) where
  Forget ∷ ∀ k φ n m a b.
         ( KnownNat n, KnownNat m
         , Object φ k n a, Object φ k m b
         )
         ⇒ a -| k φ n m |-> b
         → Unsized φ k (φ n a) (φ m b)

deriving instance (∀ i j x y. Show (x -| k φ i j |-> y)) ⇒ Show (Unsized φ k (φ n a) (φ m b))
deriving instance (∀ i j x y. Eq   (x -| k φ i j |-> y)) ⇒ Eq   (Unsized φ k (φ n a) (φ m b))
deriving instance (∀ i j x y. Ord  (x -| k φ i j |-> y)) ⇒ Ord  (Unsized φ k (φ n a) (φ m b))


-- TODO @limbo Is this actually useable / when?
remember ∷ ∀ k φ n m a b. (KnownNat n, KnownNat m, Object φ k n a, Object φ k m b)
        ⇒ φ n a -| Unsized φ k |-> φ m b
        →     a -| k φ n m     |->     b
remember (Forget f) = f




{- | A class synonym that lifts a constraint indifferent to multiplicity ("size") into
one that takes a size as a leading parameter.

For example, given

@
class BoolObj (a ∷ Type) where
  true   ∷ a
  false  ∷ a
  asBool ∷ a → Bool

instance BoolObj Bool where
  true   = True
  false  = False
  asBool = Prelude.id
@

then usage would be:

@
type SizedBoolObj = SizedCon BoolObj
@

where

>>> :k BoolObj
>> BoolObj ∷ Type → Constraint
>>> :k SizedBoolObj
>> SizedBoolObj ∷ Nat → Type → Constraint
-}
class (obj a) ⇒ SizedCon (obj ∷ κ → Constraint) (n ∷ Nat) (a ∷ κ)
instance (obj a) ⇒ SizedCon obj n a
