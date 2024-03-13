{-# OPTIONS_HADDOCK show-extensions #-}
{- |

This module exports class and instance namespaces for @Unsized@ (pro)functors,
semigroupoids, and categories, excluding anything related to monads, comonads,
free semigroupoids or free categories.

For the time being, the only link between the unsized class hierarchy and the sized
one is provided via three routes, described below.


== Lifting "unsized" morphisms with a @Nat@-indexed functor /φ ∷ Nat → κ → κ/ via @Sized@

In "Cat.Sized.Semigroupoid.Class":

> newtype Sized k φ n m a b = Sized { unSized ∷ φ n a `k` φ m b } deriving ...

In "Cat.Sized.Semigroupoid.Instances":

> instance (Unsized.Semigroupoid k) ⇒ Sized.Semigroupoid φ (Sized k) where
>   type Object φ (Sized k) n a = Unsized.Object k a
>   (Sized g) . (Sized f) = Sized $ (g . f)

In "Cat.Sized.Category.Instances":

> instance (Unsized.Category k, Sized.Semigroupoid φ (Sized k)) ⇒ Sized.Category φ (Sized k) where
>  id = Sized Unsized.id

In "Cat.Sized.Monoidal.Instances":

> instance ( KnownNat n
>          , Unsized.Category k
>          , Unsized.Functor (φ n) k k
>          , ∀ x. Unsized.Object k x ⇒ Unsized.Object' k (φ n x)
>          , Monoidal φ (Sized k)
>          )
>          ⇒ Unsized.Functor (φ n) k (Sized k φ 1 1) where
>  fmap (f ∷ a `k` b) = bisplit ∘ Sized ∘ Unsized.fmap $ f


== Forgetting the "sized product" structure via @Unsized@

In "Cat.Sized.Semigroupoid.Class":

> data Unsized (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (fna ∷ κ) (fmb ∷ κ) where
>   Forget ∷ ∀ k φ n m a b. (KnownNat n, KnownNat m) ⇒ a -| k φ n m |-> b → Unsized φ k (φ n a) (φ m b)

In "Cat.Sized.Semigroupoid.Instances":

> instance (Semigroupoid φ k) ⇒ Unsized.Semigroupoid (Unsized φ k) where
>   type Object (Unsized φ k) (φ n a) = Object φ k n a
>   (Forget (g ∷ b -| k φ l m |-> c)) . (Forget (f ∷ a -| k φ n l |-> b)) = Forget (g . f)


== Treating "sized" morphisms where sizes match as an "unsized" category

In "Cat.Sized.Semigroupoid.Instances":

> instance (KnownNat n, Semigroupoid φ k) ⇒ Unsized.Semigroupoid (k φ n n) where
>   type Object (k φ n n) a = Object φ k n a
>   (.) = (.)

In "Cat.Sized.Category.Instances":

> instance (KnownNat n, Category φ k, Unsized.Semigroupoid (k φ n n))
>   ⇒ Unsized.Category (k φ n n) where
>   id = Sized.id

For the time being, this is mostly used to define ("unsized") functor instances

 - Lift a morphism @a -| (Sized (->)) φ n n |-> b@ to
   @φ l a -| (Sized (->)) φ n n |-> φ l b@ when @φ l@ is a "Data.Functor" instance.
 - \"Factor\" the products of (\"reshape\") both the source and target of a morphism
   @a -| k φ (i * n) (i * n) |-> b@ to yield a morphism
   @φ i a -| k φ n n |-> φ i b@ via the @Factor@ newtype.


-}

module Cat.Unsized
  ( module Cat.Unsized.Functor
  , module Cat.Unsized.Profunctor
  , module Cat.Unsized.Semigroupoid
  , module Cat.Unsized.Category
  ) where

import Cat.Unsized.Functor
import Cat.Unsized.Profunctor
import Cat.Unsized.Semigroupoid
import Cat.Unsized.Category
