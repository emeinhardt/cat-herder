{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- |

module Cat.Sized.Category.Free.TTG
  ( Cat ( EmbX
        , IdX
        , OfX
        , XCat
        )
  , XEmb
  , XId
  , XOf
  , XXCat
  , NoField (NoField)
  , NoExt
  , noExt


   -- * Recursion schemes
  , CatF ( EmbF
         , IdF
         , OfF
         , XCatF
         )
  , Cat'
  , mkAlg
  , foldMap
  , fixed
  , fixedCoalg
  , unfixed
  , unfixedAlg

   -- * Re-exports from "Cat.Unsized.Semigroupoid.Free.Data"
  , HasObject (ObjectOf)
  , P (P)
  , To (To)
  ) where

import Prelude hiding
  ( (.)
  , id
  , foldMap
  )

import GHC.TypeNats (Nat, KnownNat)
import Data.Kind (Type)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Functor
  ( NT'
  , HFunctor ( hfmap
             , HFunctorObj
             )
  , Fix
  , cata
  , ana
  )

import Cat.Sized.Category.Class
  ( Category (id)
  , (.)
  , Object
  , Object'
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( HasObject ( ObjectOf )
  , P (P)
  , To (To)
  )



data Cat  x
         (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
         (n ∷ Nat) (m ∷ Nat)
         (a ∷ κ)   (b ∷ κ)   where

  EmbX ∷ ∀ x φ k n m a b.
       ( KnownNat n, KnownNat m
       , ObjectOf φ k n a, ObjectOf φ k m b
       )
       ⇒ XEmb x
       → a -|       k φ n m |-> b
       → a -| Cat x k φ n m |-> b

  OfX  ∷ ∀ x φ k n m l a c b.
       ( KnownNat n, KnownNat m, KnownNat l
       , ObjectOf φ k n a, ObjectOf φ k m c, ObjectOf φ k l b
       )
       ⇒ XOf x
       → b -| Cat x k φ l m |-> c
       → a -| Cat x k φ n l |-> b
       → a -| Cat x k φ n m |-> c

  IdX  ∷ ∀ x φ k n a.
       ( KnownNat n
       , ObjectOf φ k n a
       )
       ⇒ XId x
       → a -| Cat x k φ n n |-> a

  XCat ∷ ∀ x φ k n m a b.
       ( ObjectOf φ k n a
       , ObjectOf φ k m b
       )
       ⇒ !(XXCat x)
       → a -| Cat x k φ n m |-> b

type family XEmb  x
type family XId   x
type family XOf   x
type family XXCat x

deriving instance ( ∀ i j u v. Show (u -| k φ i j |-> v)
                  , Show (XXCat x)
                  , Show (XOf   x)
                  , Show (XId   x)
                  , Show (XEmb  x)
                  )
  ⇒ Show (a -| Cat x k φ n m |-> b)


data NoField = NoField
  deriving stock (Eq, Ord, Bounded, Enum, Show, Read)

data NoExt
  deriving stock (Eq, Ord, Show, Read)

noExt ∷ NoExt → a
noExt x = case x of {}



data CatF  x
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (φ ∷ Nat → κ → κ)
          -- (γ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   where

  EmbF ∷ ∀ x φ k t n m a b.
       ( KnownNat n, KnownNat m
       , ObjectOf φ k n a, ObjectOf φ k m b
       , Object   φ t n a, Object   φ t m b
       )
       ⇒ XEmb x
       → a -|        k   φ n m |-> b
       → a -| CatF x k t φ n m |-> b

  IdF ∷ ∀ x φ k t n a.
      ( KnownNat n
      , ObjectOf φ k n a
      , Object   φ t n a
      )
      ⇒ XId x
      → a -| CatF x k t φ n n |-> a

  OfF ∷ ∀ x φ k t n m l a c b.
      ( KnownNat n, KnownNat m, KnownNat l
      , ObjectOf φ k n a, ObjectOf φ k m c, ObjectOf φ k l b
      , Object   φ t n a, Object   φ t m c, Object   φ t l b
      )
      ⇒ XOf x
      → b -|          t φ l m |-> c
      → a -|          t φ n l |-> b
      → a -| CatF x k t φ n m |-> c

  XCatF ∷ ∀ x φ k t n m a b.
        ( ObjectOf φ k n a, ObjectOf φ k m b
        , Object   φ t n a, Object   φ t m b
        )
        ⇒ !(XXCat x)
        → a -| CatF x k t φ n m |-> b


deriving instance ( ∀ i j u v. Show (u -| k φ i j |-> v)
                  , ∀ i j u v. Show (u -| t φ i j |-> v)
                  , Show (XXCat x)
                  , Show (XOf   x)
                  , Show (XId   x)
                  , Show (XEmb  x)
                  )
  ⇒ Show (a -| CatF x k t φ n m |-> b)


type Cat' x k = Fix (CatF x k)

instance HFunctor (CatF x k) where
  hfmap _ (EmbF  x  m ) = EmbF  x m
  hfmap _ (IdF   x    ) = IdF   x
  hfmap α (OfF   x g f) = OfF   x (α g) (α f)
  hfmap _ (XCatF x    ) = XCatF x


{- | Given

 - A function that maps morphisms made with the extension constructor to a
   morphism in a target category /t/.

 - A function that maps primitive morphisms to morphisms in a target category
   /t/.

this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ x κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type).
  ( Category φ t
  -- ∀ o. ObjectOf k o ⇒ Object' t o
  )
  ⇒ (∀ i j u v.
     ( ObjectOf φ k i u, ObjectOf φ k j v
     , Object   φ t i u, Object   φ t j v
     )
     ⇒ XXCat x
     → u -| t φ i j |-> v
     )                                -- ^ A function mapping extension values into the target category.
  → (∀ i j u v.
     ( ObjectOf φ k i u, ObjectOf φ k j v
     , Object   φ t i u, Object   φ t j v
     )
     ⇒ u -| k φ i j |-> v
     → u -| t φ i j |-> v
     )                                -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → NT' φ (CatF x k t) t
mkAlg _ _ (IdF   _    ) = id
mkAlg _ _ (OfF   _ g f) = g . f
mkAlg _ α (EmbF  _   f) = α f
mkAlg χ _ (XCatF x    ) = χ x


foldMap ∷ ∀ x κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (n ∷ Nat) (m ∷ Nat)
  (a ∷ κ)   (b ∷ κ).
  ( Category φ t
  -- , Object φ (Fix (CatF k)) n a
  -- , Object φ (Fix (CatF k)) m b
  , (∀ i o. Object φ (Fix (CatF x k)) i o ⇒ Object' φ t i o)
  )
  ⇒ (∀ i j u v.
     ( ObjectOf φ k i u, ObjectOf φ k j v
     , Object   φ t i u, Object   φ t j v
     )
     ⇒ XXCat x
     → u -| t φ i j |-> v
     )                                -- ^ A function mapping extension values into the target category.
  → (∀ i j u v.
     ( ObjectOf φ k i u, ObjectOf φ k j v
     , Object   φ t i u, Object   φ t j v
     )
     ⇒ u -| k φ i j |-> v
     → u -| t φ i j |-> v
     )                                -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → (  a -| Fix (CatF x k) φ n m |-> b
    →  a -|        t       φ n m |-> b
    )
foldMap χ α = cata (mkAlg χ α)


{- | Coalgebra for converting a @Cat x k@ morphism to a @Cat' x k@ morphism. -}
fixedCoalg ∷ ∀ x φ k n m a b.
  ( ∀ j o. ObjectOf φ k j o ⇒ Object' φ (Cat x k) j o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -|           (Cat x k)  φ n m |-> b
  → a -| (CatF x k (Cat x k)) φ n m |-> b
fixedCoalg (IdX  x    ) = IdF  x
fixedCoalg (EmbX x m  ) = EmbF x m
fixedCoalg (OfX  x g f) = OfF  x g f
fixedCoalg (XCat x    ) = XCatF x


{- | Convert a @Cat x k@ morphism to a @Cat' x k@ morphism. -}
fixed ∷ ∀ x k φ n m a b.
  ( ∀ i o. ObjectOf φ        k  i o ⇒ Object' φ (Cat  x k) i o
  , ∀ i o. Object   φ (Cat x k) i o ⇒ Object' φ (Cat' x k) i o
  , HFunctorObj (CatF x k) φ (Cat x k) (Cat' x k)
  )
  ⇒ a -| Cat  x k φ n m |-> b  -- ^ A @Cat x k@ morphism.
  → a -| Cat' x k φ n m |-> b  -- ^ A @Fix (CatF x k)@ morphism.
fixed = ana fixedCoalg


{- | Algebra for converting a @Cat' x k@ morphism to a @Cat x k@ morphism. -}
unfixedAlg ∷ ∀ x k φ n m a b.
    a -| CatF x k (Cat x k) φ n m |-> b
  → a -|          (Cat x k) φ n m |-> b
unfixedAlg (IdF   x    ) = IdX  x
unfixedAlg (OfF   x g f) = OfX  x g f
unfixedAlg (EmbF  x m  ) = EmbX x m
unfixedAlg (XCatF x    ) = XCat x


{- | Convert a @Cat' x k@ morphism to a @Cat x k@ morphism. -}
unfixed ∷ ∀ x k φ n m a b.
  (∀ i o. Object φ (Cat' x k) i o ⇒ Object' φ (Cat x k) i o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -| Cat' x k φ n m |-> b  -- ^ A @Cat' x k@ morphism.
  → a -| Cat  x k φ n m |-> b  -- ^ An equivalent @Cat x k@ morphism.
unfixed = cata unfixedAlg
