{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Category.Free.TTG
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
  ) where

import Prelude hiding
  ( id
  , (.)
  , foldMap
  , Functor
  )

import Data.Kind (Type)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Functor
  ( (::~>)
  , HFunctor ( hfmap
             )
  , Fix
  , cata
  , ana
  )

import Cat.Unsized.Category.Class
  ( Category ( id
             )
  , (.)
  , Object
  , Object'
  )
import Cat.Unsized.Semigroupoid.Free.Data
  ( HasObject (ObjectOf)
  )


data Cat x (k ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ) where
  EmbX ∷ ∀ x k a b.
       ( ObjectOf k a
       , ObjectOf k b
       )
       ⇒ XEmb x
       → a -|       k |-> b
       → a -| Cat x k |-> b

  IdX  ∷ ∀ x k a.
       ( ObjectOf k a )
       ⇒ XId x
       → a -| Cat x k |-> a

  OfX  ∷ ∀ x k a c b.
       ( ObjectOf k a
       , ObjectOf k c
       , ObjectOf k b
       )
       ⇒ XOf x
       → b -| Cat x k |-> c
       → a -| Cat x k |-> b
       → a -| Cat x k |-> c

  XCat ∷ ∀ x k a b.
       ( ObjectOf k a
       , ObjectOf k b
       )
       ⇒ !(XXCat x)
       → a -| Cat x k |-> b


type family XEmb  x
type family XId   x
type family XOf   x
type family XXCat x

deriving instance ( ∀ u v. Show (u `k` v)
                  , Show (XXCat x)
                  , Show (XOf x)
                  , Show (XId x)
                  , Show (XEmb x)
                  )
  ⇒ Show (a -| Cat x k |-> b)



data NoField = NoField
  deriving stock (Eq, Ord, Bounded, Enum, Show, Read)

data NoExt
  deriving stock (Eq, Ord, Show, Read)

noExt ∷ NoExt → a
noExt x = case x of {}


data CatF  x
          (k ∷ κ → κ → Type)
          (t ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) where

  EmbF ∷ ∀ x k t a b.
       ( ObjectOf k a, ObjectOf k b
       , Object   t a, Object   t b
       )
       ⇒ XEmb x
       → a -|        k   |-> b
       → a -| CatF x k t |-> b

  IdF  ∷ ∀ x k t a.
       ( ObjectOf k a
       , Object   t a
       )
       ⇒ XId x
       → a -| CatF x k t |-> a

  OfF  ∷ ∀ x k t a b c.
       ( ObjectOf k a, ObjectOf k b, ObjectOf k c
       , Object   t a, Object   t b, Object   t c
       )
       ⇒ XOf x
       → b -|          t |-> c
       → a -|          t |-> b
       → a -| CatF x k t |-> c

  XCatF ∷ ∀ x k t a b.
        ( ObjectOf k a, ObjectOf k b
        , Object   t a, Object   t b
        )
        ⇒ !(XXCat x)
        → a -| CatF x k t |-> b

deriving instance ( ∀ u v. Show (u -| k |-> v)
                  , ∀ u v. Show (u -| t |-> v)
                  , Show (XXCat x)
                  , Show (XOf   x)
                  , Show (XId   x)
                  , Show (XEmb  x)
                  )
  ⇒ Show (a -| CatF x k t |-> b)

type Cat' x k = Fix (CatF x k)


instance HFunctor (CatF x k) where
  hfmap _ (EmbF x m)  = EmbF x m
  hfmap _ (IdF x)     = IdF x
  hfmap α (OfF x g f) = OfF x (α g) (α f)
  hfmap _ (XCatF x)   = XCatF x


{- | Given

 - A function that maps morphisms made with the extension constructor to a
   morphism in a target category /t/.

 - A function that maps primitive morphisms to morphisms in a target category
   /t/.

this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ x κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type).
  (Category t)
  ⇒ (∀ a b. ( ObjectOf k a, Object t a
            , ObjectOf k b, Object t b
            )
     ⇒ XXCat x
     → a `t` b
    )               -- ^ A function mapping extension values into the target category.
  → (∀ a b. ( ObjectOf k a, Object t a
            , ObjectOf k b, Object t b
            )
     ⇒ a `k` b
     → a `t` b
     )               -- ^ A function mapping primitive morphisms into the target category.
  → CatF x k t ::~> t
mkAlg _ _ (IdF  _    ) = id
mkAlg _ _ (OfF  _ g f) = g . f
mkAlg _ α (EmbF _   f) = α f
mkAlg χ _ (XCatF x   ) = χ x


foldMap ∷ ∀ x κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ).
  ( Category t
  -- , Object (Fix (CatF k)) a
  -- , Object (Fix (CatF k)) b
  , (∀ o. Object (Fix (CatF x k)) o ⇒ Object' t o)
  )
  ⇒ (∀ u v. ( ObjectOf k u, Object t u
            , ObjectOf k v, Object t v
            )
     ⇒ XXCat x
     → u `t` v
    )               -- ^ A function mapping extension values into the target category.
  → (∀ u v. ( ObjectOf k u, Object t u
            , ObjectOf k v, Object t v
            )
     ⇒ u `k` v
     → u `t` v
     )               -- ^ A function mapping primitive morphisms into the target category.
  → (  a -| Fix (CatF x k) |-> b
    →  a        `t`            b
    )
foldMap χ α = cata (mkAlg χ α)


{- | Coalgebra for converting a @Cat x k@ morphism to a @Cat' x k@ morphism. -}
fixedCoalg ∷ ∀ x k a b.
  (∀ o. ObjectOf k o ⇒ Object' (Cat x k) o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -|           Cat x k  |-> b
  → a -| CatF x k (Cat x k) |-> b
fixedCoalg (IdX  x    ) = IdF   x
fixedCoalg (EmbX x m  ) = EmbF  x m
fixedCoalg (OfX  x g f) = OfF   x g f
fixedCoalg (XCat x    ) = XCatF x


{- | Convert a @Cat x k@ morphism to a @Cat' x k@ morphism. -}
fixed ∷ ∀ x k a b.
  ( ∀ o. ObjectOf k o ⇒ Object' (Cat x k) o
  , ∀ o. Object (Cat x k) o ⇒ Object' (Cat' x k) o
  )
  ⇒ a -| Cat  x k |-> b  -- ^ A @Cat x k@ morphism.
  → a -| Cat' x k |-> b  -- ^ An equivalent morphism in @Fix (CatF x k)@.
fixed = ana fixedCoalg



{- | Algebra for converting a @Cat' x k@ morphism to a @Cat x k@ morphism. -}
unfixedAlg ∷ ∀ x k a b.
    a -| CatF x k (Cat x k) |-> b
  → a -|           Cat x k  |-> b
unfixedAlg (IdF   x    ) = IdX  x
unfixedAlg (OfF   x g f) = OfX  x g f
unfixedAlg (EmbF  x m  ) = EmbX x m
unfixedAlg (XCatF x    ) = XCat x


{- | Convert a @Cat' x k@ morphism to a @Cat x k@ morphism. -}
unfixed ∷ ∀ x k a b.
  (∀ o. Object (Cat' x k) o ⇒ Object' (Cat x k) o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -| Cat' x k |-> b  -- ^ A @Cat' x k@ morphism.
  → a -| Cat  x k |-> b  -- ^ An equivalent @Cat x k@ morphism.
unfixed = cata unfixedAlg


