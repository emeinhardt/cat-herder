{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{- | This module contains an extensible variant of "Cat.Unsized.Category.Free"
based on
[trees that grow](https://gitlab.haskell.org/ghc/ghc/-/wikis/implementing-trees-that-grow/trees-that-grow-guidance).
See
 - The @ghc@ gitlab wiki page linked above for general reference
 - "Cat.Unsized.GraphViz" for a module that uses extension fields for pretty
   printing to GraphViz graphs
 - "Cat.Unsized.Examples.Arith" for a worked example using the GraphViz
   functionality.


== "Trees that Grow" summary

"Trees That Grow" is an approach to solving
"[the AST typing problem](http://blog.ezyang.com/2013/05/the-ast-typing-problem)";
to wit, how should one go about adding extra information to an abstract syntax tree
type in a way that hits some sweet spot of trade-offs with respect to concerns like:

  - Code re-use and avoiding boilerplate.
  - Clear and accurate domain modeling with types.
  - Type-safety.

The basic idea is to mechanically transform a declaration of a basic AST @t@
into a new type @t'@ by

 - Adding an extra leading type parameter @x@ to @t'@ relative to @t@ —
   /the phase index/. This is a "phantom" type ("type tag") with no constructors
   actually appearing on the right-hand side of any of @t@'s constructors.

 - Adding an extra field @tfᵢ x@ to each constructor of @t@ — the
   /extension field/. The type of this field is allowed to be different for each
   constructor (via type families) and is allowed to be different for different
   phases (again, via type families); there is a type family @tfᵢ x@ (indexed by a
   phase tag @x@) for each constructor (indexed by @i@).

 - Adding one extra constructor @ext@ to @t'@ relative to @t@ — the
   /extension constructor/; the payload type that this constructor wraps
   is again given by a type family indexed by a phase tag.


== Why TTG?

Per the blog post above, there are many approaches to the AST typing problem,
and this module is just one of them; it's not a priori clear to me how their
trade-offs play out in the main setting of interest to this package, but three
things stand out about TTG:

  - TTG is good enough for some parts of GHC.
  - Between phase indices, constructor- and index-specific extension fields, and
    an extension constructor, a TTG type offers a lot of flexibility for adding
    annotations while permitting re-use of code related to AST traversals or
    transformations and use of fairly simple mechanisms for introducing or
    eliminating annotations.
  - A downside is the extra type family and even more basic instance definitions
    (e.g. @Semigroupoid@, @Category@) that need to be defined for every phase of
    interest.
-}

module Cat.Unsized.Category.Free.TTG
  ( Cat ( Emb
        , Id
        , Of
        , XCat
        )
  , XEmb
  , XId
  , XOf
  , XXCat
  , NoField (NoField)
  , NoExt
  , noExt
  , foldMap

   -- * Recursion schemes
  , CatF ( EmbF
         , IdF
         , OfF
         , XCatF
         )
  , Cat'
  , mkAlg
  , foldMap'
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
  Emb ∷ ∀ x k a b.
      ( ObjectOf k a
      , ObjectOf k b
      )
      ⇒ XEmb x
      → a -|       k |-> b  -- ^ A /k/-morphism to freely lift into a category.
      → a -| Cat x k |-> b

  Id  ∷ ∀ x k a.
      ( ObjectOf k a )
      ⇒ XId x
      → a -| Cat x k |-> a

  Of  ∷ ∀ x k a c b.
      ( ObjectOf k a
      , ObjectOf k c
      , ObjectOf k b
      )
      ⇒ XOf x
      → b -| Cat x k |-> c  -- ^ A morphism from @b@ to @c@.
      → a -| Cat x k |-> b  -- ^ A morphism from @a@ to @b@.
      → a -| Cat x k |-> c

  -- TODO The original setting of "Trees That Grow" is, well, *trees*: Consider
  -- whether it's worth constraining (or *morally correct* to constrain)
  -- @XXCat x@ to be of kind @κ → κ → Type@.
  XCat ∷ ∀ x k a b.
       ( ObjectOf k a
       , ObjectOf k b
       )
       ⇒ !(XXCat x)          -- ^ An extension value.
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



foldMap ∷ ∀ x k t a b.
  ( Category t
  , ∀ o. ObjectOf k o ⇒ Object' t o
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
  → a -| Cat x k |-> b            -- ^ A path in the free category over @k@.
  → a    `t`         b            -- ^ The resulting morphism in @t@.
foldMap _ α (Emb  _   f) = α f
foldMap _ _ (Id   _    ) = id
foldMap χ α (Of   _ g f) = foldMap χ α g . foldMap χ α f
foldMap χ _ (XCat x    ) = χ x



data CatF  x
          (k ∷ κ → κ → Type)
          (t ∷ κ → κ → Type)
          (a ∷ κ) (b ∷ κ) where

  EmbF ∷ ∀ x k t a b.
       ( ObjectOf k a, ObjectOf k b
       , Object   t a, Object   t b
       )
       ⇒ XEmb x
       → a -|        k   |-> b  -- ^ A /k/-morphism to freely lift into a category.
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
       → b -|          t |-> c  -- ^ A /t/-morphism from @b@ to @c@.
       → a -|          t |-> b  -- ^ A /t/-morphism from @a@ to @b@.
       → a -| CatF x k t |-> c

  -- TODO The original setting of "Trees That Grow" is, well, *trees*: Consider
  -- whether it's worth constraining (or *morally correct* to constrain)
  -- @XXCat x@ to be of kind @κ → κ → Type@.
  XCatF ∷ ∀ x k t a b.
        ( ObjectOf k a, ObjectOf k b
        , Object   t a, Object   t b
        )
        ⇒ !(XXCat x)             -- ^ An extension value.
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



foldMap' ∷ ∀ x κ (k ∷ κ → κ → Type) (t ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ).
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
foldMap' χ α = cata (mkAlg χ α)



{- | Coalgebra for converting a @Cat x k@ morphism to a @Cat' x k@ morphism. -}
fixedCoalg ∷ ∀ x k a b.
  (∀ o. ObjectOf k o ⇒ Object' (Cat x k) o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -|           Cat x k  |-> b
  → a -| CatF x k (Cat x k) |-> b
fixedCoalg (Id   x    ) = IdF   x
fixedCoalg (Emb  x m  ) = EmbF  x m
fixedCoalg (Of   x g f) = OfF   x g f
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
unfixedAlg (IdF   x    ) = Id   x
unfixedAlg (OfF   x g f) = Of   x g f
unfixedAlg (EmbF  x m  ) = Emb  x m
unfixedAlg (XCatF x    ) = XCat x


{- | Convert a @Cat' x k@ morphism to a @Cat x k@ morphism. -}
unfixed ∷ ∀ x k a b.
  (∀ o. Object (Cat' x k) o ⇒ Object' (Cat x k) o)  -- Constraint can be satisfied wherever phase-specific analogues of instances from Cat.Sized.Category.Free.Instances are in scope.
  ⇒ a -| Cat' x k |-> b    -- ^ A @Cat' x k@ morphism.
  → a -| Cat  x k |-> b    -- ^ An equivalent @Cat x k@ morphism.
unfixed = cata unfixedAlg
