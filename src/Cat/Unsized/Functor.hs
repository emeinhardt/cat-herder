{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |

module Cat.Unsized.Functor
  ( Functor ( fmap )
  , NatTrans ( hoist
             , comp
             )
  , Distributes ( dist
                )

    -- * Recursion schemes
  , (:~>)
  , (::~>)
  , HFunctor ( hfmap
             )
  , Fix (In, out)
  , cata
  , ana
  , K (K, unK)
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , Monad
  , return
  )
import Prelude.Unicode ((∘))

import Data.Kind    (Type)
import GHC.Generics (Generic)

import Data.Functor qualified as F

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid (Object)
  , (.)
  , Object'
  )
import Cat.Unsized.Category.Class
  ( Category
  , id
  )



{- | A functor from one category to another. -}
class ( Category r, Category t
      ) ⇒ Functor (φ ∷ κ  → κ')
                  (r ∷ κ  → κ  → Type)
                  (t ∷ κ' → κ' → Type)
  where
  fmap ∷ ∀ (a ∷ κ) (b ∷ κ).
       ( Object r a, Object t (φ a)
       , Object r b, Object t (φ b)
       )
       ⇒   a `r`   b  -- ^ The source morphism from @r@.
       → φ a `t` φ b  -- ^ The resulting morphism in @t@.

{- | Use any "Data.Functor" instance as an endofunctor on '(->)', as you'd expect. -}
instance (F.Functor φ, Category (->)) ⇒ Functor φ (->) (->) where
  fmap = F.fmap


{- | Given functors @φ@ and @γ@ from the category @r@ to the category @t@, a
   natural transformation from @φ@ to @γ@ is (equivalently)

 - An assignment to every object @a@ of @c@ a morphism @ucomp ∷ φ a \`t\` γ a@.

 - An assignment to every morphism @f ∷ a \`r\` b@ a morphism
   @hoist f ∷ φ a \`t\` γ b@ such that for every composition of @r@ morphisms
   @g ∘ f@:

    @(fmap g ∷ γ a \`t\` γ b) ∘ (hoist f ∷ φ a \`t\` γ b) ≡ (hoist g ∷ φ a \`t\` γ b) ∘ (fmap f ∷ φ a \`r\` φ b)@

'hoist' and 'comp' can each be defined in terms of the other (+/- a 'Functor'
instance) given satisfactory constraints.
-}
class ( Category r, Category t
      -- , Functor φ r t, Functor γ r t
      )
      ⇒ NatTrans
          (φ ∷ κ  → κ')  -- ^ The source functor from @r@ to @t@.
          (γ ∷ κ  → κ')  -- ^ The target functor from @r@ to @t@.
          (r ∷ κ  → κ  → Type)
          (t ∷ κ' → κ' → Type)
  where

  {- | Note that when the additional constraints @Object t (γ b)@ and
  @Functor φ r t@ hold, a default definition is available in terms of @comp@
  and @fmap@:

  >>> hoist f ≝ comp @κ @κ' @φ @γ @r @t . fmap f
  -}
  hoist ∷ ∀ (a ∷ κ) (b ∷ κ).
        ( Object r    a , Object r    b
        , Object t (φ a), Object t (γ b)
        )
        ⇒   a `r`   b  -- ^ The source morphism in @r@ from @a@ to @b@.
        → φ a `t` γ b  -- ^ The resulting morphism in @t@ taking @φ a@ to @γ b@.

  default hoist ∷ ∀ (a ∷ κ) (b ∷ κ).
        ( Object r    a , Object r    b
        , Object t (φ a), Object t (φ b)
        ,                 Object t (γ b)  -- NOTE This and @Functor φ r t @ are
        , Functor φ r t                   -- the extra constraints needed for a
        )                                 -- default definition in terms of
        ⇒   a `r`   b                     -- @fmap@ and @comp@.
        → φ a `t` γ b
  hoist f = comp @κ @κ' @φ @γ @r @t . fmap f

  {- | Note that when the additional constraint @Object φ r n a@ holds, a default
  definition is available in terms of @hoist@:

  >>> comp ≝ hoist (id @κ @r)
  -}
  comp ∷ ∀ (a ∷ κ).
       ( Object t (φ a)
       , Object t (γ a)
       )
       ⇒ φ a `t` γ a  -- ^ The @a@-component of the natural transformation.

  default comp ∷ ∀ (a ∷ κ).
        ( Object t (φ a)
        , Object t (γ a)
        , Object r    a  -- NOTE This is the extra constraint needed for a default definition.
        )
        ⇒ φ a `t` γ a
  comp = hoist (id @κ @r)




{- | This typeclass currently exists specifically for the context of bikleisli
arrows. No thought has yet been given to its interaction with e.g.
@Distributive@, @Traversable@, etc. -}
class (Functor φ k k, Functor γ k k) ⇒ Distributes φ γ k where
  dist ∷ (Object k (φ (γ a)), Object k(γ (φ a)))
       ⇒ φ (γ a) `k` γ (φ a)




{- | In the category of categories, categories are objects and natural
transformations are morphisms; this type synonym roughly captures a natural
transformation between two categories. -}
type (p ∷ κ → κ → Type) :~> (q ∷ κ → κ → Type) =
  ∀ (a ∷ κ) (b ∷ κ).
    ( Object p a, Object p b
    , Object q a, Object q b
    ) ⇒ a `p` b → a `q` b

type (p ∷ κ → κ → Type) ::~> (q ∷ κ → κ → Type) =
  ∀ a b. a `p` b → a `q` b



{- | Categories form a category; instances of this typeclass are endofunctors in
that category. Together with 'Fix', this permits the definition of recursion
schemes over categories.

See

 - §9 of Yang & Wu, 2022.
   [/Fantastic morphisms and where to find them/](https://arxiv.org/abs/2202.13633).
 - Williams 2013, [/Fixing GADTs/](http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html).
 - Milewski 2018, [/Free Monoidal Profunctors/](https://bartoszmilewski.com/2018/02/20/free-monoidal-profunctors).

The looser constraints on the second term — and the lack (compare with
Milewski's @HFunctor@) of methods enforcing that the result forms a category —
are motivated by folds: the in-flight type created by folding morphisms of a
free category category into morphisms of another doesn't look to me like it has
a sensible category instance, but I suspect I simply haven't thought about it
enough. (An endofunctor in the category of categories by definition /ought/ to
always map a morphism in one category to a morphism in another.) -}
class HFunctor (η ∷ (κ → κ → Type) → κ → κ → Type) where

  {- | @hmap@ lifts a natural transformation into the endofunctor @η@. -}
  hfmap ∷ ∀ p q. (∀ x. Object p x ⇒ Object' q x)
        ⇒ (p :~> q) → η p ::~> η q


{- | The fixpoint of an endofunctor in the category of categories. -}
newtype Fix (η ∷ (κ → κ → Type) → κ → κ → Type) (a ∷ κ) (b ∷ κ) =
  In { out ∷ η (Fix η) a b }
  deriving stock Generic

deriving instance (Show      (η (Fix η) a b)) ⇒ Show      ((Fix η) a b)
deriving instance (Eq        (η (Fix η) a b)) ⇒ Eq        ((Fix η) a b)
deriving instance (Ord       (η (Fix η) a b)) ⇒ Ord       ((Fix η) a b)
deriving instance (Bounded   (η (Fix η) a b)) ⇒ Bounded   ((Fix η) a b)
deriving instance (Enum      (η (Fix η) a b)) ⇒ Enum      ((Fix η) a b)
deriving instance (F.Functor (η (Fix η) a  )) ⇒ F.Functor ((Fix η) a  )


instance (Semigroupoid (η (Fix η))) ⇒ Semigroupoid (Fix η) where
  type Object (Fix η) a = Object (η (Fix η)) a
  (In g) . (In f) = In $ g . f

instance (Category (η (Fix η))) ⇒ Category (Fix η) where
  id = In id

{- | A catamorphism in the category of categories. -}
cata ∷ ∀ η q a b.
     ( HFunctor η, (∀ x. Object (Fix η) x ⇒ Object' q x)
     )
     ⇒ η q ::~> q         -- ^ An algebra.
     → Fix η a b → q a b
cata alg = alg ∘ hfmap (cata alg) ∘ out


{- | An anamorphism in the category of categories. -}
ana ∷ ∀ η q a b.
    ( HFunctor η
    , (∀ x. Object q x ⇒ Object' (Fix η) x)
    )
    ⇒ q ::~> η q         -- ^ A coalgebra for /η q/.
    → q a b → Fix η a b
ana coalg = In ∘ hfmap (ana coalg) ∘ coalg


newtype K a x y = K { unK ∷ a }
  deriving stock (Show, Eq, Ord, Bounded, Generic, F.Functor, Foldable)
