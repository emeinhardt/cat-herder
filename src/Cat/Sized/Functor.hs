{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Functor
  ( Functor  ( fmap )
  , NatTrans ( hoist
             , comp
             )
  , Distributes (dist)

    -- * Recursion schemes
  , NT
  , NT'
  , HFunctor ( HFunctorObj
             , hfmap
             )
  , Fix (In, out)
  , cata
  , ana
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial (Unconstrained4)
import GHC.TypeNats
  ( KnownNat
  , Nat
  )

import GHC.Generics (Generic)
import Data.Functor qualified as F

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Object'
  )
import Cat.Sized.Category.Class
  ( Category
  , id
  )



{- | A size-preserving functor from one "sized" category to another. -}
class ( Category φ r, Category γ t
      ) ⇒ Functor (η ∷        κ  → κ')  -- ^ The (outermost-)size-preserving functor from @r@ to @t@.
                  (φ ∷  Nat → κ  → κ )  -- ^ The monoidal product associated with the source category @r@.
                  (γ ∷  Nat → κ' → κ')  -- ^ The monoidal product associated with the target categort @t@.
                  (r ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
                  (t ∷ (Nat → κ' → κ') → Nat → Nat → κ' → κ' → Type)
  where
  fmap ∷ ∀ (n ∷ Nat) (m ∷ Nat)
           (a ∷ κ)   (b ∷ κ).
       ( KnownNat n, KnownNat m
       , Object φ r n a, Object γ t n (η a)
       , Object φ r m b, Object γ t m (η b)
       )
       ⇒   a -| r φ n m |->   b  -- ^ The source morphism from @r@.
       → η a -| t γ n m |-> η b  -- ^ The resulting morphism in @t@.



{- | A natural transformation from one (outermost-)size-preserving functor to another. -}
class ( Category φ r, Category γ t
      -- , Functor η φ γ r t, Functor ι φ γ r t
      )
      ⇒ NatTrans
          (η ∷        κ  → κ')  -- ^ The source size-preserving functor from @r@ to @t@.
          (ι ∷        κ  → κ')  -- ^ The target size-preserving functor from @r@ to @t@.
          (φ ∷  Nat → κ  → κ )  -- ^ The monoidal product associated with the source category @r@.
          (γ ∷  Nat → κ' → κ')  -- ^ The monoidal product associated with the target category @t@.
          (r ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
          (t ∷ (Nat → κ' → κ') → Nat → Nat → κ' → κ' → Type)
  where

  {- | Note that when the additional constraints @Object γ t m (ι b)@ and
  @Functor η φ γ r t@ hold, a default definition is available in terms of
  @comp@ and @fmap@:

  >>> hoist f ≝ comp @κ @κ' @η @ι @φ @γ @r @t . fmap f
  -}
  hoist ∷ ∀ (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , Object φ r n    a , Object φ r m    b
        , Object γ t n (η a), Object γ t m (ι b)
        )
        ⇒   a -| r φ n m |->   b  -- ^ The source morphism in @r@ from @a@ to @b@.
        → η a -| t γ n m |-> ι b  -- ^ The resulting morphism in @t@ taking @η a@ to @ι b@.

  default hoist ∷ ∀ (n ∷ Nat) (m ∷ Nat)
                    (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , Object φ r n    a , Object φ r m    b
        , Object γ t n (η a), Object γ t m (η b)
        ,                     Object γ t m (ι b)  -- NOTE This and @Functor η φ γ r t@ are the added requirements.
        , Functor η φ γ r t
        )
        ⇒   a -| r φ n m |->   b  -- ^ The source morphism in @r@ from @a@ to @b@.
        → η a -| t γ n m |-> ι b  -- ^ The resulting morphism in @t@ taking @η a@ to @ι b@.
  hoist f = comp @κ @κ' @η @ι @φ @γ @r @t . fmap f

  {- | Note that when the additional constraints @Object φ r n a@ holds, a default
  definition is available in terms of @hoist@:

  >>> comp ≝ hoist (id @κ @φ @r)
  -}
  comp ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object γ t n (η a)
       , Object γ t n (ι a)
       )
       ⇒ η a -| t γ n n |-> ι a  -- ^ The @a@-component of the natural transformation.

  default comp ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object γ t n (η a)
       , Object γ t n (ι a)
       , Object φ r n    a   -- NOTE This is the extra constraint required for this default definition.
       )
       ⇒ η a -| t γ n n |-> ι a  -- ^ The @a@-component of the natural transformation.
  comp = hoist (id @κ @φ @r)




{- | This typeclass currently exists specifically for the context of bikleisli
arrows. No thought has yet been given to its interaction with e.g.
@Distributive@, @Traversable@, etc. -}
class (Functor γ φ φ k k, Functor η φ φ k k) ⇒ Distributes γ η φ k where
  dist ∷ (Object φ k n (γ (η a)), Object φ k n (γ (η a)))
       ⇒ γ (η a) -| k φ n n |-> η (γ a)




{- | In the category of monoidal categories with product /φ/, categories are
objects and natural transformations are morphisms; this type synonym roughly
captures a natural transformation between two such categories. -}
type NT φ p q =
  ∀ n m a b.
    ( Object φ p n a, Object φ p m b
    , Object φ q n a, Object φ q m b
    )
  ⇒ a -| p φ n m |-> b
  → a -| q φ n m |-> b

type NT' φ p q =
  ∀ n m a b.
    a -| p φ n m |-> b
  → a -| q φ n m |-> b



{- | Monoidal categories with product /φ/ form a category; instances of this
typeclass are endofunctors in that category. Together with 'Fix', this permits
the definition of recursion schemes over these categories. -}
class HFunctor (η ∷ ((Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                  →  (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constriants that must hold for use of an instance /η/. -}
  type HFunctorObj η (φ ∷  Nat → κ → κ)
                     (p ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                     (q ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                   ∷ Constraint
  type HFunctorObj η φ p q = Unconstrained4 η φ p q

  {- | @hmap@ lifts a natural transformation into the endofunctor @η@. -}
  hfmap ∷ ∀ φ p q. (
                   --   (∀ x. Object p x ⇒ Object' (η p) x)
                   -- , (∀ x. Object q x ⇒ Object' (η q) x)
                     ∀ i x. Object φ p i x ⇒ Object' φ q i x
                   -- , ∀ x. Object (η p) x ⇒ Object' (η q) x
                   , HFunctorObj η φ p q
                   -- , ∀ i x. HFunctorObj η φ p q i x
                   )
        ⇒ NT φ p q → NT' φ (η p) (η q)
        -- ⇒ (p :~> q) → NatL (η p) (η q)
        -- ⇒ (p :~> q) → NatR (η p) (η q)
        -- ⇒ (p :~> q) → (η p :~> η q) -- restore
  -- hfmap ∷ ∀ p q. (p :~> q) → (η p :~> η q)
  -- hfmap ∷ ∀ p q. (p -| Nat ? |-> q) → (η p -| Nat ? |-> η q)


{- | The fixpoint of an endofunctor in the category of monoidal categories with product /φ/. -}
newtype Fix (η ∷ ((Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               →  (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (φ ∷ Nat → κ → κ)
            (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ) =
  In { out ∷ η (Fix η) φ n m a b }
  deriving stock Generic

deriving instance (Show      (η (Fix η) φ n m a b)) ⇒ Show      ((Fix η) φ n m a b)
deriving instance (Eq        (η (Fix η) φ n m a b)) ⇒ Eq        ((Fix η) φ n m a b)
deriving instance (Ord       (η (Fix η) φ n m a b)) ⇒ Ord       ((Fix η) φ n m a b)
deriving instance (Bounded   (η (Fix η) φ n m a b)) ⇒ Bounded   ((Fix η) φ n m a b)
deriving instance (Enum      (η (Fix η) φ n m a b)) ⇒ Enum      ((Fix η) φ n m a b)
deriving instance (F.Functor (η (Fix η) φ n m a  )) ⇒ F.Functor ((Fix η) φ n m a  )


instance (Semigroupoid φ (η (Fix η))) ⇒ Semigroupoid φ (Fix η) where
  type Object φ (Fix η) n a = Object φ (η (Fix η)) n a
  (In g) . (In f) = In $ g . f


instance (Category φ (η (Fix η))) ⇒ Category φ (Fix η) where
  id = In id


{- | A catamorphism in the category of categories. -}
cata ∷ ∀ φ η q n m a b.
     ( HFunctor η
     -- , Object φ (Fix η) n a
     -- , Object φ (Fix η) m b
     , (∀ i x. Object φ (Fix η) i x ⇒ Object' φ q i x)
     , HFunctorObj η φ (Fix η) q
     )
     ⇒ NT' φ (η q) q        -- ^ An algebra for /q/.
     → Fix η φ n m a b → q φ n m a b
cata alg = alg
         ∘ hfmap (cata alg)
         ∘ out


{- | An anamorphism in the category of categories. -}
ana ∷ ∀ φ η q n m a b.
    ( HFunctor η
    -- , Object φ q n a, Object φ q m b
    , (∀ i x. Object φ q i x ⇒ Object' φ (Fix η) i x)
    -- , (∀ x. Object q x ⇒ Object' (η q)   x)
    , HFunctorObj η φ q (Fix η)
    )
    ⇒ NT' φ q (η q)        -- ^ A coalgebra for /η q/.

    -- -- ⇒ q ::~> η q
    -- -- ⇒ NatL q (η q)
    -- -- ⇒ (q :~> η q)

    → q φ n m a b → Fix η φ n m a b
ana coalg = In ∘ hfmap (ana coalg) ∘ coalg
