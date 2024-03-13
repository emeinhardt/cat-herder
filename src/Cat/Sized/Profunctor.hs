{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Sized.Profunctor
  ( Profunctor (dimap)
  , Endo (Endo)
  , endo
  , unEndo
  , SizedPro (SizedPro, unSizedPro)
  , ProSG ((.))
  , ProCat
  , (⊛)
  , o
  -- , pmap -- TODO
  -- , opmap -- TODO
  -- , gopmap -- TODO
  , Dimap (Dimap)
  , pre
  , post
  , pre'
  , post'
  ) where

{- TODO
1. Newtype + instances to lift appropriate unsized profunctors analogous to
what @Sized@ does for lifting unsized semigroupoids/categories to sized ones.

2. pmap/opmap/gopmap

3. Procomposed
-}

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type)
import GHC.TypeNats
  ( KnownNat
  , Nat
  )

import Data.Constraint.Trivial
  ( Unconstrained2
  , Unconstrained4
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Data.Functor                 qualified as F

import Cat.Unsized.Semigroupoid     qualified as U
import Cat.Unsized.Category         qualified as U
import Cat.Unsized.Profunctor       qualified as U

import Cat.Sized.Functor            qualified as S

import Cat.Sized.Semigroupoid.Class qualified as S
import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 )
  , Sized (Sized, unSized)
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
             , join
             , split
             )
  )
import Cat.Sized.Semicartesian.Class
  ( Semicartesian
  , idx
  , ProjObject
  )
import Cat.Sized.Semicocartesian.Class
  ( Semicocartesian
  , inj
  , InjObject
  )


class (Category φ l, Category γ r)
  ⇒ Profunctor (φ ∷  Nat → κ  → κ )
               (l ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
               (γ ∷  Nat → κ' → κ')
               (r ∷ (Nat → κ' → κ') → Nat → Nat → κ' → κ' → Type)
               (p ∷ (Nat → κ  → κ )
                  → (Nat → κ' → κ')
                  →  Nat → Nat
                  →  κ   → κ'
                  →  Type
               ) where

  dimap ∷ ∀ n m s t i j a b.
        ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
        , Object φ l n s, Object φ l i a
        , Object γ r j b, Object γ r m t
        )
        ⇒ s -| l φ   n i |-> a  -- ^ A "preprocessing" morphism from @l@.
        → b -| r   γ j m |-> t  -- ^ A "postprocessing" morphism from @r@.
        → a -| p φ γ i j |-> b
        → s -| p φ γ n m |-> t


{- | A type that permits treating a wrapped morphism from
some category /k/ as an endoprofunctor.

Note that, per the types of 'endo', 'unEndo', and provided instances, the second
(co)product functor is expected to be the same as the first at use sites. -}
data Endo (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (φ ∷ Nat → κ → κ)
          (γ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)
  where
  Endo ∷ (Object φ k n a, Object φ k m b)
       ⇒ a -|       k  φ   n m |-> b       -- ^ The @k@-morphism to lift.
       → a -| (Endo k) φ γ n m |-> b


{- | Smart constructor for 'Endo'. -}
endo ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
     ( Object φ k n a
     , Object φ k m b
     )
     ⇒ a -|       k  φ   n m |-> b  -- ^ The lifted @k@-morphism.
     → a -| (Endo k) φ φ n m |-> b
endo = Endo


unEndo ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
       ( Object φ k n a
       , Object φ k m b
       )
       ⇒ a -| (Endo k) φ φ n m |-> b  -- ^ The lifted @k@-morphism.
       → a -|       k  φ   n m |-> b
unEndo (Endo f) = f

deriving instance (∀ i j x y. Show (x -| k φ i j |-> y)) ⇒ Show (a -| (Endo k) φ φ n m |-> b)
deriving instance (∀ i j x y. Eq   (x -| k φ i j |-> y)) ⇒ Eq   (a -| (Endo k) φ φ n m |-> b)
deriving instance (∀ i j x y. Ord  (x -| k φ i j |-> y)) ⇒ Ord  (a -| (Endo k) φ φ n m |-> b)

instance Semigroupoid φ k ⇒ Semigroupoid φ (Endo k φ) where
  type Object φ (Endo k φ) n a = Object φ k n a

  (Endo g) . (Endo f) = Endo (g S.⊙ f)

instance Category φ k ⇒ Category φ (Endo k φ) where
  id = Endo id

instance (Category φ k) ⇒ Profunctor φ k φ k (Endo k) where
  dimap pre_ post_ (Endo p) = Endo $ post_ S.⊙ p S.⊙ pre_



newtype SizedPro (k ∷ κ → κ' → Type)
                 (φ ∷ Nat → κ  → κ )
                 (γ ∷ Nat → κ' → κ')
                 (n ∷ Nat) (m ∷ Nat)
                 (a ∷ κ)   (b ∷ κ')
  = SizedPro { unSizedPro ∷ φ n a `k` γ m b }

deriving instance (                    F.Functor   (γ m), F.Functor   (k (φ n a))) ⇒ F.Functor  (SizedPro k φ γ n m a)
deriving instance ( Foldable    (φ n), Foldable    (γ m), Foldable    (k (φ n a))) ⇒ Foldable   (SizedPro k φ γ n m a)
deriving instance ( F.Functor   (φ n), F.Functor   (γ m), F.Functor   (k (φ n a))
                  , Foldable    (φ n), Foldable    (γ m), Foldable    (k (φ n a))
                  , Traversable (φ n), Traversable (γ m), Traversable (k (φ n a))) ⇒ Traversable (SizedPro k φ γ n m a)
deriving instance (∀ i j x y. Show (φ i x `k` γ j y)) ⇒ Show (SizedPro k φ γ n m a b)
deriving instance (∀ i j x y. Eq   (φ i x `k` γ j y)) ⇒ Eq   (SizedPro k φ γ n m a b)
deriving instance (∀ i j x y. Ord  (φ i x `k` γ j y)) ⇒ Ord  (SizedPro k φ γ n m a b)

instance (U.Semigroupoid p) ⇒ Semigroupoid φ (SizedPro p φ) where
  type Object φ (SizedPro p φ) n a = U.Object p (φ n a)
  (SizedPro g) . (SizedPro f) = SizedPro (g U.⊙ f)

instance (U.Category p) ⇒ Category φ (SizedPro p φ) where
  id = SizedPro U.id

instance ( U.Profunctor l r p
         , Category φ (Sized l)
         , Category γ (Sized r)
         , ∀ n o. Object φ (Sized l) n o ⇒ U.Object' l (φ n o)
         , ∀ n o. Object γ (Sized r) n o ⇒ U.Object' r (γ n o)
         )
  ⇒ Profunctor (φ ∷ Nat → κ  → κ ) (Sized (l ∷ κ  → κ  → Type))
               (γ ∷ Nat → κ' → κ') (Sized (r ∷ κ' → κ' → Type))
               (SizedPro (p ∷ κ → κ' → Type))
  where
  dimap (Sized (f ∷ φ i a `l` φ j x)) (Sized (h ∷ γ k y `r` γ l_ b)) (SizedPro (g ∷ φ j x `p` γ k y)) =
    SizedPro (U.dimap f h g)

instance (U.Category (->))
  ⇒ Profunctor φ (SizedPro (->) φ) φ (SizedPro (->) φ) (SizedPro (->)) where
  dimap (SizedPro f) (SizedPro h) (SizedPro g) = SizedPro $ h U.⊙ g U.⊙ f
-- instance (Category φ (Sized (->)))
--   ⇒ Profunctor φ (SizedPro (->) φ) φ (SizedPro (->) φ) (SizedPro (->)) where
--   dimap (SizedPro f) (SizedPro h) (SizedPro g) = SizedPro ∘ unSized $ Sized h S.⊙ Sized g S.⊙ Sized f



instance ( Monoidal φ (Sized (->))
         -- , ∀ n x. S.Object φ (SizedPro (->) φ) n x ⇒ S.Object' φ (Sized (->)) n x
         -- , S.Object φ (SizedPro (->) φ) n x ~ Unconstrained4 φ (SizedPro (->) φ) n x
         -- , S.Object φ (SizedPro (->) φ) n x ~ Unconstrained2 (->) x
         )
  ⇒ Monoidal φ (SizedPro (->) φ) where

 (SizedPro f) *** (SizedPro g) = SizedPro ∘ unSized $ Sized f *** Sized g
 ith fn (SizedPro f) = SizedPro ∘ unSized $ ith fn (Sized f)
 join = SizedPro ∘ unSized $ join
 split = SizedPro ∘ unSized $ split

instance (Semicartesian φ (Sized (->)))
  ⇒ Semicartesian φ (SizedPro (->) φ) where
  type ProjObject φ (SizedPro (->) φ) n a = ProjObject φ (Sized (->)) n a
  idx = SizedPro ∘ unSized ∘ idx

instance (Semicocartesian φ (Sized (->)))
  ⇒ Semicocartesian φ (SizedPro (->) φ) where
  type InjObject φ (SizedPro (->) φ) n a = InjObject φ (Sized (->)) n a
  inj = SizedPro ∘ unSized ∘ inj



{- | The main purpose of this typeclass is to allow for ergonomic composition of
(co)product-to-(co)product morphisms in a category /p/ that has both monoidal
products and (in general distinct) coproducts.

I'm not convinced yet this typeclass is necessary or desirable for that purpose,
but have so far not managed to make an analogue of
[@Data.Profunctor@'s @procomposed@](https://ncatlab.org/nlab/show/profunctor#the_bicategory_of_profunctors)
that typechecks. -}
class ( -- Profunctor φ (p φ) φ (p φ) p
      --   Category φ (p φ)
      -- , Category γ (p γ)
      -- , Category η (p η)
      --   Profunctor φ l γ m p
      -- , Profunctor γ m η r p
      ) ⇒ ProSG
  (φ ∷  Nat → κ  → κ )
  (l ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
  (γ ∷  Nat → κ  → κ )
  (m ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
  (η ∷  Nat → κ  → κ )
  (r ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
  (p ∷ (Nat → κ  → κ )
     → (Nat → κ  → κ )
     →  Nat → Nat
     →  κ   → κ
     →  Type
  )
  where
  (.) ∷ ∀ i j k x y z.
      ( Profunctor φ l γ m p
      , Profunctor γ m η r p
      , KnownNat i
      , KnownNat j
      , KnownNat k
      , Object φ l i x
      , Object γ m j y
      , Object η r k z
      )
      ⇒ y -| p γ η j k |-> z  -- ^ A profunctor arrow from /γ j y/ to /η k z/.
      → x -| p φ γ i j |-> y  -- ^ A profunctor arrow from /φ i x/ to /γ j y/.
      → x -| p φ η i k |-> z

class ( ProSG φ l γ m η r p
      , Category φ (p φ)
      , Category γ (p γ)
      , Category η (p η)
      ) ⇒ ProCat φ l γ m η r p

o ∷ ∀ κ
    (φ ∷  Nat → κ  → κ )
    (l ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (γ ∷  Nat → κ  → κ )
    (m ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (η ∷  Nat → κ  → κ )
    (r ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (p ∷ (Nat → κ  → κ )
       → (Nat → κ  → κ )
       →  Nat → Nat
       →  κ   → κ
       →  Type)
    (i ∷ Nat) (j ∷ Nat) (k ∷ Nat)
    (x ∷ κ)   (y ∷ κ)   (z ∷ κ).
    (
      KnownNat i, KnownNat j, KnownNat k
    , Object φ l i x, Object γ m j y, Object η r k z
    , Profunctor φ l γ m p
    , Profunctor γ m η r p
    , ProSG φ l γ m η r p
    )
    ⇒ y -| p γ η j k |-> z  -- ^ A morphism from @φ l x@ to @φ m b@.
    → x -| p φ γ i j |-> y  -- ^ A morphism from @φ n a@ to @φ l x@.
    → x -| p φ η i k |-> z  -- ^ A morphism from @φ n a@ to @φ m b@.
o = (.) @κ @φ @l @γ @m @η @r


infixr 9 ⊛
(⊛) ∷ ∀ κ
    (φ ∷  Nat → κ  → κ )
    (l ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (γ ∷  Nat → κ  → κ )
    (m ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (η ∷  Nat → κ  → κ )
    (r ∷ (Nat → κ  → κ ) → Nat → Nat → κ  → κ  → Type)
    (p ∷ (Nat → κ  → κ )
       → (Nat → κ  → κ )
       →  Nat → Nat
       →  κ   → κ
       →  Type)
    (i ∷ Nat) (j ∷ Nat) (k ∷ Nat)
    (x ∷ κ)   (y ∷ κ)   (z ∷ κ).
    (
      KnownNat i, KnownNat j, KnownNat k
    , Object φ l i x, Object γ m j y, Object η r k z
    , Profunctor φ l γ m p
    , Profunctor γ m η r p
    , ProSG φ l γ m η r p
    )
    ⇒ y -| p γ η j k |-> z  -- ^ A morphism from @φ l x@ to @φ m b@.
    → x -| p φ γ i j |-> y  -- ^ A morphism from @φ n a@ to @φ l x@.
    → x -| p φ η i k |-> z  -- ^ A morphism from @φ n a@ to @φ m b@.
(⊛) = (.) @κ @φ @l @γ @m @η @r


instance ( -- ProSG φ (p φ) γ (p γ) η (p η) p
           Category φ (p φ)
         )
         ⇒ ProSG φ (p φ) φ (p φ) φ (p φ) p where
  (.) = (S.⊙)

{- | Allows compositions of profunctor arrows from /φ/ to /φ/ with profunctor
arrows from /φ/ to /γ/. -}
instance ( Category (φ ∷ Nat → κ → κ) (p φ)
         , Category (γ ∷ Nat → κ → κ) (p γ)
         , Profunctor φ (p φ) γ (p γ) p
         )
         ⇒ ProSG φ (p φ) φ (p φ) γ (p γ) p where
  (g ∷ y -| p φ γ j k |-> z) . (f ∷ x -| p φ φ i j |-> y) =
    dimap f (id @κ @γ @(p γ)) g

{- | Allows compositions of profunctor arrows from /γ/ to /φ/ with profunctor
arrows from /φ/ to /φ/. -}
instance ( Category (φ ∷ Nat → κ → κ) (p φ)
         , Category (γ ∷ Nat → κ → κ) (p γ)
         , Profunctor γ (p γ) φ (p φ) p
         )
         ⇒ ProSG γ (p γ) φ (p φ) φ (p φ) p where
  (g ∷ y -| p φ φ j k |-> z) . (f ∷ x -| p γ φ i j |-> y) =
    dimap (id @κ @γ @(p γ)) g f



-- TODO finish
-- pmap ∷ ∀ κ (η ∷ κ → κ) (φ ∷ Nat → κ → κ) (γ ∷ Nat → κ → κ) (p ∷ (Nat → κ → κ) → (Nat → κ → κ) → Nat → Nat → κ → κ → Type) n m a b.
--      ( S.Functor η φ φ (p φ) (p φ)
--      , S.Functor η γ γ (p γ) (p γ)
--      , Profunctor φ (p φ) γ (p γ) p
--      )
--      ⇒   a -| p φ γ n m |->   b
--      → η a -| p φ γ n m |-> η b
-- pmap f = undefined


-- TODO finish
-- opmap ∷ ∀ κ l (φ ∷ Nat → κ → κ) (γ ∷ Nat → κ → κ) (p ∷ (Nat → κ → κ) → (Nat → κ → κ) → Nat → Nat → κ → κ → Type) n m a b.
--      ( S.Functor (φ l) φ φ (p φ) (p φ)
--      , S.Functor (γ l) γ γ (p γ) (p γ)
--      , Profunctor φ (p φ) γ (p γ) p
--      )
--      ⇒     a -| p φ γ n m |->     b
--      → φ n a -| p φ γ l l |-> γ m b
-- opmap = undefined




-- TODO shelve Procomposed in a branch

-- TODO It's probably desirable to make m γ j a existential for composability
-- {- | A morphism in
-- [/Prof/](https://ncatlab.org/nlab/show/profunctor#the_bicategory_of_profunctors). -}
-- data Procompose --m     -- Intermediate category common to profuntors p, q
--                 l     -- Source monoidal category (with (co)product functor φ)
--                 r     -- Target category
--                 p     -- Profunctor from φ l to γ m
--                 q     -- Profunctor from γ m to η r
--                 -- γ     -- Intermediate functor
--                 -- j     -- Intermediate object size
--                 -- a     -- Intermediate object
--                 φ η   -- Source, target (co)product functors
--                 i k   -- Size of source, target (co)product objects
--                 s t   -- Source, target (co)product objects
--   where
--   Procompose ∷ ( -- KnownNat i
--                  -- KnownNat j --
--                -- , KnownNat k
--                -- , Category φ l
--                -- , Category γ m --
--                -- , Category η r
--                -- , Profunctor φ l γ m p --
--                -- , Profunctor γ m η r q --
--                -- , Object φ l i s       -- The source (co)product in l is φ i s
--                -- , Object γ m j a       -- The intermediate (co)product in m is γ j a --
--                -- , Object η r k t       -- The target (co)product in r is η k t
--                )
--                ⇒ a -| q γ η j k |-> t  -- ^ Profunctor from /γ j a/ to /η k t/.
--                → s -| p φ γ i j |-> a  -- ^ Profunctor from /φ i s/ to /γ j a/.
--                → s -| Procompose l r p q φ η i k |-> t
--                -- → s -| Procompose m l r p q γ j a φ η i k |-> t

-- -- deriving instance ( ∀ x y. Show (x -| q γ η j k |-> y)
-- --                   , ∀ x y. Show (x -| p φ γ i j |-> y)
-- --                   )
-- --   ⇒ Show (s -| Procompose l r p q φ η i k |-> t)
-- --   -- ⇒ Show (s -| Procompose m l r p q γ j a φ η i k |-> t)

-- instance ( Category φ (l ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--          , Category η (r ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--          )
--   ⇒ Profunctor φ l η r (Procompose l r p q) where
--   -- ⇒ Profunctor φ l η r (Procompose (m ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) l r p q γ j a) where
--   dimap (pre_ ∷ s' -| l φ i' i |-> s)
--         (post_ ∷ t -| r η k k' |-> t')
--         (Procompose g f) =
--     Procompose (dimap @κ @κ             id   post_ g)
--                (dimap @κ @κ @φ @l       pre_ id    f)
--     -- Procompose (dimap @κ @κ @γ @m @η @r id   post_ g)
--     --            (dimap @κ @κ @φ @l @γ @m pre_ id    f)
--     -- Procompose (dimap @κ @κ @γ @m @η @r @q @j  @k' @a  @t' @j @k @a @t id  post_ g)
--     --            (dimap @κ @κ @φ @l @γ @m @p @i' @j  @s' @a  @i @j @s @a pre_ id   f)

-- procomposed ∷ ∀ l r p φ η i k s t.
-- -- procomposed ∷ ∀ m l r p γ j a φ η i k s t.
--   ( Category φ (p φ) -- a -| (p φ) φ j k |-> t ∘ s -| (p φ) φ i j |-> a
--   -- , Category γ (p γ) -- a -| (p γ) γ j k |-> t ∘ s -| (p γ) γ i j |-> a
--   , Category η (p η) -- a -| (p η) η j k |-> t ∘ s -| (p η) η i j |-> a
--   -- , Profunctor φ (p φ) γ (p γ) p
--   -- , Profunctor γ (p γ) η (p η) p
--   , Object φ (p φ) i s
--   -- , Object γ (p γ) j a
--   , Object η (p η) k t
--   -- , ∀ z. Object m z ⇒ Object' p z
--   )
--   ⇒ s -| Procompose l r p p φ η i k |-> t
--   -- ⇒ s -| Procompose m l r p p γ j a φ η i k |-> t
--   → s -| p φ η i k |-> t
-- procomposed (Procompose (g ∷ a -| p γ η j k |-> t) (f ∷ s -| p φ γ i j |-> a)) = undefined


-- TODO Consider removing this
data Dimap m     -- Intermediate category common to profuntors p, q
           l     -- Source monoidal category (with (co)product functor φ)
           r     -- Target category
           p     -- Profunctor from φ l to γ m
           q     -- Profunctor from γ m to η r
           γ     -- Intermediate functor
           k l'  -- Intermediate object sizes
           a b   -- Intermediate objects
           φ η   -- Source, target (co)product functors
           i j   -- Size of source, target (co)product objects
           s t   -- Source, target (co)product objects
  where
  Dimap ∷ ( KnownNat i
          , KnownNat j
          , KnownNat k
          , KnownNat l'
          , Category φ l, Category γ m, Category η r
          , Profunctor φ l γ m p
          , Profunctor γ m η r q
          , Object φ l i  s       -- Source (co)product in l
          , Object γ m k  a       -- Intermediate (co)product #1 in m
          , Object γ m l' b       -- Intermediate (co)product #2 in m
          , Object η r j  t       -- Target (co)product in r
          )
          ⇒ b -| q γ η l' j |-> t  -- ^ Profunctor from /γ l' b/ to /η j t/.
          → s -| p φ γ i  k |-> a  -- ^ Profunctor from /φ i  s/ to /γ k a/.
          → s -| Dimap m l r p q γ k l' a b φ η i j |-> t

deriving instance ( ∀ k' j' σ β. Show (σ -| q γ η k' j' |-> β)
                  , ∀ i' k' α τ. Show (α -| p φ γ i' k' |-> τ)
                  )
                  ⇒ Show (s -| Dimap m l r p q γ k l' a b φ η i j |-> t)


-- instance (Profunctor φ l γ m p, Profunctor γ m η r q)
--   ⇒ Profunctor φ l η r (Dimap φ l γ m η r) where
  -- ⇒ Profunctor φ l η r (Dimap φ l γ m η r p q) where

--   dimap (pre ∷ w `l` a) (post ∷ b `r` y) (Dimap (q ∷ x `q` b) (p ∷ a `p` x)) =
--     Dimap (dimap (id  ∷ x `m` x) (post ∷ b `r` y) q ∷ x `q` y)
--                (dimap (pre ∷ w `l` a) (id   ∷ x `m` x) p ∷ w `p` x)


pre ∷ ∀ m l r p q γ k l' φ η i j a b s t.
    s -| Dimap m l r p q γ k l' a b φ η i j |-> t
  → s -| p φ γ i k |-> a
pre (Dimap _ p) = p

post ∷ ∀ m l r p q γ k l' φ η i j a b s t.
    s -| Dimap m l r p q γ k l' a b φ η i j |-> t
  → b -| q γ η l' j |-> t
post (Dimap q _) = q

pre' ∷ ∀ m l r p q γ k l' φ η i j a b s t a' s'.
  ( Object φ l i s'
  , Object γ m k a'
  )
  ⇒ ( s  -| p φ γ i k |-> a
    → s' -| p φ γ i k |-> a'
    )
  → s  -| Dimap m l r p q γ k l' a  b φ η i j |-> t
  → s' -| Dimap m l r p q γ k l' a' b φ η i j |-> t
pre' τ (Dimap q p) = Dimap q (τ p)

post' ∷ ∀ m l r p q γ k l' φ η i j a b s t b' t'.
  ( Object γ m l' b'
  , Object η r j  t'
  )
  ⇒ ( b  -| q γ η l' j |-> t
    → b' -| q γ η l' j |-> t'
    )
  → s -| Dimap m l r p q γ k l' a b  φ η i j |-> t
  → s -| Dimap m l r p q γ k l' a b' φ η i j |-> t'
post' τ (Dimap q p) = Dimap (τ q) p
