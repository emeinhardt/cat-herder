{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Profunctor
  ( Profunctor (dimap)
  , Endo (Endo)
  , unEndo

  , Dimap (Dimap)
  , pre
  , post
  , pre'
  , post'
  , procomposed

  --   -- * Recursion schemes
  -- , (:~>)
  -- , HPFunctor ( hpmap
  --             , hdimap
  --             )
  -- , Fix ( In
  --       , out
  --       )
  -- , cata
  -- , ana
  ) where

{- TODO

 - Work out appropriate constraints for recursion schmes: see Cat.Unsized.Functor
-}

import Prelude hiding
  ( (.)
  , id
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid
  , Object
  , (.)
  -- , Object'
  )
import Cat.Unsized.Category.Class
  ( Category
  , id
  )
-- import Cat.Unsized.Category.Instances ()



class (Category l, Category r)
  ⇒ Profunctor (l ∷ κ  → κ  → Type)
               (r ∷ κ' → κ' → Type)
               (p ∷ κ  → κ' → Type) where

  dimap ∷ ∀ s t a b.
        ( Object l s, Object l a
        , Object r b, Object r t
        )
        ⇒ s `l` a  -- ^ A "preprocessing" morphism from @l@.
        → b `r` t  -- ^ A "postprocessing" morphism from @r@.
        → a `p` b
        → s `p` t

instance (Category (->)) ⇒ Profunctor (->) (->) (->) where
  dimap f h g = h . g . f

{- | A type that permits treating a wrapped morphism from
some category /k/ as an endoprofunctor.

== Example

Pretending that @(->) (->) (->)@ didn't already have a Profunctor instance...

>>> import Cat.Sized.Category.Instances ()
>>> post = (+ ( 3 ∷ Int))
>>> pre  = (* ( 2 ∷ Int))
>>> f    = (* (-1 ∷ Int))
>>> unEndo (dimap pre post $ Endo f) $ 4  -- For ergonomics, note that only @f@ needs to be wrapped.
-5
-}
data Endo (k ∷ κ → κ → Type) (a ∷ κ) (b ∷ κ) where
  Endo ∷ (Object k a, Object k b)
       ⇒ a -|      k |-> b -- ^ The @k@-morphism to lift.
       → a -| Endo k |-> b

unEndo ∷ ∀ k a b.
         a -| Endo k |-> b  -- ^ The lifted @k@-morphism.
       → a -| k      |-> b
unEndo (Endo f) = f

deriving instance (∀ x y. Show (x `k` y)) ⇒ Show (a -| Endo k |-> b)
deriving instance (∀ x y. Eq   (x `k` y)) ⇒ Eq   (a -| Endo k |-> b)
deriving instance (∀ x y. Ord  (x `k` y)) ⇒ Ord  (a -| Endo k |-> b)

instance Semigroupoid k ⇒ Semigroupoid (Endo k) where
  type Object (Endo k) a = Object k a

  (Endo g) . (Endo f) = Endo (g . f)

instance Category k ⇒ Category (Endo k) where
  id = Endo id

-- TODO Of the three ways below of allowinga category to be a profunctor into
-- and out of itself, which is better with respect to
--
--  - possible type inference issues
--  - avoiding overlapping instances
--  - ergonomics (probably number/locations of @coerce@ calls)?
--
--  instance (Category k) ⇒ Profunctor (Endo k) (Endo k) k
--
--  instance (Category k) ⇒ Profunctor (Endo k) (Endo k) (Endo k)
--
--  instance (Category k) ⇒ Profunctor k k (Endo k)
--
-- E.g. I suspect that (Profunctor k k (Endo k)) is the most ergonomic:
--
-- >>> f = undefined ∷ x → y
-- >>> pre = undefined ∷ a → x
-- >>> post = undefined ∷ y → b
-- >>> f' = over Endo (dimap pre post) f

instance (Category k) ⇒ Profunctor k k (Endo k) where
  dimap pre_ post_ (Endo p) = Endo $ post_ . p . pre_




-- TODO Consider removing this
-- TODO Any other constraints besides @Object m x@ that a downstream user may
-- want to propagate through a 'Dimap' plausibly won't.
{- |

>>> import Cat.Sized.Category.Instances ()
>>> preI = (* (2 ∷ Int))
>>> postI = (+ (3 ∷ Int))
>>> postPreI = Dimap @(->) @(->) @(->) postI preI
>>> procomposed postPreI $ 4  -- ((2 * 4) + 3)
11
>>> f = (+ (0 ∷ Int))
>>> preO = (* (-1 ∷ Int))
>>> postO = (+ (10 ∷ Int))
>>> postPreOI = dimap preO postO postPreI
>>> procomposed postPreOI $ 4  -- (((-1 * (2 * 4)) + 3) + 10)
5
-}
data Dimap (m ∷ κ₁ → κ₁ → Type)
           (l ∷ κ₀ → κ₀ → Type)
           (r ∷ κ₂ → κ₂ → Type)
           (p ∷ κ₀ → κ₁ → Type)
           (q ∷ κ₁ → κ₂ → Type)
           (a ∷ κ₁) (b ∷ κ₁)
           (s ∷ κ₀) (t ∷ κ₂)
           -- (x ∷ κ₁) (y ∷ κ₁)
           -- (a ∷ κ₀) (b ∷ κ₂)
  where
  Dimap ∷ ∀ l m r p q a b s t.
        ( -- Category l, Category m, Category r
        -- , Profunctor l m p -- Is this constraint useful/harmful?
        -- , Profunctor m r q -- Is this constraint useful/harmful?
          Object m a
        , Object m b
        -- , Object l a -- Is this constraint useful/harmful?
        -- , Object r b -- Is this constraint useful/harmful?
        )
        ⇒ b `q` t
        → s `p` a
        → s -| Dimap m l r p q a b |-> t

deriving instance (∀ β τ. Show (β `q` τ), ∀ σ α. Show (σ `p` α)) ⇒ Show (s -| Dimap m l r p q a b |-> t)
-- deriving instance (∀ u v. Show (u `q` v), ∀ t u. Show (t `p` u)) ⇒ Show (a -| Dimap l m r p q |-> b)

pre ∷ ∀ m l r p q a b s t.
    s -| Dimap m l r p q a b |-> t
  → s `p` a
pre (Dimap _ p) = p

post ∷ ∀ m l r p q a b s t.
    s -| Dimap m l r p q a b |-> t
  → b `q` t
post (Dimap q _) = q

pre' ∷ ∀ m l r p q a b s t a' s'.
  ( Object m a'
  )
  ⇒ (s `p` a → s' `p` a')
  → s  -| Dimap m l r p q a  b |-> t
  → s' -| Dimap m l r p q a' b |-> t
pre' τ (Dimap q p) = Dimap q (τ p)

post' ∷ ∀ m l r p q a b s t b' t'.
  ( Object m b'
  )
  ⇒ (b `q` t → b' `q` t')
  → s -| Dimap m l r p q a b  |-> t
  → s -| Dimap m l r p q a b' |-> t'
post' τ (Dimap q p) = Dimap (τ q) p

procomposed ∷ ∀ m l r p a s t.
  ( Category p
  , Object p s
  , Object p t
  , Object p a
  -- , ∀ z. Object m z ⇒ Object' p z
  )
  ⇒ s -| Dimap m l r p p a a |-> t
  → s `p` t
procomposed (Dimap g f) = g . f

dimapped ∷ ∀ κ
  (l ∷ κ → κ → Type) (m ∷ κ → κ → Type) (r ∷ κ → κ → Type)
  (p ∷ κ → κ → Type)
  a b s t.
    ( Category p
    , Object m a
    , Object m b
    , Object p s
    , Object p t
    , Object p a
    , Object p b -- right, left', right'
    -- , Category m
    -- , Category l
    -- , Category r
    , Object l s -- right
    , Object l a -- right'
    , Object r t -- left
    , Object r b -- left'
    , Profunctor l m p -- right
    , Profunctor m r p -- left, left'
    )
  ⇒ s -| Dimap m l r p p a b |-> t
  → a `m` b
  → s `p` t
-- dimapped (Dimap h f) g = dimap @κ @κ @m @r g id h . f
-- dimapped (Dimap h f) g = h . dimap @κ @κ @l id g f
-- dimapped (Dimap h f) g = h . dimap g (id @κ @r) (id @κ @p) . f
dimapped (Dimap h f) g = h . dimap (id @κ @l) g (id @κ @p) . f

instance (Profunctor l m p, Profunctor m r q)
  ⇒ Profunctor
  (l ∷ κ₀ → κ₀ → Type)
  (r ∷ κ₂ → κ₂ → Type)
  (Dimap (m ∷ κ₁ → κ₁ → Type) l r p q x y)
  where

  dimap (pre_ ∷ s₀ `l` s₁) (post_ ∷ t₁ `r` t₀) (Dimap (q ∷ b `q` t₁) (p ∷ s₁ `p` a)) =
    Dimap (dimap (id   ∷ b  `m` b ) (post_ ∷ t₁ `r` t₀) q ∷ b  `q` t₀)
               (dimap (pre_ ∷ s₀ `l` s₁) (id    ∷ a  `m` a ) p ∷ s₀ `p` a )

-- instance (Profunctor l m p, Profunctor m r q)
--   ⇒ Profunctor l r (Dimap l m r p q) where

--   dimap (pre ∷ w `l` a) (post ∷ b `r` y) (Dimap (q ∷ x `q` b) (p ∷ a `p` x)) =
--     Dimap (dimap (id  ∷ x `m` x) (post ∷ b `r` y) q ∷ x `q` y)
--                (dimap (pre ∷ w `l` a) (id   ∷ x `m` x) p ∷ w `p` x)


-- TODO work out appropriate constraints: see Cat.Unsized.Functor

{- | In the category of profunctors, profunctors are objects and natural
transformations are morphisms; this type synonym roughly captures a natural
transformation between two profunctors. -}
type (p ∷ κ → κ' → Type) :~> (q ∷ κ → κ' → Type) =
  ∀ (a ∷ κ) (b ∷ κ'). a `p` b → a `q` b


{- | Profunctors form a category; instances of this typeclass are endofunctors in
that category. Together with 'Fix', this permits the definition of recursion
schemes over profunctors.

See
[Milewski, 2018. *Free monoidal profunctors*](https://bartoszmilewski.com/2018/02/20/free-monoidal-profunctors)
for discussion somewhat specialized to endoprofunctors on @(->)@. -}
class HPFunctor (η ∷ (κ → κ' → Type) → κ → κ' → Type) where

  {- | @hpmap@ lifts a natural transformation from the profunctor @p@ to the
  profunctor @q@. -}
  hpmap ∷ (p :~> q) → (η p :~> η q)

  {- | @hdimap@ shows that the result of the mapping defined by @η@ is also a
  profunctor. -}
  -- hdimap ∷ (Category l, Category r, Object l s, Object l a, Object r b, Object r t)
  --        ⇒ (s `l` a) → (b `r` t) → η p a b → η p s t
  hdimap ∷ (s `l` a) → (b `r` t) → η p a b → η p s t

{- | The fixpoint of an endofunctor in the category of profunctors. -}
newtype Fix (η ∷ (κ → κ' → Type) → κ → κ' → Type) (a ∷ κ) (b ∷ κ') =
  In { out ∷ η (Fix η) a b }

instance (Category l, Category r, HPFunctor η) ⇒ Profunctor l r (Fix η) where
  dimap pre_ post_ (In η) = In (hdimap pre_ post_ η)


{- | A catamorphism in the category of profunctors. -}
cata ∷ HPFunctor η ⇒ (η q :~> q) → Fix η a b → q a b
cata alg = alg ∘ hpmap (cata alg) ∘ out


{- | An anamorphism in the category of profunctors. -}
ana ∷ HPFunctor η ⇒ (q :~> η q) → q a b → Fix η a b
ana coalg = In ∘ hpmap (ana coalg) ∘ coalg
