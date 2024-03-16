{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Cat.Unsized.Profunctor
  ( Profunctor (dimap)
  , Endo (Endo)
  , unEndo

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
