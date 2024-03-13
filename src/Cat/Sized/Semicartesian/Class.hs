{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- |

module Cat.Sized.Semicartesian.Class
  ( -- * Indexing (projection of) a single value
    Semicartesian ( ProjObject
                  , idx
                  )
  , index
  , π
  , ProjObject'
  , idxRep
  , FinRep (FinRep, unFinRep)
  , idxs
  , idxs'

    -- * Removal of a single value
  , HasTerminal (terminal)

  , Delete ( DelObject
           , del
           )
  , DelObject'

    -- * Selecting a contiguous range ("slice") of values
  , Select ( SelectObject
           , sel
           )
  , SelectObject'
  , unfork

    -- * Sequence combinators
  , head
  , tail
  , last
  , init
  , prefix
  , suffix
  , take
  , drop
  ) where

{- | TODO Variants of the sequence combinators that take proxies for length parameter

Cleanup after further testing (e.g. unfork).
-}


import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , head
  , tail
  , last
  , init
  , take
  , drop
  )
import Prelude.Unicode ((∘))
import Data.Composition ((.:))

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained4
  , Unconstrained5
  )

import GHC.TypeNats
  ( KnownNat
  , Nat
  , natVal
  -- , SNat
  , pattern SNat
  , type (+)
  , type (-)
  , type (<=)
  -- , type (*)
  -- , withKnownNat
  -- , withSomeSNat
  )
import Data.Finite
  ( Finite
  , natToFinite
  )
-- import Data.Proxy qualified as P
-- import Data.Proxy (Proxy (Proxy))

import Data.Functor.Rep qualified as R
import Data.Functor.Rep
  ( Representable
  , Rep
  , tabulate
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )


import Cat.Sized.Functor
  ( Functor -- (fmap)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ((.))
  , Object'
  , Sized (Sized)
  )
import Cat.Sized.Category.Class
  ( Category (id)
  , Object
  , Sub (Sub)
  , (⊙)
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , Unit
             , (***)
             , mul
             , ith
             , ith'
             , sing
             , unsing
             , join
             , split
             , assoc
             , lift1
             , bisplit
             , bijoin
             , biassoc
             )
  , omap
  )



import Cat.Sized.Category.Instances ()
import Cat.Sized.Monoidal.Instances ()



{- | A semicartesian monoidal category has projections from its products, i.e. the
ability to "index" into a product/destroy objects.

Note that the only ("only") thing prohibiting you from trying to project a value
out of a product with 0 elements is that @Finite 0@ is uninhabited. I suspect
this is enough type safety and that adding a @1 <= n@ constraint to @inj@ would
only risk making type inference more difficult. -}
class (Monoidal φ k)
  ⇒ Semicartesian (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constraints on whether an object /a/ can be projected from a
   /φ/-structure of length /n/. -}
  type ProjObject φ k (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type ProjObject φ k n a = Unconstrained4 φ k n a

  {- | The /ith/ projection from an /n/-ary product. -}
  idx ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      -- , 1 <= n
      , Object φ k n a
      , Object φ k 1 a
      , ProjObject φ k n a
      )
      ⇒ Finite n            -- ^ The index to project out of an /n/-product.
      → a -| k φ n 1 |-> a


{- | Synonym for 'idx' — perhaps clearer, but likely to lead to namespace clashes.  -}
index ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
        (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , Object φ k n a
     , Object φ k 1 a
     , ProjObject φ k n a
     , Semicartesian φ k
     )
     ⇒ Finite n            -- ^ The index to project out of an /n/-product.
     → a -| k φ n 1 |-> a
index = idx


{- | Synonym for 'idx'. -}
π ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
        (n ∷ Nat) (a ∷ κ).
  ( KnownNat n
  , Object φ k n a
  , Object φ k 1 a
  , ProjObject φ k n a
  , Semicartesian φ k
  )
  ⇒ Finite n            -- ^ The index to project out of an /n/-product.
  → a -| k φ n 1 |-> a
π = idx


{- | This is a "class synonym" for the type family 'ProjObject'; it's often needed to
write quantified constraints. -}
class    (ProjObject φ k n a)
  ⇒ ProjObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (ProjObject φ k n a)
  ⇒ ProjObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)


-- TODO @limbo-test
{- | This newtype provides a derivation for @Semicartesian φ (Sized (->))@ for any
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
functor @(φ n)@ where @Rep (φ n) ~ Finite n@. -}
newtype FinRep (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (φ ∷  Nat → κ → κ)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ)
  = FinRep { unFinRep ∷ a -| k φ n m |-> b }

instance Semigroupoid φ k
  ⇒ Semigroupoid (φ ∷ Nat → Type → Type) (FinRep (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type))
  where
  type Object φ (FinRep k) n a = Object φ k n a
  -- type Object φ (FinRep k) n a = (Object φ k n a, Representable (φ n), Rep (φ n) ~ Finite n)
  (FinRep g) . (FinRep f) = FinRep (g . f)

instance ( Semigroupoid φ (FinRep k)
         , Category φ k
         , ∀ m x. (Object' φ (FinRep k) m x) ⇒ Object' φ k m x
         -- , ∀ m x. (Object' φ (FinRep k) m x, Representable (φ m), Rep (φ m) ~ Finite m) ⇒ Object' φ k m x
         ) ⇒ Category φ (FinRep k) where
  id = FinRep id

instance ( Category φ (FinRep k)
         , ∀ m x. (Object' φ (FinRep k) m x) ⇒ Object' φ k m x
         -- , ∀ m x. (Object' φ (FinRep k) m x, Representable (φ m), Rep (φ m) ~ Finite m) ⇒ Object' φ k m x
         , Monoidal φ k
         )
  ⇒ Monoidal φ (FinRep k) where
  type Proxy φ (FinRep k) = Proxy φ k

  (FinRep f) *** (FinRep g) = FinRep $ f *** g

  mul pn pm pn' pm' (FinRep f) (FinRep g) = FinRep $ mul pn pm pn' pm' f g

  ith     fn (FinRep f) = FinRep $ ith     fn f
  ith' pn fn (FinRep f) = FinRep $ ith' pn fn f

  sing     = FinRep   sing
  unsing   = FinRep   unsing
  join     = FinRep   join
  split    = FinRep   split
  assoc    = FinRep   assoc
  lift1    = FinRep ∘ lift1   ∘ unFinRep
  bisplit  = FinRep ∘ bisplit ∘ unFinRep
  bijoin   = FinRep ∘ bijoin  ∘ unFinRep
  biassoc  = FinRep ∘ biassoc ∘ unFinRep

instance
  ( Monoidal φ (FinRep k)
  , k ~ Sized (->)
  )
  ⇒ Semicartesian (φ ∷ Nat → Type → Type) (FinRep (k ∷ (Nat → Type → Type) → Nat → Nat → Type → Type → Type))
  where
    type ProjObject φ (FinRep k) n a = (Representable (φ 1), Representable (φ n), Rep (φ n) ~ Finite n)
    idx (fn ∷ Finite n) = FinRep ∘ Sized $ tabulate ∘ const ∘ flip R.index fn


{- | This is a generic implementation for 'index' in @Sized (->)@ in terms of
'index' for any sized functor /φ/ with suitable
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instances.

This may be easier to use (require less cajoling of GHC) than 'FinRep'. -}
idxRep ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (a ∷ Type).
      ( -- KnownNat n
        Representable (φ n)
      , Representable (φ 1)
      -- , Integral (Rep (φ n))
      -- , Integral (Rep (φ 1))
      )
      ⇒ Rep (φ n)            -- ^ The index to project out of an /n/-product.
      -- ⇒ Finite n            -- ^ The index to project out of an /n/-product.
      → (φ n a → φ 1 a)
idxRep = tabulate ∘ const .: flip R.index



{- | @idxs \@κ \@l i@ lifts @idx \@κ i@ from a projection for the /i/th element of
/n/ to a morphism that gets the /ith/ element from each /n/-product in an
/l/-product of /n/-products.

>>> idxs n = omap $ idx n
-}
idxs ∷ ∀ κ (l ∷ Nat) (φ ∷ Nat → κ → κ) k (n ∷ Nat) (a ∷ κ).
     ( Functor (φ l) φ φ k k
     , Semicartesian φ k
     , KnownNat l, KnownNat n
     , ProjObject φ k n a
     , Object φ k n a
     , Object φ k 1 a
     , Object φ k 1 (φ n a)
     , Object φ k 1 (φ 1 a)
     , Object φ k 1 (φ l (φ n a))
     , Object φ k 1 (φ l (φ 1 a))
     , Object φ k l (φ n a)
     , Object φ k l (φ 1 a)
     )
     ⇒ Finite n
     → φ n a -| k φ l l |-> φ 1 a  -- ^ @idx@ lifted to act on an /l/-product of /n/-products.
idxs = omap @l @φ @k
     ∘ idx @κ


{- | Variant of 'idxs'.

>>> idxs' n = join ⊙ idxs n
-}
idxs' ∷ ∀ κ (l ∷ Nat) (φ ∷ Nat → κ → κ) k (n ∷ Nat) (a ∷ κ).
      ( Functor (φ l) φ φ k k
      , Semicartesian φ k
      , KnownNat l, KnownNat n
      , ProjObject φ k n a
      , Object φ k n a
      , Object φ k 1 a
      , Object φ k 1 (φ n a)
      , Object φ k 1 (φ 1 a)
      , Object φ k 1 (φ l (φ n a))
      , Object φ k 1 (φ l (φ 1 a))
      , Object φ k l (φ n a)
      , Object φ k l (φ 1 a)
      , Object φ k l a
      )
      ⇒ Finite n
      → φ n a -| k φ l l |-> a  -- ^ @idx@ lifted to act on an /l/-product of /n/-products.
idxs' n = join
        ⊙ idxs n



-- TODO Given a ("representable"?) cartesian category C with all finite
-- products, what is the analogue of C's terminal object in the setting of
-- concategories, PROPs, or polycategories? Is it (always?) going to be
-- (isomorphic to) @φ 0 x@? @φ 1 u@ where @u@ (in many-sorted contexts) is the
-- terminal object of C?

-- TODO Modulo the issue above, 'terminal' *probably* be part of 'Semicartesian'
-- as long as 'Unit' is an associated type synonym of 'Monoidal' and you don't
-- have much infrastructure in place for a parallel semigroupoid-esque typeclass
-- hierarchy.
{- | This typeclass reflects the expected form of a terminal morphism for
Cartesian categories and related constructions. -}
class (Monoidal φ k)
  ⇒ HasTerminal (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  where

  terminal ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
           ( KnownNat n
           , Object φ k n a
           , Object φ k m b
           , Unit φ k n a ~ φ m b
           , Unit φ k n b ~ φ m b
           )
           ⇒ a -| k φ n m |-> b



{- | Variation on 'HasTerminal' and 'Semicartesian' whose defining method throws
away a selected index of a product and keeps everything else. -}
class (Monoidal φ k)
  ⇒ Delete (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constraints on whether an object /a/ can be struck from a
   /φ/-structure of length /n/. -}
  type DelObject φ k (n ∷ Nat) (a ∷ κ)  ∷ Constraint
  type DelObject φ k n a = Unconstrained4 φ k n a

  {- | Delete an element from an /n/-ary product. -}
  del ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , 1 <= n
      , Object φ k  n      a
      , Object φ k (n - 1) a
      , DelObject φ k n a
      )
      ⇒ Finite n                  -- ^ The index to remove from an /n/-product.
      → a -| k φ n (n - 1) |-> a


{- | This is a "class synonym" for the type family 'DelObject'; it's often needed to
write quantified constraints. -}
class    (DelObject φ k n a)
  ⇒ DelObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)
instance (DelObject φ k n a)
  ⇒ DelObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ)



{- | A variation on 'Semicartesian' whose defining method selects a sequence of
contiguous indices of a product and throws away everything else to either side. -}
class (Monoidal φ k)
  ⇒ Select (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constraints on whether the /l/ contiguous objects of /a/ starting from
  any position /0/ through /i/ (for /i ≤ n - l/) can be projected from a
  /φ/-structure of length /n/. -}
  type SelectObject φ k (l ∷ Nat) (n ∷ Nat) (a ∷ κ) ∷ Constraint
  type SelectObject φ k l n a = Unconstrained5 φ k l n a

  {- | Select a length /l/ sequence of contiguous objects from an /n/-product. -}
  sel ∷ ∀ (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
      ( KnownNat l, KnownNat n
      , l <= n
      , Object φ k n a
      , Object φ k l a
      , SelectObject φ k l n a
      )
      ⇒ Finite ((n - l) + 1)   -- ^ The starting index of the length /l/ "slice".
      → a -| k φ n l |-> a


{- | This is a "class synonym" for the type family 'SelectObject'; it's often needed to
write quantified constraints. -}
class    (SelectObject φ k l n a)
  ⇒ SelectObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (l ∷ Nat) (n ∷ Nat) (a ∷ κ)
instance (SelectObject φ k l n a)
  ⇒ SelectObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (l ∷ Nat) (n ∷ Nat) (a ∷ κ)


{- | The inverse of @curry (&&&)@. -}
unfork ∷ ∀ κ (φ ∷ Nat → κ → κ)
       (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
       (l ∷ Nat) (n ∷ Nat) (m ∷ Nat)
       (a ∷ κ)   (b ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat l
       , Object φ k  l      a
       , Object φ k (n + m) b
       , Object φ k  n      b
       , Object φ k      m  b
       , Select φ k
       , SelectObject φ k n (n + m) b
       , SelectObject φ k m (n + m) b
       )
       ⇒   a -| k φ l (n + m) |-> b   -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.
       → ( a -| k φ l  n      |-> b
         , a -| k φ l      m  |-> b
         )
-- a b c d e  length 5, maxIdx = 5-1 = 4
-- 0 1 2 3 4
-- unfork from n+m=5 to n=2,m=3:
-- slice of length 2 from (2 + 3) starting at 0 where the range of possible indices for slices of length 2 is [0,1,2,3], which has length 4=((5 - 2) + 1); the Finite value must be a Finite (n+m - n + 1 = m+1) = Finite 4
-- slice of length 3 from (2 + 3) starting at 2 where the range of possible indices for slices of length 3 is [0,1,2], which has length 3=((5 - 3) + 1); the Finite value must be a Finite (n+m - m + 1 = n+1) = Finite 3
--
--             slice of length n from n + m...starting at 0 with length (((n+m) - n) = m)
-- unfork h = ( (slice @κ @φ @k @n @(n + m)) (natToFinite @0 @(((n + m) - n) + 1) (SNat @0)) . h
--            , (slice @κ @φ @k @m @(n + m)) (natToFinite @n @(((n + m) - m) + 1) (SNat @n)) . h
--            )
-- unfork h = ( (slice @κ @φ @k @n @(n + m)) (natToFinite @0 @(      m       + 1) (SNat @0)) . h
--            , (slice @κ @φ @k @m @(n + m)) (natToFinite @n @(  n           + 1) (SNat @n)) . h
--            )
unfork h = ( (sel @κ @φ @k @n @(n + m)) (natToFinite @0 @(m + 1) (SNat @0)) ⊙ h
           , (sel @κ @φ @k @m @(n + m)) (natToFinite @n @(n + 1) (SNat @n)) ⊙ h
           )


{- | Select the prefix of length /l/ from an /n/-ary product. -}
prefix ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
     ( KnownNat l, KnownNat n
     , l <= n
     , Object φ k n a
     , Object φ k l a
     , SelectObject φ k l n a
     , Select φ k
     )
     ⇒ a -| k φ n l |-> a
prefix = sel 0


{- | Select the suffix of length /l/ from an /n/-ary product. -}
suffix ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
     ( KnownNat l, KnownNat n
     , l <= n
     , Object φ k n a
     , Object φ k l a
     , SelectObject φ k l n a
     , Select φ k
     )
     ⇒ a -| k φ n l |-> a
suffix =
  let n' = natVal (SNat @n)
      l' = natVal (SNat @l)
      i  = fromIntegral (n' - l')
  in sel i


{- | Retrieve the first element of the source product: synonym for @idx 0@. -}
head ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , Object φ k n a
     , Object φ k 1 a
     , ProjObject φ k n a
     , Semicartesian φ k
     )
     ⇒ a -| k φ n 1 |-> a
head = idx 0


{- | Retrieve the last element of the source product. -}
last ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , Object φ k n a
     , Object φ k 1 a
     , ProjObject φ k n a
     , Semicartesian φ k
     )
     ⇒ a -| k φ n 1 |-> a
last = idx (fromIntegral $ (natVal (SNat @n) - 1))


{- | Retrieve all but the first element of the source product. -}
tail ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , 1 <= n
     , Object φ k  n      a
     , Object φ k (n - 1) a
     , SelectObject φ k (n - 1) n a
     , Select φ k
     )
     ⇒ a -| k φ n (n - 1) |-> a
tail = suffix @κ @φ @k @(n - 1)


{- | Retrieve all but the last element of the source product. -}
init ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (n ∷ Nat) (a ∷ κ).
     ( KnownNat n
     , 1 <= n
     , Object φ k n a
     , Object φ k (n - 1) a
     , SelectObject φ k (n - 1) n a
     , Select φ k
     )
     ⇒ a -| k φ n (n - 1) |-> a
init = prefix @κ @φ @k @(n - 1)


{- | Take the first @l@ elements of the source product. Synonym for 'prefix'. -}
take ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
     ( KnownNat l, KnownNat n
     , l <= n
     , Object φ k n a
     , Object φ k l a
     , SelectObject φ k l n a
     , Select φ k
     )
     ⇒ a -| k φ n l |-> a
take = sel 0

{- | Drop the first @l@ elements of the source product. -}
drop ∷ ∀ κ
     (φ ∷ Nat → κ → κ)
     (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
     (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
     ( KnownNat l, KnownNat n
     , l <= n
     , Object φ k  n      a
     , Object φ k (n - l) a
     , SelectObject φ k (n - l) n a
     , Select φ k
     )
     ⇒ a -| k φ n (n - l) |-> a
drop = sel $ fromIntegral $ natVal (SNat @l)


instance (Semicartesian φ k) ⇒ Semicartesian φ (o `Sub` k) where
  type ProjObject φ (o `Sub` k) n a = ProjObject φ k n a
  idx = Sub ∘ idx

instance (HasTerminal φ k, Unit φ k m x ~ Unit φ (o `Sub` k) m x) ⇒ HasTerminal φ (o `Sub` k) where
  terminal = Sub terminal

instance (Delete φ k) ⇒ Delete φ (o `Sub` k) where
  type DelObject φ (o `Sub` k) n a = DelObject φ k n a
  del = Sub ∘ del

instance (Select φ k) ⇒ Select φ (o `Sub` k) where
  type SelectObject φ (o `Sub` k) l n a = SelectObject φ k l n a
  sel = Sub ∘ sel
