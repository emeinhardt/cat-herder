{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- see comments on takeA, dropA
{- |

Because constraints and kind annotations make Haddock difficult to read, the
instances exported by this module are summarized below:

== Generic instances for any @Monoidal φ k@

- Lift any @a -| k φ n m |-> b@ to @φ 1 a -| k φ n m | φ 1 b@ via @Solo@ and
  @lift1@ through either @Unsized.fmap@ (when @m ~n@) or @Sized.fmap@.

- Lift any @a -| k φ (i * n) (i * n) |-> b@ to @φ i a -| k φ n n | φ i b@ via
  @Factor@ and @bisplit@ through @Unsized.fmap@.


== Generic instances for @Sized k@

These instances will plausibly be moved elsewhere or subsumed by more general
functors.

- Lift any /un/sized morphism @a \`k\` b@ to a morphism
  @φ n a -| (Sized k) φ 1 1 |-> φ n b@ when @Monoidal φ (Sized k)@ holds through
  @Unsized.fmap@.

    - Compose with @bijoin@ to lift an unsized /k/-arrow @a \`k\` b@ to
      @a -| (Sized k) φ n n |-> b@.

- For any @φ@ such that @φ i@ is always @Applicative@ and @Traversable@, lift
  an @a -| (Sized (->)) φ n m |-> b@ arrow to a
  @φ l a -| (Sized (->)) φ n m |-> φ l b@ arrow trhough @Unsized.fmap@ (when
  @m ~ n@) or @Sized.fmap@.

- For any @φ@ such that @Monoidal φ (Sized (->))@ and such that @φ i@ is always
  @Applicative@ and @Traversable@, and for any @l@ such that @φ l@ is a sized
  endofunctor on morphisms in @Sized (->)@, there is both a
  @MonoidalEndo (φ l) φ (Sized (->))@ instance and an
  @OpMonoidalEndo (φ l) φ (Sized (->))@.

    - Because specialized @zip@ and @zipWith@ instances are expected, an
      instance is not provided, but if for some reason you don't have or don't want
      to use specialized instances, @instance Zip φ k@ should be enough, provided
      the appropriate default object constraints hold.


== Concrete instances for @Sized (->)@

These instances will plausibly be moved elsewhere.

 - @Monoidal Data.Vector.Sized.Vector (Sized (->))@
 - @Monoidal Cat.Sized.Monoida.Data.R1 (Sized (->))@
 - @Zip Data.Vector.Sized.Vector (Sized (->))@
 - @Zip Cat.Sized.Monoida.Data.R1 (Sized (->))@

-}

-- TODO cleanup after testing

module Cat.Sized.Monoidal.Instances
 (
 ) where

import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zip
  , zipWith
  , traverse
  , sequence
  , Monad
  , return
  )

-- Module convention: use (∘) for composition in Hask, use (⊙) for "sized"
-- semigroupoid composition
import Prelude.Unicode ((∘))
-- import Control.Arrow.Unicode ((⁂))

import Data.Kind (Type)

-- import Data.Data (Proxy(Proxy))
import GHC.TypeNats
  ( KnownNat
  , Nat
  -- , SNat
  -- , pattern SNat
  -- , type (+)
  -- , type (-)
  -- , type (<=)
  , type (*)
  -- , natVal
  )
import Data.Finite
  ( Finite
  -- , getFinite
  )

-- import Control.Arrow qualified as CA
import Data.Functor  qualified as F
import Control.Monad qualified as M

-- import Data.Maybe (fromJust)
-- import Algebra.Graph.Label
--   ( Semiring ( one
--              , (<.>)
--              )
--   , zero
--   , (<+>)
--   )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Category.Class   qualified as U
import Cat.Unsized.Functor          qualified as U

import Cat.Sized.Functor            qualified as S
-- import Cat.Sized.Monad              qualified as S
-- import Cat.Sized.Monad
--   ( Monad ( return
--           , bind
--           )
--   )
import Cat.VectorSized
  ( parV
  , ithV
  , singV
  , unsingV
  , joinV
  , splitV
  , zipWithV
  )
import Cat.Orthotope
  ( R1 ( R1, unR1 )
  -- , diagA
  , diagR1

  , parA
  -- , unParA
  -- , takeA
  -- , dropA
  -- , ithA
  , ithA'
  -- , splitA
  , splitR1
  -- , joinA
  , joinR1

  -- , Sr2 (Sr2, unSr2)
  -- , sr2
  -- , mulSr2
  -- , idSr2
  -- , eye
  -- , idxSr2
  -- , sumSr2
  -- , ithSr2
  -- , selSr2
  -- , dupSr2
  -- , padSr2
  )

-- import Cat.Sized.Semigroupoid.Internal qualified as I
import Cat.Sized.Semigroupoid.Internal
  ( ISemigroupoid (IObject)
  , IObject'
  , (⋄)
  , One (One, unOne)
  )
import Cat.Sized.Semigroupoid.Class
  ( -- Semigroupoid ( Object
    --              , (.)
    --              )
  -- , Object'
    (⊙)
  )
import Cat.Sized.Category.Class
  ( -- Category
    id
  )
import Cat.Sized.Category.Instances ()
import Cat.Sized.Category.Class
  ( Sized ( Sized )
  , unSized
  )

import Cat.Sized.Monoidal.Class
  ( Monoidal ( -- Proxy
               (***)
             , ith
             , assoc
             , split
             , join
             , unsing
             , sing
             , lift1
             -- , bising
             , bisplit
             , bijoin
             -- , biassoc
             )
  , Solo   (Solo, unSolo)
  , Factor
  -- , omap
  -- , gmap
  )


import Cat.Sized.Functor.Monoidal
  ( MonoidalEndo (splat)
  , OpMonoidalEndo (unsplat)
  , Zip (zip, zipWith)
  , TraversableEndo ( sequence
                    -- , traverse
                    -- , consume
                    )
  , DistributiveEndo ( distribute
                     -- , collect
                     )
  )
import Cat.Sized.Functor
  ( Functor (fmap)
  )

-- import Data.Vector       qualified as V
import Data.Vector.Sized qualified as VS
-- import Data.Array.Shaped qualified as A
-- import Data.Array.Shaped (Array)



-- If (Category φ k) and (Monoidal φ k) and (KnownNat l), then Functor (φ l) φ φ k k

-- instance (KnownNat l, Category φ k)
-- -- instance (KnownNat l, Monoidal φ k)
--   ⇒ Functor (φ l) φ φ k k where
--   fmap (f ∷ a -| k φ n m |-> b) = -- RHS ∷ (φ l a -| k φ n m |-> φ l b)
--     undefined

-- instance ( KnownNat l
--          , Category φ (Sized (->))
--          , Applicative (φ l)
--          )
--   ⇒ Functor (φ l) φ φ (Sized (->)) (Sized (->)) where
--   fmap (f ∷ a -| (Sized (->)) φ n m |-> b) = -- RHS ∷ (φ l a -| k φ n m |-> φ l b)
--     -- undefined
--     let f' ∷ φ n a → φ m b
--         f' = unSized f
--         f_ ∷ φ n (φ l a) →
--     in  undefined

{-
  φ l a -| k φ  n       m      |-> φ l b
= {- dimap split join -}
      a -| k φ (n * l) (m * l) |->     b
-}



-- Lift @a -| k φ n m |-> b@ to @φ 1 a -| k φ n m |-> φ 1 b@

-- Unclear to me if this may plausibly lead to overlapping instance issues, so
-- it's commented out in favor of @Solo@ for now
-- -- | We can always introduce one level of "nesting" to an existing @(φ z x)@ to get @(φ 1 (φ z x))@.
-- instance ( Monoidal φ k )
--   ⇒ Functor (φ 1) (φ ∷ Nat → κ → κ) φ (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) k where
--   fmap ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
--         ( KnownNat n, KnownNat m
--         , Object φ k n a, Object φ k n (φ 1 a)
--         , Object φ k m b, Object φ k m (φ 1 b)
--         )
--         ⇒     a -| k φ n m |->     b   -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
--         → φ 1 a -| k φ n m |-> φ 1 b   -- ^ The same morphism with a trival extra layer of nesting at each end.
--   fmap f = (split @κ @φ @k @m @1 @b)  -- Type applications are not necessary,
--           ⊙ f                          -- but are left as a form of
--           ⊙ (join @κ @φ @k @n @1 @a)   -- documentation.


{- | Lift any @a -| k φ n m |-> b@ to @φ 1 a -| k φ n m | φ 1 b@ via @Solo@. -}
instance (Monoidal φ k) ⇒ S.Functor (φ 1) φ φ (Solo k) (Solo k) where
  fmap = Solo ∘ lift1 ∘ unSolo

-- TODO cleanup after testing
-- There's already an instance
-- deriving newtype instance
--   ( KnownNat n
--   , S.Semigroupoid φ k
--   , U.Category (k φ n n)
--   -- , U.Semigroupoid (Solo k φ n n)
--   )
--   ⇒ U.Category (Solo k φ n n)


{- | Lift any @a -| k φ n n |-> b@ to @φ 1 a -| k φ n n | φ 1 b@ via @Solo@. -}
instance ( Monoidal φ k
         -- , U.Category (Solo k φ n n)
         , KnownNat n
         -- , ∀ x. U.Object' (Solo k φ n n) x ⇒ S.Object' φ k n x
         )
-- instance (Monoidal φ k, U.Category (Solo k φ n n), KnownNat n, ∀ x. Object φ k n x ⇒ S.Object' φ k n (φ 1 x))
  ⇒ U.Functor (φ 1) (Solo k φ n n) (Solo k φ n n) where
  fmap = Solo ∘ lift1 ∘ unSolo



-- Lift @a -| k φ (i * n) (i * n) |-> b@ to @φ i a -| k φ n n |-> φ i b@


{- | Lift any @a -| k φ (i * n) (i * n) |-> b@ to @φ i a -| k φ n n | φ i b@ via
@Factor@. -}
instance ( Monoidal φ k
         , KnownNat n, KnownNat i, KnownNat m
         , m ~ i * n
         )
         ⇒ U.Functor (φ i) (Factor k φ m m) (Factor k φ n n) where
  fmap = bisplit




{- | Lift any /un/sized morphism @a \`k\` b@ to a morphism
@φ n a -| (Sized k) φ 1 1 |-> φ n b@ when @Sized k@ and @φ@ define a monoidal
category.

Compose with @bijoin@ to lift an unsized /k/-arrow

> a `k` b

to

> a -| (Sized k) φ n n |-> b
-}
instance ( KnownNat n
         , U.Category k
         , U.Functor (φ n) k k
         , ∀ x. U.Object k x ⇒ U.Object' k (φ n x)
         , Monoidal φ (Sized k)
         )
         ⇒ U.Functor (φ n) k (Sized k φ 1 1) where
  fmap = bisplit ∘ Sized ∘ U.fmap


{- | For any @φ@ such that @φ i@ is always @Applicative@ and @Traversable@, lift
an @a -| (Sized (->)) φ n n |-> b@ arrow to a
@φ m a -| (Sized (->)) φ n n |-> φ m b@ arrow.  -}
instance ( KnownNat n, KnownNat m
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         )
         ⇒ U.Functor (φ m) ((Sized (->)) φ n n) ((Sized (->)) φ n n) where
  fmap (Sized f) = Sized (sequenceA ∘ F.fmap f ∘ sequenceA)

{- | For any @φ@ such that @φ i@ is always @Applicative@ and @Traversable@, lift
an @a -| (Sized (->)) φ n m |-> b@ arrow to a
@φ l a -| (Sized (->)) φ n m |-> φ l b@ arrow.  -}
instance ( KnownNat l
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         )
         ⇒ S.Functor (φ l) φ φ (Sized (->)) (Sized (->)) where
  fmap (Sized f) = Sized (sequenceA ∘ F.fmap f ∘ sequenceA)

instance ( KnownNat l
         , Functor (φ l) φ φ (Sized (->)) (Sized (->))
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         , Monoidal φ (Sized (->))
         )
  ⇒ MonoidalEndo (φ l) φ (Sized (->)) where
  splat ∷ ∀ n a. (KnownNat n) ⇒ φ l a -| (Sized (->)) φ n 1 |-> φ l (φ n a)
  splat = sing
        ⊙ Sized ( sequenceA
                ∘ ( F.fmap @(φ n)
                  $ F.fmap @(φ l)
                    P.id
                  )
                )


instance ( KnownNat l
         , Functor (φ l) φ φ (Sized (->)) (Sized (->))
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         , Monoidal φ (Sized (->))
         )
  ⇒ OpMonoidalEndo (φ l) φ (Sized (->)) where
  unsplat ∷ ∀ n a. (KnownNat n) ⇒ φ l (φ n a) -| (Sized (->)) φ 1 n |-> φ l a
  unsplat = ( Sized
            $ sequenceA
            ∘ ( F.fmap @(φ l)
              $ F.fmap @(φ n)
                P.id
              )
            )
          ⊙ unsing

{- | Every @Applicative@, @Traversable@ sized product functor for @->@ with a
@MonoidalEndo@ instance for @->@ is a @TraversableEndo@.

>>> sequence ≝ bijoin $ fmap $ splat ⊙ unsing
-}
instance ( KnownNat l
         , Monoidal φ (Sized (->))
         , Functor (φ l) φ φ (Sized (->)) (Sized (->))
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         , MonoidalEndo (φ l) φ (Sized (->))
         )
  ⇒ TraversableEndo (φ l) φ (Sized (->)) where
  sequence ∷ ∀ η n a.
           ( KnownNat n
           , MonoidalEndo η φ (Sized (->))
           -- φ l    a  -| (Sized (->)) φ n l |-> φ n         a
           -- η      a  -| (Sized (->)) φ n 1 |-> η   (φ n    a)   -- MonoidalEndo η
           -- η      a  -| (Sized (->)) φ l 1 |-> η   (φ l    a)   -- MonoidalEndo η
           -- φ l (η a) -| (Sized (->)) φ 1 1 |-> η   (φ l    a)   -- MonoidalEndo η, push in outer source layer
           -- φ n (φ l (η a)) -| (Sized (->)) φ 1 1 |-> φ n (η   (φ l    a))   -- MonoidalEndo η, push in outer source layer
           -- (φ l (η a)) -| (Sized (->)) φ n n |-> (η   (φ l    a))   -- MonoidalEndo η, push in outer source layer
           -- φ l    a  -| (Sized (->)) φ n 1 |-> φ l (φ n    a)   -- MonoidalEndo (φ l)
           -- φ l (η a) -| (Sized (->)) φ n 1 |-> φ l (φ n (η a))  -- sub (η a) into sequence from MonoidalEndo φ l — but how do I make a morphism like this?
           -- φ l (η a) -| (Sized (->)) φ n 1 |-> φ l (η (φ n a))  -- fmap @(φ l) $ sequence @η
           -- φ l (η a) -| (Sized (->)) φ n l |-> (η (φ n a))      -- unsing ⊙ (fmap @(φ l) $ sequence @η)
           -- φ l (η a) -| (Sized (->)) φ n 1 |-> (η (φ l (φ n a))) -- sequence @η ⊙ unsing ⊙ (fmap @(φ l) $ sequence @η)
           )
           ⇒ φ l (η a) -| (Sized (->)) φ n n |-> η (φ l a)
  sequence = bijoin
           $ fmap
           $ splat @Type @η @φ @(Sized (->))  -- ∷ η a -| (Sized (->)) φ l 1 |-> η (φ l a)
           ⊙ unsing                           -- ∷ φ l (η a) -| k φ 1 l |-> η a
    -- let step0 ∷ η a -| (Sized (->)) φ l 1 |-> η (φ l a)
    --     step0 = splat
    --     step1 ∷ φ l (η a) -| Sized (->) φ 1 1 |-> η (φ l a)
    --     step1 = step0 ⊙ unsing
    --     step2 ∷ φ n (φ l (η a)) -| Sized (->) φ 1 1 |-> φ n (η (φ l a))
    --     step2 = fmap step1
    --     step3 ∷ φ l (η a) -| Sized (->) φ n n |-> η (φ l a)
    --     step3 = bijoin step2
    --     -- step2 ∷ φ l (η a) -| Sized (->) φ n n |-> η (φ l a)
    --     -- step2 = omap step2
    -- in  step3
  -- sequence = Sized $ F.fmap @(φ n) (sequenceA @(φ l) @η)


{- | Every @Applicative@, @Traversable@ sized product functor for @->@ with a
@MonoidalEndo@ instance for @->@ is a @DistributiveEndo@.

>>> distribute ≝ split ⊙ fmap (id ⊙ join)
-}
instance ( KnownNat l
         , Monoidal φ (Sized (->))
         , Functor (φ l) φ φ (Sized (->)) (Sized (->))
         , ∀ i. KnownNat i ⇒ Applicative (φ i)
         , ∀ i. KnownNat i ⇒ Traversable (φ i)
         , MonoidalEndo (φ l) φ (Sized (->))
         )
  ⇒ DistributiveEndo (φ l) φ (Sized (->)) where

  distribute ∷ ∀ η (n ∷ Nat) a.
           ( KnownNat n
           , Functor η φ φ (Sized (->)) (Sized (->))
           )
           ⇒ η (φ l a) -| (Sized (->)) φ n n |-> φ l (η a)
          --        a  -| (Sized (->)) φ (n * l) (n * l) |-> a
          --   (φ l a) -| (Sized (->)) φ n (n * l) |->   a
          -- η (φ l a) -| (Sized (->)) φ n (n * l) |-> η a
  distribute = split
             ⊙ fmap ( id
                    ⊙ join @Type @φ @(Sized (->))
                    )
  -- distribute =
  --   let idNL ∷ a -| (Sized (->)) φ (n * l) (n * l) |-> a
  --       idNL = id
  --       step1 ∷ φ l a -| (Sized (->)) φ n (n * l) |-> a
  --       step1 = idNL ⊙ join
  --       step2 ∷ η (φ l a) -| (Sized (->)) φ n (n * l) |-> η a
  --       step2 = fmap step1
  --       -- step2 = fmap @Type @Type @η step1
  --       step3 ∷ η (φ l a) -| (Sized (->)) φ n n |-> φ l (η a)
  --       step3 = split ⊙ step2
  --       -- step0 ∷ φ l (φ n a) -| (Sized (->)) φ 1 n |-> φ l      a
  --       -- step0 = unsplat
  --       -- step1 ∷ φ l      a  -| (Sized (->)) φ n 1 |-> φ l (φ n a)
  --       -- step1 = splat
  --   in  step3




-- VS.Vector instance for Sized (->)

instance Monoidal VS.Vector (Sized (->)) where
  (Sized f) *** (Sized g) = Sized $ parV f g
  ith i  = Sized ∘ ithV i ∘ unSized
  sing  = Sized singV
  unsing  = Sized unsingV
  join   = Sized joinV
  split  = Sized splitV

{- | @zip ≝ Sized sequenceA@

@zipWith (Sized f) ≝ Sized $ Prelude.fmap f ∘ sequenceA@
-}
instance Zip VS.Vector (Sized (->)) where
  zip = Sized sequenceA
  zipWith = Sized ∘ zipWithV ∘ unSized

-- instance Functor (VS.Vector 1) VS.Vector VS.Vector (Sized (->)) (Sized (->)) where
--   fmap ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type).
--         ( KnownNat n, KnownNat m
--         , Object VS.Vector (Sized (->)) n a, Object VS.Vector (Sized (->)) n (VS.Vector 1 a)
--         , Object VS.Vector (Sized (->)) m b, Object VS.Vector (Sized (->)) m (VS.Vector 1 b)
--         )
--         ⇒ (a -| (Sized (->)) VS.Vector n m |-> b)
--         → (VS.Vector 1 a -| (Sized (->)) VS.Vector n m |-> VS.Vector 1 b)
--   fmap f = split . f . join




-- Data.Array.Shaped instance for Sized (->)


instance Monoidal R1 (Sized (->)) where

  (f ∷ Sized (->) R1 n m a b) *** (g ∷ Sized (->) R1 n' m' a b) =
     Sized   $ R1
   ∘ (parA (unR1 ∘ unSized f ∘ R1)
           (unR1 ∘ unSized g ∘ R1)
     )
   ∘ unR1

  ith (i ∷ (Finite n)) (f ∷ (Sized (->) R1 1 1 a a)) =
     Sized   $ R1
   ∘ ithA' i (unR1 ∘ unSized f ∘ R1)
   ∘ unR1

  sing = Sized $ R1 ∘ pure

  unsing = join

  join = Sized joinR1

  split ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
        ( KnownNat n, KnownNat m )
        ⇒ Sized (->) R1 (n * m) n a (R1 m a)
  split = splitR1

  assoc = split ⊙ join


{- | @zip = Sized sequenceA@ (+ newtype wrapping).

@zipWith (Sized f) ≈ Sized $ Prelude.fmap f ∘ sequenceA@
-}
instance Zip R1 (Sized (->)) where
  zip = Sized
      $ R1 ∘ F.fmap R1
      ∘ sequenceA
      ∘ F.fmap unR1 ∘ unR1

  zipWith (Sized f) = Sized
                    $ R1 ∘ F.fmap R1
                    ∘ F.fmap (unR1 ∘ f ∘ R1)
                    ∘ sequenceA
                    ∘ F.fmap unR1 ∘ unR1


-- TODO revisit when you revisit comonad instances
{- | @orthotope@ arrays are probably better used with their reshaping abilities
than monadically.

Like @Data.Vector.Sized@, @join@ gets the "diagonal" from the "square matrix" of
its input.
-}
instance (KnownNat n) ⇒ M.Monad (R1 n) where
  return = pure

  (ma ∷ R1 n a) >>= (f ∷ a → R1 n b) = diagR1 (F.fmap f ma)

-- TODO revisit when you need a comonad instance — there's really a slew of instances
-- that make sense
-- instance (KnownNat n) ⇒ W.Comonad (R1 n) where


{- for an RN instance of zip...

>>> import Text.PrettyPrint.HughesPJClass
>>> pp = putStrLn ∘ prettyShow
>>> import Data.Array.Shaped qualified as A
>>> abcdef = A.fromList @'[6] "abcdef"
>>> abcdef23 = A.reshape @[2,3] abcdef
>>> abcdef32 = A.reshape @[3,2] abcdef
>>> pp $ A.window @[2,1] abcdef23
>>> :t A.window @[2,1] abcdef23
>>> pp $ A.reshape @[3,2] $ A.window @[2,1] abcdef23 -- "zipping together" each column of the two rows of abcdef23
>>> pp $ A.window @[1,2] abcdef32
>>> pp $ A.reshape @[3,2] $ A.window @[1,2] abcdef32 -- same as @pp abcdef32@
-}



-- instance (Semiring a) ⇒ ISemigroupoid R1 Sr2 a where
--   -- type IObject R1 Sr2 n a = (Semiring a)
--   (.) = mulSr2


-- instance (Semiring a, Semigroupoid R1 (One a Sr2)) ⇒ Category R1 (One a Sr2) where
--   id = One $ idSr2

-- TODO Monoidal instance for SrN
