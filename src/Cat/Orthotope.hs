{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- see comments on takeA, dropA
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{- |

= @orthotope@?

This module contains types and functions used for method definitions for
monoidal product functors based on the
[@orthotope@](https://hackage.haskell.org/package/orthotope) package's 'Array'
type from @Data.Array.Shaped@.

The @orthotope@ package's APL-inspired combinators for "reshaping",
"stretching", "broadcasting", etc. offer an ergonomic interface for
multidimensional arrays that are internally a single flat array together with
metadata about dimensions (a so-called "dope vector"). (See
[Lennart Augustsson's talk](https://www.youtube.com/watch?v=rtc_j8Hnzac) for an
introduction to these ideas in the context of @orthotope@.)

While not offering the fully expressivity of rank polymorphic operators in an
APL-like language, in the context of this package the small set of combinators
available from @orthotope@ can conveniently express many useful operations on
homogeneously nested finite, traversable, etc. monoidal products
("multidimensional arrays") that would normally be expressed using a slew of
much more polymorphic combinators on arbitrarily heterogeneous compositions
(nestings) of functors in a language like Haskell.


== This module

The main rationale for this module is the types and smart constructors it
exports — the sized product type 'R1' that can be combined with e.g. '(->)' plus
typess representing a category of matrices or tensors over a semiring;
underlying helper functions on @Array@s used here are defined in
'Cat.Orthotope.Extras'.

The 'R1' wrapper around @Array [n] a@ is one of the monoidal product functors
with many instances for `(->)` currently.

The 'Sr2' wrapper around @Array [m,n] a@ represents matrices over a semiring @a@
(i.e. morphisms to+from finite dimensional vectors over @a@). It is also a
simpler version of the 'SrN' type representing tensors of rank ≥ 2.

  - The 'Sr2' type is associated with the 'Semiring' typeclass offered by
  @algebraic-graphs@; pending more important development, there are other
  packages offering 'Semiring' classes embedded in a richer hierarchy that might
  be more useful more often (e.g. 'numhask') or for more purposes.

An 'SrN' wrapper around an @Array (m : n : outs ++ ins) a@ represents a morphism
from a tensor of shape @n : ins@ to one of shape @m : outs@ where both contain
values from a semiring @a@. Type families allow it to be treated as though it
were an explicitly nested @Array@ of @Array@s.

== Status

This module is in-progress, currently missing

 - Actual instances for most category-related typeclasses for 'Sr2': while the
   module has functions suitable for many instances, the @Monoidal@ typeclass
   currently requires that any instance be able to represent nested products.
   Until or unless these methods are split off into a subclass for monoidal
   categories with monadic product functors, no @Monoidal@ instance will be
   possible for 'Sr2'.
 - Function definitions for most category typeclass methods for 'SrN' besides
   'Semigroupoid' and 'Category'; unlike 'Sr2', 'SrN' is capable of representing
   morphisms to and from nested products.
-}

module Cat.Orthotope
  ( -- * Data
    -- | These are product functors intended to serve as product functors per se,
    --  not as morphisms.
    R0 (R0, unR0)
  , r0
  , R1 (R1, unR1)
  , RN (RN, unRN)

    -- * 'R1' and `(->)`
    -- ** Monad instance
  , diagR1
  , diagA
    -- ** 'Monoidal' instance
  , parA
  , unParA
  , ithA
  , ithA'
  , splitR1
  , splitA
  , joinR1
  , joinA
  , takeA
  , dropA
    -- ** 'Braided' instance
  , swapA
    -- ** 'Permutable' instance
  , permuteA
    -- ** 'Diagonal' instance
  , forkA
  , dupA
    -- ** 'Select' instance
  , selA
    -- ** 'Delete' instance
  , delA
    -- ** 'Semicocartesian' instance
  , injA
    -- ** 'Pad' instance
  , padA

    -- * Morphisms in a semiring
  , SrN (SrN, getSrN)
  , srN
  , unSrN
  , Nest
  , UnNest
  , UnNesting
  , UnNestings
  , mapSrN
  , Sr2 (Sr2, unSr2)
  , sr2
  , ones
  , zeros
    -- ** 'Semiring' from @algebraic-graphs@ + monoid newtypes
    -- | The 'Semiring' class from @algebraic-graphs@ and these particular newtypes
    -- are currently exported for package development.
  , Semiring (one, (<.>))
  , Sum (Sum, getSum)
  , Any (Any, getAny)
    -- ** Composition (matrix multiplication)
  , mulSrN
  , contract
  , contract2
  , contractn
  , mulANsr
  , mulSr2
  , mulA2sr
  , mulA2get
  , dotSr
  , idSrN
  , idSr2
  , eye
    -- ** Monoidal product (direct sum)
  , sumSr2
  , sumA2
  -- , zeroSr2
  -- , zeroA2
    -- ** Arrow injection
  , ithSr2
  , ithA2
    -- *** Nested product (monadic) combinators
  -- , joinSr2
  -- , joinA2
  -- , splitSr2
  -- , splitA2
    -- ** Braiding
  , swapSr2
  , swapA2
  , permSr2
  , permA2
    -- ** Projection
  , idxSr2
  , hot
  , selSr2
  , selA2
    -- ** Duplication
  , dupSr2
  , dupA2
  , dupSr2'
  , dupA2'
    -- ** Injection
  , injSr2
  , injA2
  , padSr2
  , padA2
    -- ** Coduplication
  , jamSr2
  , jamA2

  ) where

{- TODO

 - Continue to move scattered instance implementations for 'R1' into explicit
   functions and gather them here.

 - TODO Introduce type synonyms or typeclass to make the constraints related to
   permutations/transpositions easier to read and less tedious to write/work
   with in downstream functions.
-}

{- TODO Add relevant instances for (roughly in order of expected utility):
 - RN
 - SrN
 - R0
-}

import Prelude hiding
  ( Functor
  , fmap
  , zip
  , zipWith
  )
import Prelude.Unicode
  ((∘))
import Data.Composition
  ((.:))
import Control.Arrow.Unicode
  ((⁂))
import Control.Arrow
  ( second
  , (&&&)
  , (>>>)
  )

import Data.Kind
  (Type)
import Data.Coerce
  (coerce)
import GHC.Generics
  (Generic)
import Data.Proxy
  (Proxy(Proxy))
import qualified Data.Proxy as P
import GHC.TypeNats
  ( Nat
  -- , SNat
  , pattern SNat
  , KnownNat
  , type (+)
  , type (-)
  , type (<=)
  , type (*)
  , natVal
  -- , withSomeSNat
  -- , withKnownNat
  -- , someNatVal
  -- , natSing
  )
import Data.Finite
  ( Finite
  , getFinite
  , finite
  )


import Data.Bool
  (bool)
import Data.Maybe
  (fromJust)

import Cat.Sized.Semigroupoid.Class
  ( Sized ( Sized )
  -- , unSized
  )

import Data.Functor.Contravariant
  ( contramap
  , Op (Op, getOp)
  )
import Data.Functor       qualified as F
import Data.Functor.Rep   qualified as R

import Data.List          qualified as L
import Data.Vector        qualified as V
import Data.Vector.Sized  qualified as VS
import Data.Array.Convert qualified as C
import Data.Array.Dynamic qualified as D
import Data.Array.Shaped  qualified as A
import Data.Array.Shaped
  ( Array
  , scalar
  , unScalar
  , transpose
  , zipWithA
  , Shape
  , Rank
  , rerank
  , unravel
  , ravel
  , generate
  )
import Data.Array.Internal.Shape (Take, Drop, type (++))
import Data.Array.Internal.Shaped  qualified as S
import Data.Array.Internal.ShapedG qualified as G

import Cat.Orthotope.Extras
  ( Representable (Rep)
  , pregenerate
  , subindexes
  , getSubindex
  , slipNr
  , slipNl
  , vappend
  , happend
  , SplitAt
  , Prefix
  , Suffix
  )

import Data.Monoid
  ( Any ( Any
       , getAny
       )
  , Sum ( Sum
        , getSum
        )
  )
import Algebra.Graph.Label
  ( Semiring ( one
             , (<.>)
             )
  , zero
  , (<+>)
  )




{- | A rank 0 @orthotope@ array, aka a scalar. 'r0' is a smart constructor tagged
with the 'Nat' that is expected to be appropriate.

(If you are unfamiliar with @orthotope@ (or APL-like rank polymorphism and array
languages generally) and are confused by this, note that the /empty/ array of
/length/ ("size") 0 has rank /1/.)

This currently does not have instances associated with it.
-}
newtype R0 (n ∷ Nat) (a ∷ Type) = R0 { unR0 ∷ Array '[] a }
  deriving newtype (Eq, Ord, Read, Show, F.Functor, Foldable)
  deriving stock (Generic, Traversable)

r0 ∷ a → R0 0 a
r0 = R0 ∘ scalar


{- | This newtype creates a "sized" monoidal product functor that lets morphisms
in some category between rank 1 arrays from @orthotope@ ("Data.Array.Shaped") be
treated as morphisms between (tagged, homogeneous) finite products (a "sized
morphism").

This is one of the two basic product functors with the most instances (paired
with `->`) in the package.
-}
newtype R1 (n ∷ Nat) (a ∷ Type) = R1 { unR1 ∷ Array '[n] a }
  deriving newtype (Eq, Ord, Read, Show, F.Functor, Foldable, Applicative)
  deriving stock (Generic, Traversable)


{- | This newtype lets morphisms in some category between arrays of rank ≥ 1 from
@orthotope@ ("Data.Array.Shaped") be treated as morphisms between (tagged,
homogeneous) finite products (a "sized morphism"). -}
newtype RN (sh ∷ [Nat]) (n ∷ Nat) (a ∷ Type)
 = RN { unRN ∷ Array (n ': sh) a }
  deriving newtype (Eq, Ord, Read, Show, F.Functor, Foldable, Applicative)
  deriving stock (Generic, Traversable)



{- | This is the underlying implementation of 'join' in the current monad instance
for 'R1' with respect to '(->)'; it simply returns the diagonal values. -}
diagA ∷ ∀ n a.
      (KnownNat n)
      ⇒ Array '[n] (Array '[n] a) → Array '[n] a
diagA =
  let tab ∷ Array '[n] (Array '[n] a) → [Int] → a
      tab sq [i] = A.unScalar
                 ∘ flip A.index i
                 ∘ A.unScalar
                 ∘ A.index sq
                 $ i
  in  generate ∘ tab

diagR1 ∷ ∀ n a.
       (KnownNat n)
       ⇒ R1 n (R1 n a) → R1 n a
diagR1 = R1
       ∘ diagA
       ∘ F.fmap unR1
       ∘ unR1

{- | Monoidal product for 'R1' and '(->)'. -}
parA ∷ ∀ (n ∷ Nat) (m ∷ Nat) (n' ∷ Nat) (m' ∷ Nat) (a ∷ Type) (b ∷ Type).
     ( KnownNat n, KnownNat m, KnownNat n', KnownNat m' )
     ⇒ (Array '[n]      a → Array '[m]      b)
     → (Array     '[n'] a → Array     '[m'] b)
     → (Array '[n + n'] a → Array '[m + m'] b)
parA f g
  = uncurry A.append
  ∘ (f ⁂ g)
  ∘ unParA


unParA ∷ ∀ (n ∷ Nat) (m ∷ Nat) a.
       ( KnownNat n, KnownNat m )
       ⇒  Array '[n + m] a
       → (Array '[n] a, Array '[m] a)
unParA =   takeA @n
       &&& dropA @n



takeA ∷ ∀ (i ∷ Nat) (n ∷ Nat) a.
      ( KnownNat i, KnownNat n
      , i <= n                  -- GHC can't tell that this constraint is necessary/desirable.
      )
      ⇒ Array '[n] a
      → Array '[i] a
takeA = A.fromVector
      ∘ V.take (fromIntegral $ natVal (Proxy @i))
      ∘ A.toVector


dropA ∷ ∀ (i ∷ Nat) (n ∷ Nat) a.
      ( KnownNat i, KnownNat n
      , i <= n                   -- GHC/HLS claims this is redundant, but also
      )                          -- says this function won't typecheck without it
      ⇒ Array '[n]     a
      → Array '[n - i] a
dropA = A.fromVector
      ∘ V.drop (fromIntegral $ natVal (Proxy @i))
      ∘ A.toVector


ithA ∷ ∀ (n ∷ Nat) (a ∷ Type).
     ( KnownNat n )
     ⇒ Finite n
     → (a → a)
     → (Array '[n] a → Array '[n] a)
ithA (fi ∷ Finite n) (f ∷ a → a)
  = let update_ ∷ Int → (a → a) → V.Vector a → V.Vector a
        update_ i φ v = v V.// [(i, φ $ v V.! i)]
    in A.fromVector @'[n]
     ∘ update_ (fromIntegral ∘ getFinite $ fi) f
     ∘ A.toVector @'[n]


ithA' ∷ ∀ (n ∷ Nat) (a ∷ Type).
      ( KnownNat n )
      ⇒ Finite n
      → (Array '[1] a → Array '[1] a)
      → (Array '[n] a → Array '[n] a)
ithA' (fi ∷ Finite n) (f ∷ Array '[1] a → Array '[1] a)
  = ithA fi ( A.unScalar ∘ flip (A.index) 0
            ∘ f
            ∘ pure
            )


{- |

>>> abcdef ∷ Array '[6] Char = A.fromList "abcdef"
>>> splitA @3 @2 abcdefA
fromList @[3] [fromList @[2] "ab",fromList @[2] "cd",fromList @[2] "ef"]
-}
splitA ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
       ( KnownNat n, KnownNat m )
       ⇒ Array '[n * m] a
       → Array '[n] (Array '[m] a)
splitA = (\as → generate (A.index as ∘ head))
       ∘ A.reshape

splitR1 ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
       ( KnownNat n, KnownNat m )
       ⇒ Sized (->) R1 (n * m) n a (R1 m a)
splitR1 = Sized
        $ R1
        ∘ F.fmap R1
        ∘ splitA
        ∘ unR1


swapA ∷ ∀ (n ∷ Nat) a.
      ( KnownNat n
      )
      ⇒ Finite n
      → Finite n
      → Array '[n] a
      → Array '[n] a
swapA i j a =
  let v = A.toVector a
      i' = fromIntegral $ getFinite i
      j' = fromIntegral $ getFinite j
  in  A.fromVector
    $ v V.// [ (i', v V.! j')
             , (j', v V.! i')
             ]

-- swapA' ∷ ∀ (n ∷ Nat) a prox.
--        ( KnownNat n
--        )
--        ⇒ prox   n
--        → Finite n
--        → Finite n
--        → Array '[n] a
--        → Array '[n] a
-- swapA' (_ ∷ prox n) i j a =
--   let v = A.toVector a
--       i' = fromIntegral $ getFinite i
--       j' = fromIntegral $ getFinite j
--   in  A.fromVector
--     $ v V.// [ (i', v V.! j')
--              , (j', v V.! i')
--              ]



permuteA ∷ ∀ γ n a.
          ( KnownNat n
          -- , Object φ k n a
          -- , PermObject φ k n a
          , R.Representable γ
          , R.Rep γ ~ Finite n
          )
          ⇒ γ (Finite n)
          → Array '[n] a
          → Array '[n] a
permuteA t =
    let
       t' ∷ γ Int
       t' = (fromIntegral ∘ getFinite) <$> t
       p ∷ γ Int → Array '[n] a → Array '[n] a
       p xs fa =   A.generate  -- A.generate ∷ ([Int] → a) → Array sh a
               $   head
               >>> fromIntegral @Int
               >>> finite
               >>> R.index xs
               >>> A.index fa
               >>> A.unScalar
    in p t'



dupA ∷ ∀ (n ∷ Nat) (s ∷ Nat) a.
     ( KnownNat n, KnownNat s
     , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
     )
     ⇒ Array '[    n] a
     → Array '[s * n] a
dupA a =
  let m' ∷ Int
      m' = fromIntegral $ natVal (P.Proxy @(s * n))
      f ∷ [Int] → a
      f [j] = unScalar $ a `A.index` (j `div` m') -- This is safe (in spite of the incomplete pattern matching) iff orthotope's generate implementation is safe.
  in  A.generate f

-- TODO Look at implementation and do some testing to see how performance compares to dupA above
-- dupA' ∷ ∀ (n ∷ Nat) (s ∷ Nat) a.
--       ( KnownNat n, KnownNat s
--       , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
--       )
--       ⇒ Array '[n] a
--       → Array '[s * n] a
-- dupA' = A.reshape @'[s * n]
--       ∘ A.stretchOuter @s
--       ∘ A.reshape @'[1,n]


forkA ∷ ∀ (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) a b.
      ( KnownNat n, KnownNat m
      )
      ⇒ (Array '[l] a → Array '[n    ] b)
      → (Array '[l] a → Array '[    m] b)
      → (Array '[l] a → Array '[n + m] b)
forkA f g = uncurry (A.append) ∘ (f &&& g)



selA ∷ ∀ (l ∷ Nat) (n ∷ Nat) a.
     ( KnownNat l, KnownNat n
     , l <= n                       -- GHC (unhelpfully) warns about this being redundant
     )
     ⇒ Finite ((n - l) + 1) -- ^ The starting index of the length /l/ "slice".
     → Array '[n] a
     → Array '[l] a
selA fn = A.fromVector
        ∘ V.slice (fromIntegral fn) (fromIntegral $ natVal (Proxy @l))
        ∘ A.toVector


delA ∷ ∀ (n ∷ Nat) a.
     ( KnownNat n
     , 1 <= n                       -- GHC (unhelpfully) warns about this being redundant
     )
     ⇒ Finite n
     → Array '[n    ] a
     → Array '[n - 1] a
delA fn a =
  let i  = fromIntegral fn
      n' = fromIntegral $ natVal (Proxy @n)
      l  = n' - 1
      u = A.toVector a
      v = V.slice  0       i             u
      w = V.slice (i + 1) (n' - (i + 1)) u
      f j
       | j < i     = v V.!  j
       | otherwise = w V.! (j - i)
  in A.fromVector $ V.generate l f


injA ∷ (Monoid a, KnownNat m, KnownNat n)
     ⇒ Finite n
     → Array '[1] a
     → Array '[m] a
injA (fn ∷ Finite n) =
  let x = fromIntegral $ getFinite fn
      tab ∷ Monoid a ⇒ a → [Int] → a
      tab a ys
        | head ys == x = a
        | otherwise    = mempty
  in  A.generate ∘ tab
    ∘ unScalar ∘ flip A.index 0


padA ∷ ∀ n l a. (KnownNat n, KnownNat l, Monoid a)
     ⇒ (Finite ((n - l) + 1))
     → Array '[l] a
     → Array '[n] a
padA (x ∷ Finite ((n - l) + 1)) =
    let l' = fromIntegral @Nat     @Int $ natVal (SNat @l)
        x' = fromIntegral @Integer @Int $ getFinite x
        tab ∷ Array '[l] a → [Int] → a
        tab fa ys =
          let y = head ys
          in  if   y >= x' || y < (x' + l')
              then unScalar $ A.index fa y
              else mempty
    in A.generate ∘ tab




-- TODO optimize this later / to whatever extent that's possible+worthwhile
joinA ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
      ( KnownNat n, KnownNat m )
      ⇒ Array '[n] (Array '[m] a) → Array '[n * m] a
joinA = A.fromList
       ∘ concat
       ∘ F.fmap A.toList ∘ A.toList

joinR1 ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ Type).
       ( KnownNat n, KnownNat m )
       ⇒ R1 n (R1 m a) → R1 (n * m) a
joinR1 = R1
       ∘ joinA
       ∘ F.fmap unR1
       ∘ unR1



{- | This newtype lets rank 2 @orthotope@ arrays ("Data.Array.Shaped") with @n@
columns and @m@ rows ("matrices") be treated as morphisms

- from rank 1 arrays of size @n@ ("column vectors")

- to rank 1 arrays of size @m@ ("row vectors").

Note that

 - The order of size parameters on @M@ follows the convention of (all else
being equal) input parameters preceding output parameters.
 - The order of dimension sizes on the wrapped "Array" type is flipped.

Why? Because it makes matrix multiplication /G⋅F/ align with function
composition /g ∘ f/. -}
newtype M2 (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type)
  = M2 { unM2 ∷ Array '[m,n] b }
  deriving newtype (Eq, Ord, Read, Show, F.Functor, Foldable, Applicative)
  deriving stock (Generic, Traversable)


{- | A rank 2 'Array' of shape @[m,n]@ carrying @a@ values is isomorphic to a
morphism from @R1 n a@ to @R1 m a@. -}
m2 ∷ ∀ n m a. Array '[m,n] a → M2 R1 n m a a
m2 = M2


{- | Variant on 'M2' specifically intended to model matrices over a semiring.

The inability of this type to represent nested products means it cannot have a
@Monoidal@ instance as long that typeclass requires definitions of methods
for working with nested products. -}
newtype Sr2 (φ ∷ Nat → κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type)
  = Sr2 { unSr2 ∷ Array '[m,n] b }
  deriving newtype (Eq, Ord, Read, Show, F.Functor, Foldable, Applicative)
  deriving stock (Generic, Traversable)



{- | A rank 2 'Array' of shape @[m,n]@ carrying @a@ values is isomorphic to a
morphism from @R1 n a@ to @R1 m a@. -}
sr2 ∷ ∀ n m a. Semiring a
    ⇒ Array '[m,n] a → Sr2 R1 n m a a
sr2 = Sr2



{- | Dot product for values in a 'Semiring'.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> six = A.iota @6 :: Array '[6] Int
>>> pp six
┌───────────┐
│0 1 2 3 4 5│
└───────────┘
>>> a = reshape @[3,2] six
>>> b = reshape @[2,3] six
>>> pp a
┌───┐
│0 1│
│2 3│
│4 5│
└───┘
>>> pp b
┌─────┐
│0 1 2│
│3 4 5│
└─────┘
>>> a_row2 = a `A.index` 2
>>> b_col2 = (transpose @'[1,0] b) `A.index` 2
>>> pp a_row2
┌───┐
│4 5│
└───┘
>>> pp b_col2
┌───┐
│2 5│
└───┘
>>> pp $ getSum <$> dotSr (Sum <$> a_row2) (Sum <$> b_col2)
┌──┐
│33│
└──┘
-}
dotSr ∷ ∀ n a. (KnownNat n, Semiring a)
      ⇒ Array '[n] a → Array '[n] a → Array '[] a
dotSr =  A.reduce   (<+>) zero
      .: zipWithA (<.>)

instance (Num a) ⇒ Semiring (Sum a) where
  one = Sum 1
  (Sum a) <.> (Sum b) = Sum $ a * b



{- | Accessor that takes a pair of 2D arrays /g, f/ with dimensions suitable for
multiplication (composition) /g ⋅ f/ and returns a function from a pair of
indices into their common dimension. -}
mulA2get ∷ ∀ n m o a.
         (KnownNat n, KnownNat m, KnownNat o)
         ⇒ Array '[o,m] a
         → Array '[m,n] a
         → (Int, Int)
         → (Array '[m] a, Array '[m] a)
mulA2get = uncurry (⁂)
         ∘ (A.index ⁂ A.index)
         ∘ second (transpose @'[1,0])
        .: (,)


{- | Naive matrix multiplication for 2D orthotope arrays with elements in a 'Semiring'.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> g = A.fromList [2, 8, 3, 5, 4, 1] :: Array '[2,3] Int
>>> f = A.fromList [4, 1, 6, 3, 2, 4] :: Array '[3,2] Int
>>> pp g
┌─────┐
│2 8 3│
│5 4 1│
└─────┘
>>> pp f
┌───┐
│4 1│
│6 3│
│2 4│
└───┘
>>> pp $ getSum <$> mulA2sr (Sum <$> g) (Sum <$> f)
┌─────┐
│62 38│
│46 21│
└─────┘
-}
mulA2sr ∷ ∀ n m o a.
        (KnownNat n, KnownNat m, KnownNat o, Semiring a)
        ⇒ Array '[o,m] a
        → Array '[m,n] a
        → Array '[o,n] a
mulA2sr = generate                                        -- ∷ ([Int] → a) → Array '[n,o] a
        ∘ getOp ∘ contramap ((L.!! 0) &&& (L.!! 1)) ∘ Op  -- "adapter" for orthotope's 'tabulate' variant
        ∘ (   unScalar ∘ uncurry dotSr
          .: uncurry mulA2get
          )
       .: (,)


mulSr2 ∷ ∀ n m o a.
        ( KnownNat n, KnownNat m, KnownNat o
        , Semiring a
        )
        ⇒ Sr2 R1 m o a a
        → Sr2 R1 n m a a
        → Sr2 R1 n o a a
mulSr2 = Sr2
       ∘ uncurry mulA2sr
       ∘ (unSr2 ⁂ unSr2)
      .: (,)


{- | Contract a multidimensional tensor along (sum over) its leading dimension. -}
contract ∷ ∀ n sh l a.
         ( KnownNat n
         , Shape sh
         , SplitAt l sh '[n]
         , (sh ++ '[]) ~ sh
         , Semiring a
         )
         ⇒ Array (n ': sh) a
         → Array sh a
contract = rerank @l @'[n] @'[] @(sh ++ '[n]) (A.reduce (<+>) zero)
         ∘ C.convert
         ∘ (flip D.transpose <*> (slipNr 1))
         ∘ C.convert


{- | Contract a pair of multidimensional arrays along (sum over) their common
leading dimension: in roughly Einstein summation notation,

\( out_{a,b,c,x,y} = g_{i,a,b,c} ⋅ f_{i,x,y} \)

>>> f = A.reshape $ A.iota ∷ Array [2,3,4] Int
>>> g = A.reshape $ A.iota ∷ Array [2,5] Int
>>> pp f
┌───────────┐
│ 0  1  2  3│
│ 4  5  6  7│
│ 8  9 10 11│
│           │
│12 13 14 15│
│16 17 18 19│
│20 21 22 23│
└───────────┘
>>> pp g
┌─────────┐
│0 1 2 3 4│
│5 6 7 8 9│
└─────────┘
>>> :t F.fmap getSum $ contract2 (Sum <$> f) (Sum <$> g)
F.fmap getSum $ contract2 (Sum <$> f) (Sum <$> g)
  :: Array [3, 4, 5] Int
>>> pp $ F.fmap getSum $ contract2 (Sum <$> f) (Sum <$> g)
┌───────────────────┐
│ 60  72  84  96 108│
│ 65  79  93 107 121│
│ 70  86 102 118 134│
│ 75  93 111 129 147│
│                   │
│ 80 100 120 140 160│
│ 85 107 129 151 173│
│ 90 114 138 162 186│
│ 95 121 147 173 199│
│                   │
│100 128 156 184 212│
│105 135 165 195 225│
│110 142 174 206 238│
│115 149 183 217 251│
└───────────────────┘
-}
contract2 ∷ ∀ n sh sh' lSh lSh' a.
          ( KnownNat n
          , Shape sh, Shape sh', Shape (sh  ++ sh')
          , Shape (Take lSh  (sh  ++ '[n]))
          , Shape (Take lSh' (sh' ++ '[n]))
          , Suffix lSh  sh  '[n]
          , Suffix lSh' sh' '[n]
          , Semiring a
          )
          ⇒ Array (n  ': sh ) a  -- ^ A tensor whose leading dimension matches that of the other operand.
          → Array (n  ': sh') a
          → Array (sh ++ sh') a
contract2 =
  let
    lsh = fromIntegral $ natVal (SNat @lSh)

    preg ∷ Array (n  ': sh ) a → Array (sh  ++ '[n]) a
    pref ∷ Array (n  ': sh') a → Array (sh' ++ '[n]) a
    preg = C.convert ∘ (flip D.transpose <*> slipNr 1) ∘ C.convert
    pref = C.convert ∘ (flip D.transpose <*> slipNr 1) ∘ C.convert

    h ∷ Array (sh  ++ '[n]) a → Array (sh' ++ '[n]) a → [Int] → a
    h g f = let h' = unScalar
                   ∘ (uncurry (dotSr @n))
                   ∘ ((fromJust .: (subindexes @lSh ) $ g) ⁂ (fromJust .: (subindexes @lSh') $ f))
                   ∘ L.splitAt lsh
            in  h'

  in  generate
    ∘ (uncurry h)
    ∘ (preg ⁂ pref)
   .: (,)



-- TODO See what can be done to simplify constraints by unifying annotations
-- that GHC can't figure out are equivalent.
-- TODO Performance: After upstream operations have been considered for
-- performance, it's probably worth spending a little time on this; ultimately
-- though, as long as performance isn't horrific, simplifying constraints ±
-- focusing on making operations translate to a tensor library focused on
-- performance is a better investment of time.
{- | @contractn \@n g f@ contracts a pair of multidimensional arrays along (sums
over) their common leading /n/ dimensions @ds@: in roughly Einstein summation
notation, a contraction over the leading 3 dimensions could look like

\( out_{a,b,c,x,y} = g_{i,j,k,a,b,c} ⋅ f_{i,j,k,x,y} \)

>>> f = A.reshape $ A.iota ∷ Array [2,4,5] Int
>>> g = A.reshape $ A.iota ∷ Array [2,4,3,6] Int
>>> pp f
┌──────────────┐
│ 0  1  2  3  4│
│ 5  6  7  8  9│
│10 11 12 13 14│
│15 16 17 18 19│
│              │
│20 21 22 23 24│
│25 26 27 28 29│
│30 31 32 33 34│
│35 36 37 38 39│
└──────────────┘
>>> pp g
┌───────────────────────┐
│  0   1   2   3   4   5│
│  6   7   8   9  10  11│
│ 12  13  14  15  16  17│
│                       │
│ 18  19  20  21  22  23│
│ 24  25  26  27  28  29│
│ 30  31  32  33  34  35│
│                       │
│ 36  37  38  39  40  41│
│ 42  43  44  45  46  47│
│ 48  49  50  51  52  53│
│                       │
│ 54  55  56  57  58  59│
│ 60  61  62  63  64  65│
│ 66  67  68  69  70  71│
│                       │
│                       │
│ 72  73  74  75  76  77│
│ 78  79  80  81  82  83│
│ 84  85  86  87  88  89│
│                       │
│ 90  91  92  93  94  95│
│ 96  97  98  99 100 101│
│102 103 104 105 106 107│
│                       │
│108 109 110 111 112 113│
│114 115 116 117 118 119│
│120 121 122 123 124 125│
│                       │
│126 127 128 129 130 131│
│132 133 134 135 136 137│
│138 139 140 141 142 143│
└───────────────────────┘
>>> :t F.fmap getSum $ contractn @2 (Sum <$> f) (Sum <$> g)
F.fmap getSum $ contractn @2 (Sum <$> f) (Sum <$> g)
  :: Array [5, 3, 6] Int
>>> pp $ F.fmap getSum $ contractn @2 (Sum <$> f) (Sum <$> g)
┌───────────────────────────────────┐
│12600 12740 12880 13020 13160 13300│
│13440 13580 13720 13860 14000 14140│
│14280 14420 14560 14700 14840 14980│
│                                   │
│13104 13252 13400 13548 13696 13844│
│13992 14140 14288 14436 14584 14732│
│14880 15028 15176 15324 15472 15620│
│                                   │
│13608 13764 13920 14076 14232 14388│
│14544 14700 14856 15012 15168 15324│
│15480 15636 15792 15948 16104 16260│
│                                   │
│14112 14276 14440 14604 14768 14932│
│15096 15260 15424 15588 15752 15916│
│16080 16244 16408 16572 16736 16900│
│                                   │
│14616 14788 14960 15132 15304 15476│
│15648 15820 15992 16164 16336 16508│
│16680 16852 17024 17196 17368 17540│
└───────────────────────────────────┘
-}
contractn ∷ ∀ n ds sh sh' lSh lSh' a.
          ( Shape ds, Shape sh, Shape sh', Shape (sh ++ sh')
          , Prefix n ds sh
          , Prefix n ds sh'
          , Suffix lSh  sh  ds
          , Suffix lSh' sh' ds
          , Shape (Take lSh  (sh  ++ ds))
          , Shape (Take lSh' (sh' ++ ds))
          , Semiring a
          )
          ⇒ Array (ds ++ sh ) a  -- ^ A tensor whose trailing dimensions after the first /n/ (@ds@) will be the leading dimensions of the contracted tensor.
          → Array (ds ++ sh') a
          → Array (sh ++ sh') a
contractn =
  let
    lsh = fromIntegral $ natVal (SNat @lSh)
    n'  = natVal (SNat @n)

    preg ∷ Array (ds ++ sh ) a → Array (sh  ++ ds) a
    pref ∷ Array (ds ++ sh') a → Array (sh' ++ ds) a
    preg = C.convert ∘ (flip D.transpose <*> slipNr n') ∘ C.convert
    pref = C.convert ∘ (flip D.transpose <*> slipNr n') ∘ C.convert

    h ∷ Array (sh  ++ ds) a → Array (sh' ++ ds) a → [Int] → a
    h g f = let h' = unScalar
                   ∘ A.reduce (<+>) zero
                   ∘ uncurry (A.zipWithA (<.>))
                   ∘ ((fromJust .: (subindexes @lSh ) $ g) ⁂ (fromJust .: (subindexes @lSh') $ f))
                   ∘ L.splitAt lsh
            in  h'

  in  generate
    ∘ (uncurry h)
    ∘ (preg ⁂ pref)
   .: (,)


-- TODO Introduce a type synonym or typeclass to make the constraints here
-- easier to read and less tedious to write/work with in downstream functions.
{- | Permute the dimensions of a pair of 'SrN' morphisms so that the common
dimensions to be contracted along are moved to the front.

>>> g' = (A.reshape $ A.iota) ∷ Array [6,2, 7,8,9,10, 3,4,5] Int
g' :: Array [6, 2, 7, 8, 9, 10, 3, 4, 5] Int
>>> f' = (A.reshape $ A.iota) ∷ Array [2,6, 3,4,5, 7,8,9,10] Int
f' :: Array [2, 6, 3, 4, 5, 7, 8, 9, 10] Int
>>> g = srN @4 @3 g'
g ::
  SrN
    Int
    R1
    2
    6
    (R1 3 (R1 4 (R1 5 Int)))
    (R1 7 (R1 8 (R1 9 (R1 10 Int))))
>>> f = srN @3 @4 f'
f ::
  SrN
    Int
    R1
    6
    2
    (R1 7 (R1 8 (R1 9 (R1 10 Int))))
    (R1 3 (R1 4 (R1 5 Int)))
>>> :t precontractn g f
precontractn g f
  :: (Array [2, 3, 4, 5, 6, 7, 8, 9, 10] Int,
      Array [2, 3, 4, 5, 6, 7, 8, 9, 10] Int)
-}
precontractn ∷ ∀ n m o
               ds sh sh'
               s a b c.
             ( UnNestings s R1 m o b c ds  sh
             , UnNestings s R1 n m a b sh' ds
             , Shape ((UnNest s R1 b) ++ sh )
             , Shape ((UnNest s R1 b) ++ sh')
             )
             ⇒ SrN s R1 m o b c
             → SrN s R1 n m a b
             → ( Array (ds ++ sh ) s
               , Array (ds ++ sh') s
               )  -- ^ The underlying arrays of the two morphisms with their dimensions permuted for contraction.
precontractn =
  let
      lds  = fromIntegral $ natVal $ SNat @(A.Rank ds )
      lsh  = fromIntegral $ natVal $ SNat @(A.Rank sh )
      lsh' = fromIntegral $ natVal $ SNat @(A.Rank sh')

      trF  = (0 : [2..lds]) ++ (1 : [(lds + 1)..(lds + lsh' - 1)])
      trG  = (1 : [(lsh + 1)..(lsh + lds - 1)]) ++ (0 : [2..lsh])

      permG ∷ Array (o : m : (UnNest s R1 c ++ UnNest s R1 b)) s → Array (ds ++ sh ) s
      permF ∷ Array (m : n : (UnNest s R1 b ++ UnNest s R1 a)) s → Array (ds ++ sh') s
      permG = C.convert ∘ D.transpose trG ∘ C.convert
      permF = C.convert ∘ D.transpose trF ∘ C.convert
  in  ((permG ∘ unSrN) ⁂ (permF ∘ unSrN))
   .: (,)



-- TODO Introduce a type synonym or typeclass to make the constraints here
-- easier to read and less tedious to write/work with in downstream functions.
{- | Postprocess an 'Array' that is the result of a composition (contraction)
of 'SrN' morphisms.

>>> f = (A.reshape $ A.iota) ∷ Array [3,6,7,8, 2,4,5] Int
>>> :t postcontractn @2 @3 @[3,6,7,8] f
postcontractn @2 @3 @[3,6,7,8] f
  :: SrN Int R1 2 3 (R1 4 (R1 5 Int)) (R1 6 (R1 7 (R1 8 Int)))
-}
postcontractn ∷ ∀ n o sh sh' s a c.
              ( UnNestings s R1 n o a c sh' sh
              , a ~ Nest s R1 (UnNest s R1 a)
              , c ~ Nest s R1 (UnNest s R1 c)
              , SplitAt (Rank (UnNest s R1 c)) (UnNest s R1 c) (UnNest s R1 a)
              , Shape (UnNest s R1 c ++ (n : UnNest s R1 a))
              )
              ⇒ Array (sh ++ sh') s
              → SrN s R1 n o a c
postcontractn =
  let lsh  = fromIntegral $ natVal $ SNat @(A.Rank sh )
      lsh' = fromIntegral $ natVal $ SNat @(A.Rank sh')

      tr = [0, lsh] ++ [1..(lsh - 1)] ++ [(lsh + 1)..(lsh + lsh' - 1)]

      perm ∷ Array (sh ++ sh') s → Array (o : n : (UnNest s R1 c) ++ (UnNest s R1 a)) s
      perm = C.convert ∘ D.transpose tr ∘ C.convert
  in  srN @(Rank (UnNest s R1 c)) @(Rank (UnNest s R1 a)) ∘ perm



-- TODO Introduce a type synonym or typeclass to make the constraints here
-- easier to read and less tedious to write/work with in downstream functions.
{- | @mulSrN g f@ composes @g@ with @f@, contracting the underlying tensors along
the dimensions specified by their types.

>>> f' = A.reshape $ A.iota ∷ Array [3,2, 5,6, 4] Int
>>> g' = A.reshape $ A.iota ∷ Array [4,3, 7, 5,6] Int
>>> f = srN @2 @1 $ Sum <$> f'
f :: SrN Int R1 2 3 (R1 4 (Sum Int)) (R1 5 (R1 6 (Sum Int)))
>>> g = srN @1 @2 $ Sum <$> g'
g :: SrN Int R1 3 4 (R1 5 (R1 6 Int)) (R1 7 Int)
>>> :t mulSrN @3 g f
mulSrN g f :: SrN (Sum Int) R1 2 4 (R1 4 (Sum Int)) (R1 7 (Sum Int))
-}
mulSrN ∷ ∀ r n m o
          ds sh sh' lSh lSh'
          s a b c.
      ( UnNestings s R1 m o b c ds  sh
      , UnNestings s R1 n m a b sh' ds
      , Suffix lSh  sh  ds
      , Suffix lSh' sh' ds
      , Prefix r ds sh
      , Prefix r ds sh'
      , a  ~ Nest s R1 (UnNest s R1 a)
      , c  ~ Nest s R1 (UnNest s R1 c)
      , SplitAt (Rank (UnNest s R1 c)) (UnNest s R1 c) (UnNest s R1 a)
      , (lSh' + r) ~ (1 + Rank (UnNest s R1 b ++ sh'))
      , (lSh  + r) ~ (1 + Rank (UnNest s R1 b ++ sh ))
      , Shape (Take lSh  (sh  ++ ds))
      , Shape (Take lSh' (sh' ++ ds))
      , Shape (UnNest s R1 b ++ sh )
      , Shape (UnNest s R1 b ++ sh')
      , Shape (UnNest s R1 c ++ sh')
      , Semiring s
      )
      ⇒ SrN s R1 m o b c  -- ^ A tensor ≅ to a morphism from @R1 m b@ to @R1 o c@.
      → SrN s R1 n m a b  -- ^ A tensor ≅ to a morphism from @R1 n a@ to @R1 m b@.
      → SrN s R1 n o a c
mulSrN = postcontractn @n @o @sh @sh' @s @a @c
       ∘ uncurry (contractn @r @ds @sh @sh' @lSh @lSh')
       ∘ uncurry (precontractn @n @m @o @ds @sh @sh' @s @a @b @c)
      .: (,)



-- TODO Introduce a type synonym or typeclass to make the constraints here
-- easier to read and less tedious to write/work with in downstream functions.
-- TODO Performance: After upstream operations have been considered for
-- performance, it's probably worth spending a little time on this; ultimately
-- though, as long as performance isn't horrific, simplifying constraints ±
-- focusing on making operations translate to a tensor library focused on
-- performance is a better investment of time.
{- | Generalization of matrix multiplication for /n/-dimensional tensors:
performs a tensor contraction by summing over a single common index.

In roughly Einstein summation notation, given /g ∷ o ✕ m ✕ i/, /f ∷ m ✕ n ✕ i/,
this produces a tensor /h/ where coordinate /(o,n,i)/ is defined by

\( h_{o,n} =  g_{o,m} ⋅ f_{m,n} \)

Note that the /i/-sized dimension is not mentioned; the computation above is
"broadcast" along /i/.

>>> g = A.reshape @[5,2,4] $ A.iota @40 @Int
>>> f = A.reshape @[2,3,4] $ A.iota @24 @Int
>>> :t getSum <$> mulANsr (Sum <$> g) (Sum <$> f)
getSum <$> mulANsr (Sum <$> g) (Sum <$> f)
  :: Array [5, 3, 4] Int
>>> pp g
┌───────────┐
│ 0  1  2  3│
│ 4  5  6  7│
│           │
│ 8  9 10 11│
│12 13 14 15│
│           │
│16 17 18 19│
│20 21 22 23│
│           │
│24 25 26 27│
│28 29 30 31│
│           │
│32 33 34 35│
│36 37 38 39│
└───────────┘
>>> pp f
┌───────────┐
│ 0  1  2  3│
│ 4  5  6  7│
│ 8  9 10 11│
│           │
│12 13 14 15│
│16 17 18 19│
│20 21 22 23│
└───────────┘
>>> pp $ getSum <$> mulANsr (Sum <$> g) (Sum <$> f)
┌───────────────────┐
│  48   66   88  114│
│  64   90  120  154│
│  80  114  152  194│
│                   │
│ 144  178  216  258│
│ 224  266  312  362│
│ 304  354  408  466│
│                   │
│ 240  290  344  402│
│ 384  442  504  570│
│ 528  594  664  738│
│                   │
│ 336  402  472  546│
│ 544  618  696  778│
│ 752  834  920 1010│
│                   │
│ 432  514  600  690│
│ 704  794  888  986│
│ 976 1074 1176 1282│
└───────────────────┘
-}
mulANsr ∷ ∀ n m o sh l a.
        ( KnownNat n, KnownNat m, KnownNat o
        , Shape sh
        , Shape (Drop l (sh ++ [o,n]))
        , Shape (Take l (sh ++ [o,n]))
        , Suffix  l sh [o,n]
        , SplitAt l sh [o,m]
        , SplitAt l sh [m,n]
        , Semiring a
        )
        ⇒ Array (o ': m ': sh) a  -- ^ /o✕m✕sh/ tensor to be contracted along /m/.
        → Array (m ': n ': sh) a  -- ^ /m✕n✕sh/ tensor to be contracted along /m/.
        → Array (o ': n ': sh) a
mulANsr =
  let
      preg ∷ Array (o ': m ': sh) a → Array ( sh ++ [o,m] ) a
      pref ∷ Array (m ': n ': sh) a → Array ( sh ++ [m,n] ) a
      preg = C.convert ∘ (flip D.transpose <*> (slipNr 2)) ∘ C.convert
      pref = C.convert ∘ (flip D.transpose <*> (slipNr 2)) ∘ C.convert

      -- Reach @l@ levels down and broadcast matrix multiplication
      -- ≡ perform a contraction along the specified common axis.
      h ∷ Array ( sh ++ [o,m] ) a
        → Array ( sh ++ [m,n] ) a
        → [Int]
        → Array [o,n] a
      h g' f' = let h_ ∷ [Int] → Array [o,n] a
                    h_ pref' = let g_ ∷ Array [o, m] a
                                   g_ = getSubindex @l pref' g'
                                   f_ ∷ Array [m, n] a
                                   f_ = getSubindex @l pref' f'
                               in  mulA2sr g_ f_
                in h_

      gf ∷ Array ( sh ++ [o,m] ) a
         → Array ( sh ++ [m,n] ) a
         → Array ( sh ++ [o,n] ) a
      gf = pregenerate @l .: h

      postgf ∷ Array (sh ++ [o,n]) a → Array (o ': n ': sh) a
      postgf = C.convert ∘ (flip D.transpose <*> (slipNl 2)) ∘ C.convert

  in  postgf
    ∘ uncurry gf
    ∘ (preg ⁂ pref)
   .: (,)






{- | Create a column vector with a single "hot" index /r/ that selects a
particular row from any matrix the vector is postcomposed with.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> sixEight = A.reshape $ A.iota :: Array [6,8] Int
>>> pp sixEight
┌───────────────────────┐
│ 0  1  2  3  4  5  6  7│
│ 8  9 10 11 12 13 14 15│
│16 17 18 19 20 21 22 23│
│24 25 26 27 28 29 30 31│
│32 33 34 35 36 37 38 39│
│40 41 42 43 44 45 46 47│
└───────────────────────┘
>>> pp $ getSum <$> mulA2sr (hot 2) (Sum <$> sixEight)
┌───────────────────────┐
│16 17 18 19 20 21 22 23│
└───────────────────────┘
>>> twoSixEight = A.stretchOuter @2 $ A.reshape @[1,6,8] sixEight
>>> pp twoSixEight
┌───────────────────────┐
│ 0  1  2  3  4  5  6  7│
│ 8  9 10 11 12 13 14 15│
│16 17 18 19 20 21 22 23│
│24 25 26 27 28 29 30 31│
│32 33 34 35 36 37 38 39│
│40 41 42 43 44 45 46 47│
│                       │
│ 0  1  2  3  4  5  6  7│
│ 8  9 10 11 12 13 14 15│
│16 17 18 19 20 21 22 23│
│24 25 26 27 28 29 30 31│
│32 33 34 35 36 37 38 39│
│40 41 42 43 44 45 46 47│
└───────────────────────┘
>>> import Data.Functor qualified as F
>>> pp $ (rerank @1 $ F.fmap getSum ∘ mulA2sr (hot 2) ∘ F.fmap Sum) twoSixEight
┌───────────────────────┐
│16 17 18 19 20 21 22 23│
│                       │
│16 17 18 19 20 21 22 23│
└───────────────────────┘
-}
hot ∷ ∀ n a.
    ( KnownNat n, Semiring a )
    ⇒ Finite n
    → Array [1,n] a
hot fn =
  let x = fromIntegral $ getFinite fn
      tab y
        | y == x    = one
        | otherwise = zero
  in  A.reshape ∘ generate @'[n] $ tab ∘ head


idxSr2 ∷ ∀ n a.
      (KnownNat n, Semiring a)
      ⇒ Finite n
      → Sr2 R1 n 1 a a
idxSr2 = sr2 ∘ hot


{- | The identity matrix over a semiring. -}
eye ∷ ∀ n a.
    ( KnownNat n, Semiring a )
    ⇒ Array '[n,n] a
eye =
  let tab [x,y]
        | x == y    = one
        | otherwise = zero
  in  generate tab


idSr2 ∷ ∀ n a.
      ( KnownNat n, Semiring a )
      ⇒ Sr2 R1 n n a a
idSr2 = sr2 eye

{- | The identity tensor for the shape @n : (UnNest s R1 a)@. -}
idSrN ∷ ∀ n s a.
     ( KnownNat n
     , Shape (UnNest s R1 a ++ UnNest s R1 a)
     , SplitAt (Rank (UnNest s R1 a)) (UnNest s R1 a) (UnNest s R1 a)
     , a ~ Nest s R1 (UnNest s R1 a)
     , Semiring s
     )
     ⇒ SrN s R1 n n a a  -- ^ The identity tensor for the shape @n : (UnNest s R1 a)@
idSrN =
  let r ∷ Int
      r = (1 ∷ Int) + (fromIntegral $ natVal $ (SNat @(Rank (UnNest s R1 a))))
      tab ∷ [Int] → s
      tab = bool zero one
          ∘ and ∘ uncurry (L.zipWith (==))
          ∘ L.splitAt r
  in srN @(Rank (UnNest s R1 a)) @(Rank (UnNest s R1 a)) @n @n @(UnNest s R1 a) @(UnNest s R1 a)
     ∘ generate $ tab


{- | Create an 'Array' of arbitrary shape filled with the multiplicative identity
of a semiring. -}
ones ∷ ∀ sh a.
     ( A.Shape sh, Semiring a )
     ⇒ Array sh a
ones = A.constant one


{- | Create an 'Array' of arbitrary shape filled with the additive identity of a
semiring. -}
zeros ∷ ∀ sh a.
      ( A.Shape sh, Semiring a )
      ⇒ Array sh a
zeros = A.constant zero



{- | The direct sum (Kronecker sum) of two matrices over a semiring.


>>> exm = A.fromList [2, 8, 3, 5, 4, 1] :: Array [2,3] Int
>>> pp exm
┌─────┐
│2 8 3│
│5 4 1│
└─────┘
>>> exn = A.fromList [4, 1, 6, 3, 2, 4, 5, 7] :: Array [4,2] Int
>>> pp exn
┌───┐
│4 1│
│6 3│
│2 4│
│5 7│
└───┘
>>> :t sumA2 (Sum <$> exm) (Sum <$> exn)
sumA2 (Sum <$> exm) (Sum <$> exn) :: Array [6, 5] (Sum Int)
>>> pp $ F.fmap getSum $ sumA2 (Sum <$> exm) (Sum <$> exn)
┌─────────┐
│2 8 3 0 0│
│5 4 1 0 0│
│0 0 0 4 1│
│0 0 0 6 3│
│0 0 0 2 4│
│0 0 0 5 7│
└─────────┘
-}
sumA2 ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
          (n' ∷ Nat) (m' ∷ Nat)
          a.
        ( KnownNat n , KnownNat m
        , KnownNat n', KnownNat m'
        , Semiring a
        )
        ⇒ Array '[m , n ] a
        → Array '[m', n'] a
        → Array '[m + m', n + n'] a
sumA2 = uncurry vappend
      ∘ (flip happend zeros ⁂ happend zeros)
     .: (,)


sumSr2 ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
           (n' ∷ Nat) (m' ∷ Nat)
           a.
       ( KnownNat n , KnownNat m
       , KnownNat n', KnownNat m'
       , Semiring a
       )
       ⇒ Sr2 R1  n        m       a a
       → Sr2 R1      n'       m'  a a
       → Sr2 R1 (n + n') (m + m') a a
sumSr2 = sr2
       ∘ uncurry sumA2
       ∘ (unSr2 ⁂ unSr2)
      .: (,)


{- | Inject a morphism /f/ acting on a single object into one that acts on /n/
objects, with /f/ acting on a designated /i/th input and identity morphisms on
all other inputs.

>>> two = pure 2 ∷ Array '[1] Int
>>> pp $ getSum <$> ithA2 @3 1 (Sum <$> A.reshape two)
┌─────┐
│1 0 0│
│0 2 0│
│0 0 1│
└─────┘
-}
ithA2 ∷ ∀ (n ∷ Nat) a.
      ( KnownNat n, Semiring a )
      ⇒ Finite n
      → Array '[1,1] a
      → Array '[n,n] a
ithA2 =
  let -- TODO Performance: There's probably a way of using modular arithmetic to
      -- create an appropriate flat container in one pass that can then be
      -- reshaped.
      g' ∷ Int → a → [Int] → a
      g' i a = let g_ [r,c]
                     | r == c && c == i = a
                     | r == c           = one
                     | otherwise        = zero
                in g_
  in generate
   ∘ uncurry g'
   ∘ (fromIntegral ⁂ ( unScalar
                     ∘ flip A.index 0
                     ∘ A.reshape
                     )
     )
   .: (,)


ithSr2 ∷ ∀ (n ∷ Nat) a.
       ( KnownNat n, Semiring a )
       ⇒ Finite n
       → Sr2 R1 1 1 a a
       → Sr2 R1 n n a a
ithSr2 i = sr2 ∘ ithA2 i ∘ unSr2



-- joinA2 ∷ ∀ (n ∷ Nat) (m ∷ Nat) a.
--        ( KnownNat n, KnownNat m, KnownNat (n * m)
--        , Semiring a
--        )
--        ⇒ Array '[n*m,n] a




{- | Per the note on @permute@ in "Cat.Sized.Braided.Class", there's nothing that
statically prevents the representable functor parameter from duplicating (and
hence also) destroying some input indices. This is not currently checked. -}
permA2 ∷ ∀ γ (n ∷ Nat) a.
       ( KnownNat n
       , Representable γ
       , Rep γ ~ Finite n
       , Semiring a
       )
       ⇒ γ (Finite n)
       → Array '[n,n] a
permA2 t =
  let -- TODO Performance: I'm sure there's a bit of modular arithmetic that
      -- might permit defining the result in a single flat vector or list that
      -- can then be reshaped.
      f ∷ [Finite n] → a
      f [r,c]
        | t `R.index` r == c = one
        | otherwise          = zero
  in  generate (f ∘ F.fmap fromIntegral)


permSr2 ∷ ∀ γ (n ∷ Nat) a.
       ( KnownNat n
       , Representable γ
       , Rep γ ~ Finite n
       , Semiring a
       )
       ⇒ γ (Finite n)
       → Sr2 R1 n n a a
permSr2 = Sr2 ∘ permA2


swapA2 ∷ ∀ (n ∷ Nat) a.
       (KnownNat n, Semiring a)
       ⇒ Finite n  -- ^ The first of two indices to swap.
       → Finite n  -- ^ The other of two indices to swap.
       → Array '[n,n] a
swapA2 i j =
  -- TODO Redefine this in terms of actual permutation matrices,
  -- = as the direct sum of appropriate identity matrices
  let f ∷ Finite n → Finite n
      f r
        | r == i    = j
        | otherwise = r
  in  permA2 $ VS.generate f


swapSr2 ∷ ∀ (n ∷ Nat) a.
        (KnownNat n, Semiring a)
        ⇒ Finite n  -- ^ The first of two indices to swap.
        → Finite n  -- ^ The other of two indices to swap.
        → Sr2 R1 n n a a
swapSr2 = sr2 .: swapA2






{- | Create a transformation that takes @l@ inputs to @n ≥ l@ outputs, with excess
dimensions padded with zero, and with the @l@ inputs starting at a given offset.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> pp $ getSum <$> padA2 @3 @4 @(Sum Int) 0
┌─────┐
│1 0 0│
│0 1 0│
│0 0 1│
│0 0 0│
└─────┘
>>> pp $ getSum <$> padA2 @3 @4 @(Sum Int) 1
┌─────┐
│0 0 0│
│1 0 0│
│0 1 0│
│0 0 1│
└─────┘
>>> six = A.iota ∷ Array '[6] Int
>>> pp six
┌───────────┐
│0 1 2 3 4 5│
└───────────┘
>>> pp $ A.reshape @'[8] $ getSum <$> mulA2sr (padA2 @6 @8 0) (A.reshape @[6,1] (Sum <$> six))
┌───────────────┐
│0 1 2 3 4 5 0 0│
└───────────────┘
-}
padA2 ∷ ∀ l n a.
      ( KnownNat l, KnownNat n, Semiring a)
      ⇒ Finite ((n - l) + 1)          -- ^ The index to inject a slice into.
      → Array '[n,l] a
padA2 idx =
  let x  = fromIntegral $ getFinite idx ∷ Int
      l' = fromIntegral $ natVal $ SNat @l
      n' = fromIntegral $ natVal $ SNat @n
      x' =  x + l'                          -- Last index of the slice
      topBotPads = (x, n' - x')             -- # dims to pad above and below eyeL
      -- TODO Performance: use TN.withSomeSNat and rewrite with Shaped to avoid O(n) penalty
      eyeL = D.generate [l',l'] (\[i,j] → if i == j then one else zero)
      padZ = D.pad [topBotPads, (0,0)] zero eyeL
  in  C.convert padZ


padSr2 ∷ ∀ l n a.
      ( KnownNat l, KnownNat n, Semiring a)
      ⇒ Finite ((n - l) + 1)          -- ^ The index to inject a slice into.
      → Sr2 R1 l n a a
padSr2 = sr2 ∘ padA2


{- | This morphism injects a single value into an /n/-product.

Near-synonym for 'hot'. -}
injA2 ∷ ∀ n a.
      ( KnownNat n, 1 <= n, Semiring a )
      ⇒ Finite n         -- ^ The index to inject a single object into.
      → Array '[n,1] a
injA2 = A.reshape ∘ hot
-- injA2 = padA2


injSr2 ∷ ∀ n a.
      ( KnownNat n, 1 <= n, Semiring a )
      ⇒ Finite n         -- ^ The index to inject a single object into.
      → Sr2 R1 1 n a a
injSr2 = sr2 ∘ injA2
-- injSr2 = padSr2


{- | Select an /l/-slice from /n/ inputs with the slice starting at a particular
index. -}
selA2 ∷ ∀ l n a.
      (KnownNat l, KnownNat n, Semiring a)
      ⇒ Finite ((n - l) + 1)   -- ^ The starting index of the length /l/ "slice".
      → Array [l,n] a
selA2 = A.transpose @[1,0]
      ∘ flip mulA2sr eye
      ∘ padA2


selSr2 ∷ ∀ l n a.
       (KnownNat l, KnownNat n, Semiring a)
       ⇒ Finite ((n - l) + 1)   -- ^ The starting index of the length /l/ "slice".
       → Sr2 R1 n l a a
selSr2 = sr2 ∘ selA2



dupSr2 ∷ ∀ n s a.
       ( KnownNat n, KnownNat s, 1 <= s, Semiring a )
       ⇒ Sr2 R1 n (s * n) a a
dupSr2 = sr2 dupA2


dupSr2' ∷ ∀ n s a.
        ( KnownNat n, KnownNat s, 1 <= s, Semiring a )
        ⇒ Sr2 R1 n (s * n) a a
dupSr2' = sr2 dupA2'


{- | Replicate an /n/-length input by making /s/ copies of each of the /n/ inputs,
where each replicate is in a contiguous block with its "clones" — relative order
(position) in the input is conserved in the output.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> three = iota @3 @Int
>>> pp three
┌─────┐
│0 1 2│
└─────┘
>>> pp $ F.fmap getSum $ A.reshape @'[6] $ mulA2sr (dupA2 @3 @2) (A.reshape $ Sum <$> three)
┌───────────┐
│0 0 1 1 2 2│
└───────────┘
-}
dupA2 ∷ ∀ n s a.
      ( KnownNat n, KnownNat s, 1 <= s, Semiring a )
      ⇒ Array '[s * n, n] a
dupA2 = A.reshape
      ∘ A.transpose @[1,0]
      ∘ A.stretchOuter
      ∘ A.reshape @[1,n,n]
      $ eye @n


{- | Replicate an /n/-length input by concatenating /s/ /n/-length copies of the
input side by side: relative order (position) in the input is only conserved
/within/ each of the /s/ copies.

>>> import Text.PrettyPrint.HughesPJClass (prettyShow)
>>> pp = putStrLn . prettyShow :: (Pretty a) => a -> IO ()
>>> import Data.Array.Shaped (Array, reshape, iota, transpose)
>>> import qualified Data.Array.Shaped as A
>>> three = iota @3 @Int
>>> pp three
┌─────┐
│0 1 2│
└─────┘
>>> pp $ F.fmap getSum $ A.reshape @'[6] $ mulA2sr (dupA2' @3 @2) (A.reshape $ Sum <$> three)
┌───────────┐
│0 1 2 0 1 2│
└───────────┘
-}
dupA2' ∷ ∀ n s a.
       ( KnownNat n, KnownNat s, 1 <= s, Semiring a )
       ⇒ Array '[s * n, n] a
dupA2' = A.reshape
       ∘ A.stretchOuter
       ∘ A.reshape @[1,n,n]
       $ eye @n

{- | The matrix such that, /∀ n ∷ Nat, n ≥ 1/, /∀ i ∷ Finite n/, and semirings /a/:

>>> mulA2sr (jamA2 @n @a) (injA2 @n i) ≡ eye @1 @a
-}
jamA2 ∷ ∀ n a.
      ( KnownNat n, Semiring a )
      ⇒ Array '[1,n] a
jamA2 = ones


jamSr2 ∷ ∀ n a.
      ( KnownNat n, Semiring a )
      ⇒ Sr2 R1 n 1 a a
jamSr2 = sr2 jamA2







-- TODO Consider making this an open type family
{- | See 'SrN' for context.

>>> :k! Nest Int R1 '[]
Nest Int R1 '[] :: Type
= Int
>>> :k! Nest Int R1 '[2,3]
Nest Int R1 '[2,3] :: Type
= R1 2 (R1 3 Int)
-}
type family Nest (c ∷ Type) (φ ∷ Nat → Type → Type) (shape ∷ [Nat]) ∷ Type where
  Nest c R1 '[]      = c
  Nest c R1 (n : sh) = R1 n (Nest c R1 sh)


-- TODO Consider making this an open type family
{- | See 'SrN' for context.

>>> :k! UnNest Int R1 Int
UnNest Int R1 Int :: [GHC.Num.Natural.Natural]
= '[]
>>> :k! UnNest Int R1 (R1 2 (R1 3 Int))
UnNest Int R1 (R1 2 (R1 3 Int)) :: [GHC.Num.Natural.Natural]
= [2, 3]
-}
type family UnNest (c ∷ Type) (φ ∷ Nat → Type → Type) (nest ∷ Type) ∷ [Nat] where
  UnNest c R1       c  = '[]
  UnNest c R1 (R1 n a) = (n : (UnNest c R1 a))

-- {- | See 'SrN' for context.
-- -}
-- type FlatHalf (c ∷ Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (nest ∷ Type) ∷ [Nat] = (n : (UnNest c R1 a))
-- type family FlatHalf (c ∷ Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (nest ∷ Type) ∷ [Nat] where
--   FlatHalf c R1 n a  = (n : (UnNest c R1 a))

-- type family Flat (c ∷ Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (ins ∷ Type) (outs ∷ Type) ∷ [Nat] where
--   Flat c R1 n m a b  = (FlatHalf c R1 n a) ++ (FlatHalf c R1 m b)

{- | A type synoynm for a cluster of constraints frequently needed with 'SrN'. -}
type UnNesting (s ∷ Type) (φ ∷ Nat → Type → Type) (outermost ∷ Nat) (nested ∷ Type) (dims ∷ [Nat]) =
  ( KnownNat outermost
  , dims ~ outermost : (UnNest s φ nested)
  , KnownNat (A.Rank dims)
  , Shape dims
  -- , Shape (UnNest s φ nested)
  )

{- | A type synoynm for a cluster of constraints frequently needed with 'SrN'. -}
type UnNestings (s ∷ Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type) (ins ∷ [Nat]) (outs ∷ [Nat]) =
  ( UnNesting s φ n a ins
  , UnNesting s φ m b outs
  , Shape (UnNest s φ b ++ UnNest s φ a)
  )


{- | This newtype wraps a multidimensional @orthotope@ 'Array' of rank ≥ 2 and (in
conjunction with type families and a smart constructor) presents it as though it
were actually constructed as an explicitly nested array-of-arrays:

=== Motivation

A morphism

> f ∷ R1 4 (R1 5 a) -| (Sized (->)) R1 2 3 |-> R1 6 (R1 7 a)

is a function to and from three layers of explicitly nested 'Array's (wrapped in
'R1'):

> unSized f ∷ R1 2 (R1 4 (R1 5 a)) -> R1 3 (R1 6 (R1 7 a))

This does not take advantage of any of the affordances that 'orthotope' offers
for /n/-dimensional arrays.

In contrast, the analogous morphism

> f' ∷ R1 4 (R1 5 a) -| (SrN a) R1 2 3 |-> R1 6 (R1 7 a)

unwraps to

> unSrn f' ∷ Array (3 : 2 : [6,7] ++ [4,5]) a

=== Consequences

'R1' is a phantom type that represents a fictive product functor: every morphism
like @f'@ above is isomorphic to a morphism where 'R1' is actually used with
explicit nesting. This offers the benefits of @orthotope@'s facilities for
/n/-dimensional arrays while fitting in with at least most of the rest of the
package, including — critically — morphism composition.

Note that an 'SrN'-wrapped 'Array' represents a decision to divide up the
dimensions of an 'Array' in a specific way for composition (tensor contraction),
and there is a convention for the order of dimensions in the wrapped array.

The smart constructor @srN@ has two leading type arguments for indicating the
rank of the source and target.

One downside of this use of type families is that 'SrN' does not currently have
a 'Functor' instance; I suspect there may be other consequences.


=== 'SrN' is not a closed category

Note also that because of the relationship between types and the definition of
composition, there are some things this type *can't* express. Consider

>>> stackedG = (A.reshape $ A.iota) ∷ Array [2,3,4, 6, 5,7] Int
>>> stackedF = (A.reshape $ A.iota) ∷ Array [2,3,4, 8, 6  ] Int

We *could* think about these two arrays as /2✕3✕4/ stacks of morphisms that we
could contract (compose) along the dimension /6/ to yield a /2✕3✕4✕8✕5✕7/, but
try to hammer this into the type of 'SrN': where would /2✕3✕4/ go, what would
that have to mean for composition?

Could it be a common prefix of the source and target?

>>> stackedG' = ... ∷ SrN Int R1 2 2 (R1 3 (R1 4 (R1 5 (R1 7 Int)))) (R1 3 (R1 4 (R1 6 Int)))
>>> stackedF' = ... ∷ SrN Int R1 2 2 (R1 3 (R1 4 (R1 6 Int))) (R1 3 (R1 4 (R1 8 Int)))

If we composed @stackedG' ∘ stackedF'@, we would have to contract along a shared
set of dimensions of shape @[2,3,4,6]@, and yet the resulting morphism would
*also* still have to have @[2,3,4,5,7]@ as the shape of the source and
@[2,3,4,8]@ as the shape of the target: that doesn't make sense.

(@[2,3,4,6]@ also couldn't be a common suffix for similar reasons.)

A more concise way of putting this is that if @SrN@ represents all of the
morphisms in some category, that category is not /closed/: its morphisms aren't
objects that we can take products of, and that's because a product of morphisms
is simply not expressible by design. (When support for closed categories is
added, a generalization of @SrN@ supporting such products of morphisms will be
added.)


=== Examples

>>> ex = (A.reshape $ A.iota) ∷ Array '[3,2,4,5] Int
ex :: Array [3, 2, 4, 5] Int
>>> pp ex
┌───────────────────┐
│  0   1   2   3   4│
│  5   6   7   8   9│
│ 10  11  12  13  14│
│ 15  16  17  18  19│
│                   │
│ 20  21  22  23  24│
│ 25  26  27  28  29│
│ 30  31  32  33  34│
│ 35  36  37  38  39│
│                   │
│                   │
│ 40  41  42  43  44│
│ 45  46  47  48  49│
│ 50  51  52  53  54│
│ 55  56  57  58  59│
│                   │
│ 60  61  62  63  64│
│ 65  66  67  68  69│
│ 70  71  72  73  74│
│ 75  76  77  78  79│
│                   │
│                   │
│ 80  81  82  83  84│
│ 85  86  87  88  89│
│ 90  91  92  93  94│
│ 95  96  97  98  99│
│                   │
│100 101 102 103 104│
│105 106 107 108 109│
│110 111 112 113 114│
│115 116 117 118 119│
└───────────────────┘
>>> ex1 = srN @1 @1 ex
ex1 :: SrN Int R1 2 3 (R1 5 Int) (R1 4 Int)
>>> ex2 = srN @2 ex
ex2 :: SrN Int R1 2 3 Int (R1 4 (R1 5 Int))
>>> ex3 = srN @0 ex
ex3 :: SrN Int R1 2 3 (R1 4 (R1 5 Int)) Int
>>> tw322 = (A.reshape $ A.iota @12) ∷ Array '[3,2,2] Int
>>> pp tw322
┌─────┐
│ 0  1│
│ 2  3│
│     │
│ 4  5│
│ 6  7│
│     │
│ 8  9│
│10 11│
└─────┘
>>> tw322₁ = srN @1 @0 tw322
tw322₁ :: SrN Int R1 2 3 (R1 2 Int) Int
>>> tw322₂ = srN @0 @1 tw322
tw322₂ :: SrN Int R1 2 3 Int (R1 2 Int)
-}
newtype SrN (c ∷ Type) (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type)
  = SrN { getSrN ∷ Array (m ': n ': ((UnNest c φ b) ++ (UnNest c φ a))) c }
  deriving stock (Generic)


deriving instance ( Eq c
                  , Shape (UnNest c φ b ++ UnNest c φ a)
                  , KnownNat n, KnownNat m
                  )
  ⇒ Eq (SrN c φ n m a b)
deriving instance ( Ord c
                  , Shape (UnNest c φ b ++ UnNest c φ a)
                  , KnownNat n, KnownNat m
                  )
  ⇒ Ord (SrN c φ n m a b)
deriving instance ( Show c
                  , Shape (UnNest c φ b ++ UnNest c φ a)
                  , KnownNat n, KnownNat m
                  )
  ⇒ Show (SrN c φ n m a b)


-- class NestingOf (sh ∷ [Nat]) (c ∷ Type) (φ ∷ Nat → Type → Type) (a ∷ Type)
-- instance (sh ~ UnNest c R1 a) ⇒ NestingOf sh c φ a


{- | Sugar for @coerce ∘ Prelude.fmap ∘ coerce@ that permits use of the functor instance
for 'Array' on an 'SrN' value.

>>> g' = A.reshape $ A.iota ∷ Array [4,3, 7, 5,6] Int
g' :: Array [4, 3, 7, 5, 6] Int
>>> f' = A.reshape $ A.iota ∷ Array [3,2, 5,6, 4] Int
f' :: Array [3, 2, 5, 6, 4] Int
>>> g = srN @1 @2 $ Sum <$> g'
g :: SrN (Sum Int) R1 3 4 (R1 5 (R1 6 (Sum Int))) (R1 7 (Sum Int))
>>> f = srN @2 @1 $ Sum <$> f'
f :: SrN (Sum Int) R1 2 3 (R1 4 (Sum Int)) (R1 5 (R1 6 (Sum Int)))
>>> :t mapSrN getSum (mulSrN g f)
mapSrN getSum (mulSrN g f) :: SrN Int R1 2 4 (R1 4 Int) (R1 7 Int)
-}
mapSrN ∷ ∀ s r n m a b a' b' outs ins.
      ( KnownNat n
      , KnownNat m
      , Shape (UnNest s R1 b ++ UnNest s R1 a)
      , outs ~ UnNest s R1 b
      , ins  ~ UnNest s R1 a
      , a' ~ Nest r R1 ins
      , b' ~ Nest r R1 outs
      )
      ⇒ (s → r)
      → SrN s R1 n m a  b
      → SrN r R1 n m a' b'
mapSrN f = coerce ∘ F.fmap @(Array (m : n : (UnNest s R1 b) ++ (UnNest s R1 a))) f ∘ coerce




-- TODO lOut,lIn are relatively implementation-tied: consider
--  - Switching the order.
--  - Tweaking the meaning: 'lIn'/'lout' should indicate the *total* size of the
--    source/target — 1 greater than what they mean now.
{- | Smart constructor for 'SrN'. Use the two leading type arguments @lOut@ and
@lIn@ to indicate the rank of extra dimensions after the first two for the
target and source (respectively).

>>> g = A.reshape $ A.iota ∷ Array [4,2, 5,6, 3] Int
>>> g' = srN @2 @1 $ Sum <$> g ∷ R1 3 (Sum Int) -| SrN (Sum Int) R1 2 4 |-> R1 5 (R1 6 (Sum Int))
-}
srN ∷ ∀ lOut lIn n m ins outs c.
   ( KnownNat n, KnownNat m
   , SplitAt lOut outs ins
   , (UnNest c R1 (Nest c R1 outs) ++ UnNest c R1 (Nest c R1 ins))
   ~ (outs ++ ins)
   )
   ⇒ Array (m ': n ': (outs ++ ins)) c             -- ^ The tensor to treat as a morphism.
   → SrN c R1 n m (Nest c R1 ins) (Nest c R1 outs)
srN = SrN


{- | Unwrapper for 'SrN' that can help with type inference. -}
unSrN ∷ ∀ n m a b c.
         ( KnownNat n, KnownNat m )
         ⇒ SrN c R1 n m a b
         → Array (m : n : (UnNest c R1 b ++ UnNest c R1 a)) c
unSrN = getSrN
