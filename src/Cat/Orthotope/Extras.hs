{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- see comments on takeA, dropA
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
available from @orthotope@ can (constraints aside) conveniently express many
useful operations on homogeneously nested finite, traversable, etc. monoidal
products ("multidimensional arrays") that would normally be expressed using a
slew of much more polymorphic combinators on arbitrarily heterogeneous
compositions (nestings) of functors in a language like Haskell.


== This module

The main rationale for this module is supporting "Cat.Orthotope".

Notably lacking at the moment are type synonyms, constraints, or type families
to cut down on the clutter of constraints related to transpositions that appear
in "Cat.Orthotope".
-}

module Cat.Orthotope.Extras
  ( -- * Functions for working with @orthotope@ arrays
    -- |
    --
    -- Besides functions for pretty-printing and indexing, note that there are
    -- currently also orphan instances for 'Representable' and functions reliant
    -- on the 'Representable'-parameterized 'Store' 'Comonad' from the
    -- 'adjunctions' package.

    pp
  , vappend
  , happend
    -- ** Indexing
  , innerIndex
  , ginnerIndex
  , outerIndex
  , shapeToStrides
  , stridesToShape
  , coordsOf
  , indexes
  , indexes'
  , CoordsError (Short, Long, NegIdx, Bounds)
    -- *** Safe alternatives to @index@ or @indexes@ for specific ranks
  , index1
  , index2
  , index3
  , index4
  , index5
  , index6
  , index7
  , index1'
  , index2'
  , index3'
  , index4'
  , index5'
  , index6'
  , index7'
    -- ** Subarrays
    -- |
    -- The @orthotope@ API currently provides a fairly small API for working
    -- with subarrays, especially if you want more than views. The functions
    -- below have not been optimized at all; they are intended to scaffold
    -- implementation of tensor contractions along more than one index of
    -- /n/-dimensional tensors.
  , subarraysL
  , subarrays
  , unravelN
  , ravelN
  , sufgenerate
  , pregenerate
  , subindexes
  , getSubindex
  , setSubindex
  , isubmap
    -- ** Permutation helpers
  , slipNr
  , slipNl
    -- ** Type-level machinery
    -- |
    -- These type tynonyms reduce constraint clutter.
  , SplitAt
  , Prefix
  , Suffix
    -- ** 'Store' comonad helpers
  , Pointed
  , PointedT
  , pointed
  , unPointed
  , pointedT
  , unPointedT
  , stencil
  , tabulate'
    -- ** 'Store' comonad re-exports
  , Representable (Rep, index, tabulate)
  , Comonad ( extract
            , duplicate
            , extend
            )
  , (<<=)
  , (=>>)
  , (=<=)
  , (=>=)
  , liftW
  , liftW2
  , Store
  , StoreT (StoreT)
  , ComonadStore ( pos
                 , peek
                 , peeks
                 , seek
                 , seeks
                 , experiment
                 )
    -- ** Finite re-export
  , Finite
  ) where

{- TODO

 - Continue to move scattered instance implementations for 'R1' into explicit
   functions and gather them here.

 - Introduce type synonyms or typeclass to make the constraints related to
   permutations/transpositions easier to read and less tedious to write/work
   with in downstream functions.

 - A variation on rerank2 where the arguments don't need to have exactly the
   same outer shape might go a long way in this module and in @Cat.Orthotope@.
-}

import Prelude qualified as P
import Prelude hiding
  ( Functor
  , fmap
  , zip
  , zipWith
  )
import Prelude.Unicode
  ( (∘)
  )
import Data.Function
  ( (&)
  )
import Data.Composition
  ( (.:)
  , (.:.)
  )
import Control.Arrow.Unicode
  ( (⁂)
  )
import Control.Arrow
  ( (&&&)
  , (>>>)
  , first
  )

import GHC.Generics
  ( Generic
  )
import Data.Data
  ( Proxy (Proxy)
  )
import GHC.TypeNats
  ( Nat
  , pattern SNat
  , KnownNat
  , type (+)
  , natVal
  )
import Data.Finite
  ( Finite
  )


import Data.Bool   (bool)
import Data.Either (lefts)
import Data.Maybe  (fromJust)
import Control.Applicative
  ( ZipList ( ZipList
            , getZipList
            )
  )


import Data.Functor     qualified as F
import Data.Functor.Identity
  ( Identity (Identity)
  )
import Control.Comonad
  ( Comonad ( extract
            , duplicate
            , extend
            )
  , (<<=)
  , (=>>)
  , (=<=)
  , (=>=)
  , liftW
  , liftW2
  )
import Control.Comonad.Representable.Store
    ( ComonadStore ( pos
                   , peek
                   , peeks
                   , seek
                   , seeks
                   , experiment
                   )
    , Store
    , StoreT (StoreT)
    , store
    -- , runStore
    )

import Data.Functor.Rep  (Representable, Rep)
import Data.Distributive (Distributive, distribute)
import Data.Functor.Rep   qualified as R
import Data.List          qualified as L
import Data.Vector        qualified as V
import Data.Array.Dynamic qualified as D
import Data.Array.Shaped  qualified as A
import Data.Array.Shaped
  ( Array
  , transpose
  , Shape
  -- , Rank
  -- , rerank
  -- , unravel
  -- , ravel
  , generate
  )

import Data.Array.Internal (subArraysT, T(..), vConcat)
import Data.Array.Internal.Shape (Take, Drop, type (++))
-- import Data.Array.Internal.Shape   qualified as Sh
import Data.Array.Internal.Shaped  qualified as S
import Data.Array.Internal.ShapedG qualified as G

import Text.PrettyPrint.HughesPJClass
  ( Pretty
  , prettyShow
  )



type SplitAt (n ∷ Nat) (l ∷ [Nat]) (r ∷ [Nat]) =
  ( Shape (l ++ r)
  , A.Rank l ~ n
  , Take n (l ++ r) ~ l
  , Drop n (l ++ r) ~ r
  , KnownNat n
  )

type Suffix (n ∷ Nat) (l ∷ [Nat]) (r ∷ [Nat]) =
  ( Shape (l ++ r)
  , A.Rank l ~ n
  , Drop n (l ++ r) ~ r
  , KnownNat n
  )

type Prefix (n ∷ Nat) (l ∷ [Nat]) (r ∷ [Nat]) =
  ( Shape (l ++ r)
  , A.Rank l ~ n
  , Take n (l ++ r) ~ l
  , KnownNat n
  )



-- Utilities for orthotope internal-bookkeeping


getG ∷ Array sh a → G.Array sh V.Vector a
getG (S.A g) = g

getT ∷ G.Array sh V.Vector a → T V.Vector a
getT (G.A t) = t

getGT ∷ Array sh a → T V.Vector a
getGT = getT ∘ getG



subarraysRaw ∷ Array sh a → [Int] → [T V.Vector a]
subarraysRaw a pre = subArraysT pre $ getGT a

-- subarraysG ∷ ∀ n sh sh' a.
--                  (KnownNat n, Shape sh, Shape sh', Drop n sh ~ sh')
--                ⇒ Array sh a → [G.Array sh' V.Vector a]
-- subarraysG = F.fmap G.A
--            ∘ (subarraysRaw <*> (take (fromIntegral $ natVal $ SNat @n) ∘ A.shapeL))


-- TODO Refactor: Defining this in terms of @slice@ rather than @subArraysT@ is
-- a better idea:
--  1. @slice@ is part of the public API, @subArraysT@ is not.
--  2. @slice@ gives you an @Array@ back.
{- | Given @arr ∷ Array sh a@, @n ∷ Nat ≤ Rank sh@, @subarraysL \@n arr@ returns a
list of @arr@'s subarrays @n@ levels down. See also 'rerank'.

Note this currently relies on parts of @orthotope@'s internal API, and hence so
do 'subarrays', 'unravelN', 'isubmap', 'subindexes', 'getSubindex',
'setSubindex'. -}
subarraysL ∷ ∀ n sh sh' a.
           (KnownNat n, Shape sh, Shape sh', Drop n sh ~ sh')
           ⇒ Array sh a → [Array sh' a]
subarraysL = F.fmap (S.A ∘ G.A)
           ∘ (subarraysRaw <*> (take (fromIntegral $ natVal $ SNat @n) ∘ A.shapeL))


{- | Mildly shape-polymorphic variation on 'unravel': @subarrays \@n arr@
yields the array of subarrays of @arr@ @\n@ levels down. -}
subarrays ∷ ∀ n sh i o a.
          (KnownNat n, Shape sh, Shape i, Shape o, Drop n sh ~ i, Take n sh ~ o)
          ⇒ Array sh a → Array o (Array i a)
subarrays = A.fromList ∘ subarraysL @n


{- | Synonym for 'subarrays'. Inverse of 'ravelN'. Compare with @orthotope@'s
'ravel'. -}
unravelN ∷ ∀ n sh i o a.
          (KnownNat n, Shape sh, Shape i, Shape o, Drop n sh ~ i, Take n sh ~ o)
          ⇒ Array sh a → Array o (Array i a)
unravelN = subarrays @n


{- | Inverse of 'unravelN'. Compare with @orthotope@'s 'unravel'. -}
ravelN ∷ ∀ n sh i o a.
       (KnownNat n, Shape sh, Shape i, Shape o, Drop n sh ~ i, Take n sh ~ o)
       ⇒ Array o (Array i a) → Array sh a
ravelN = A.fromVector
       ∘ vConcat
       ∘ F.fmap A.toVector
       ∘ A.toList



{- | @innerIndex strides offset i@ finds the first index in a flattened internal
vector of item @i@ of the outermost dimension of an array. -}
innerIndex ∷ [Int] → Int → Int → Int
innerIndex strides offset i = offset + i*(strides L.!! 0)


{- | @ginnerIndex strides offset [i,j,k,...]@ finds the first index in a flattened
internal vector of the item with coordinates @[i,j,k,...]@ of an array. -}
ginnerIndex ∷ [Int] → Int → [Int] → Int
ginnerIndex strides offset coords = offset + dotL strides coords


{- | @outerIndex size strides offset i@ yields the coordinates that an inner index
@i@ into the inner flat vector corresponds to. This is essentially a
change-of-base calculation from a base-10 numeral (@i@) to a "numeral" where
(neglecting the offset) the "bases" are given by the @strides@.

>>> as = A.reshape @'[5,2,4] $ A.iota @40 @Int
>>> shapeToStrides 40 [5,2,4]
[8,4,1]
>>> pp as
┌───────────┐
│ 0  1  2  3│
│ 4  5  6  7│
│           │
│ 8  9 10 11│  -- 10 is @ [1,0,2] in the 'Array' and 10 in the internal vector
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
>>> outerIndex 40 (shapeToStrides 40 [5,2,4]) 0 10
[1,0,2]
>>> pp $ head ∘ reverse $ subarraysL @1 as
┌───────────┐  -- subarray with strides [4,1] and offset 32
│32 33 34 35│  -- 34 is @ [0,2] in the 'Array' and 34 in the internal vector
│36 37 38 39│
└───────────┘
>>> outerIndex 8 [4,1] 32 34
[0,2]
>>> outerIndex 8 [4,1] 0 2
[0,2]
-}
outerIndex ∷ Int → [Int] → Int → Int → [Int]
outerIndex size strides _ i =  -- The offset doesn't seem to actually be necessary
  -- Notes:
  --  1. qj is the previous stride length
  --  2. The initial "previous" stride length is the size because, for any index
  --     @i@ into an array of length @size@, @i `mod` size = i@, and that's what
  --     you want to start off.
  let δ i_ (qj, cs) x = (x, ((i_ `mod` qj) `div` x) : cs)
  in  L.reverse ∘ snd $ L.foldl (δ i) (size, []) strides



{- | @shapeToStrides size shape@ yields the strides of an array with the given
size and shape:

>>> shapeToStrides 40 [5,2,4] = [8,4,1]  -- [40/5, 40/5/2, 40/5/2/4]
-}
shapeToStrides ∷ Int → [Int] → [Int]
shapeToStrides size = F.fmap round
                    ∘ tail ∘ L.scanl (/) (fromIntegral @Int @Double size)
                    ∘ F.fmap fromIntegral


{- | @stridesToShape size strides@ yields the shape of an array with the given
size and strides:

>>> stridesToShape 40 [8,4,1] = [5,2,4]  -- [40/8, 8/4, 4/1]
-}
stridesToShape ∷ Int → [Int] → [Int]
stridesToShape size strides =
  let xs = fromIntegral size : ys   ∷ [Double]
      ys = fromIntegral <$> strides ∷ [Double]
  in  F.fmap round $ getZipList $ ((/) <$> ZipList xs) <*> ZipList ys



{- | Generate the set of possible ("outer") coordinates into an /n/-dimensional
@orthotope@ array with the given shape. -}
coordsOf ∷ ∀ sh. (Shape sh) ⇒ [[Int]]
coordsOf =
  let size_     = A.sizeP  $ Proxy @sh
      shape_    = A.shapeP $ Proxy @sh
      strides_  = shapeToStrides size_ shape_
      innerIdxs = [0..(size_ - 1)]
  in outerIndex size_ strides_ 0 <$> innerIdxs




index1 ∷ ∀ n sh a.
       (KnownNat n)
       ⇒ Array (n ': sh) a
       → Finite n
       → Array sh a
index1 a = A.index a ∘ fromIntegral

index2 ∷ ∀ n m sh a.
       (KnownNat n, KnownNat m)
       ⇒ Array (n ': m ': sh) a
       → Finite n
       → Finite m
       → Array sh a
index2 a = uncurry (&)
         ∘ (A.index a ∘ fromIntegral ⁂ flip A.index ∘ fromIntegral)
        .: (,)

index3 ∷ ∀ n m o sh a.
       (KnownNat n, KnownNat m, KnownNat o)
       ⇒ Array (n ': m ': o ': sh) a
       → Finite n
       → Finite m
       → Finite o
       → Array sh a
index3 a =  uncurry (&)
         ∘  (uncurry (index2 a) ⁂ index1')
        .:. (,)
        .:  (,)

index4 ∷ ∀ n m o p sh a.
       (KnownNat n, KnownNat m, KnownNat o, KnownNat p)
       ⇒ Array (n ': m ': o ': p ': sh) a
       → Finite n
       → Finite m
       → Finite o
       → Finite p
       → Array sh a
index4 a n m o p = index1' p $ index3 a n m o


index5 ∷ ∀ n m o p q sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q)
        ⇒ Array (n ': m ': o ': p ': q ': sh) a
        → Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Array sh a
index5 a n m o p q = index1' q $ index4 a n m o p

index6 ∷ ∀ n m o p q r sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q, KnownNat r)
        ⇒ Array (n ': m ': o ': p ': q ': r ': sh) a
        → Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Finite r
        → Array sh a
index6 a n m o p q r = index1' r $ index5 a n m o p q

index7 ∷ ∀ n m o p q r s sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q, KnownNat r, KnownNat s)
        ⇒ Array (n ': m ': o ': p ': q ': r ': s ': sh) a
        → Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Finite r
        → Finite s
        → Array sh a
index7 a n m o p q r s = index1' s $ index6 a n m o p q r




index1' ∷ ∀ n sh a.
        (KnownNat n)
        ⇒ Finite n
        → Array (n ': sh) a
        → Array sh a
index1' = flip A.index ∘ fromIntegral

index2' ∷ ∀ n m sh a.
        (KnownNat n, KnownNat m)
        ⇒ Finite n
        → Finite m
        → Array (n ': m ': sh) a
        → Array sh a
index2' = uncurry (>>>)
        ∘ (flip A.index ∘ fromIntegral ⁂ flip A.index ∘ fromIntegral)
       .: (,)

index3' ∷ ∀ n m o sh a.
        (KnownNat n, KnownNat m, KnownNat o)
        ⇒ Finite n
        → Finite m
        → Finite o
        → Array (n ': m ': o ': sh) a
        → Array sh a
index3' =  uncurry (>>>)
        ∘  (uncurry index2' ⁂ index1')
       .:. (,)
       .:  (,)

index4' ∷ ∀ n m o p sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p)
        ⇒ Finite n
        → Finite m
        → Finite o
        → Finite p
        → Array (n ': m ': o ': p ': sh) a
        → Array sh a
index4' n m o p = index1' p ∘ index3' n m o

index5' ∷ ∀ n m o p q sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q)
        ⇒ Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Array (n ': m ': o ': p ': q ': sh) a
        → Array sh a
index5' n m o p q = index1' q ∘ index4' n m o p

index6' ∷ ∀ n m o p q r sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q, KnownNat r)
        ⇒ Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Finite r
        → Array (n ': m ': o ': p ': q ': r ': sh) a
        → Array sh a
index6' n m o p q r = index1' r ∘ index5' n m o p q

index7' ∷ ∀ n m o p q r s sh a.
        (KnownNat n, KnownNat m, KnownNat o, KnownNat p, KnownNat q, KnownNat r, KnownNat s)
        ⇒ Finite n
        → Finite m
        → Finite o
        → Finite p
        → Finite q
        → Finite r
        → Finite s
        → Array (n ': m ': o ': p ': q ': r ': s ': sh) a
        → Array sh a
index7' n m o p q r s = index1' s ∘ index6' n m o p q r



-- TODO Consider rewrite in terms of 'Data.Array.Internal' primitives
{- | @orthotope@ does not offer a way to index into more than the outermost
dimension of an /n/-dimensional (rank /n/) 'Array'. I.e., given
@xs ∷ Array [2,3,4] Int@, there's no way to give a complete coordinate (e.g.
@[1,2,1]@) to access a particular value for arbitrary shape arrays.

@indexes xs coords@ does just this, returning @Nothing@ if the list of
coordinates is too short or any coordinate is out of bounds, and returning @Just@
an @a@ otherwise.

Note that without type-heterogeneous lists, the safest alternatives to this you
ould define would be a size-indexed functor of 'Int's or one of 'Finite n's for
whatever the largest dimension 'n' is. See also 'index1', 'index2', 'index3',
etc. for safer alternatives for specific ranks. -}
indexes ∷ ∀ sh a. (Shape sh) ⇒ Array sh a → [Int] → Maybe a
indexes a coords
  | length (A.shapeP (Proxy @sh)) /= length coords           = Nothing
  | any (uncurry (<=)) (P.zip (A.shapeP (Proxy @sh)) coords) = Nothing
  | otherwise =
    let δ q@(     _, []   ) _ = q
        δ   (offset, s':s_) i = (dimOffsets offset s' (product s_) !! i, s_)
        q₀ sh' = (0, sh')
        s      = A.shapeP (Proxy @sh)
        v      = A.toVector a
        idx    = fst (L.foldl' δ (q₀ s) coords)
    in Just $ v V.! idx


{- | ≈ Hadamard (elementwise) product of two lists.

No attempt is made to control for matched lengths. -}
hadL ∷ ∀ a. Num a ⇒ [a] → [a] → [a]
hadL xs ys = getZipList $ ((*) <$> ZipList xs) <*> ZipList ys


{- | ≈ Dot product of two lists.

No attempt is made to control for matched lengths. -}
dotL ∷ ∀ a. Num a ⇒ [a] → [a] → a
dotL = sum .: hadL


dimOffsets ∷ Int → Int → Int → [Int]
dimOffsets i l s = (+ i) <$> hadL [0 ∷ Int .. (l - 1)] (repeat s)
  -- let dotL xs ys = getZipList $ ((*) <$> ZipList xs) <*> ZipList ys
  -- in (+ i) <$> dotL [0 ∷ Int .. (l - 1)] (repeat s)


{- | Variant of 'indexes' that produces more informative errors. -}
indexes' ∷ ∀ sh a. (Shape sh) ⇒ Array sh a → [Int] → Either [CoordsError] a
indexes' = uncurry (>>)
         ∘ ((validCoords (Proxy @sh) ∘ snd) &&& (return ∘ fromJust ∘ uncurry indexes ))
        .: (,)


{- | For each of the four constructors

 - The 'ShapeL' (≡ [Int]) is the relevant shape of the 'Array' from the
   error-generating call.
 - The second item is the specific set of coordinates ("index") that the
   error-generating call tried to access or provide.
-}
data CoordsError =
    Short  !A.ShapeL ![Int] !Int  -- ^ Last Int indicates how many values short the list of coordinates is.
  | Long   !A.ShapeL ![Int] !Int  -- ^ Last Int indicates how many values extra the list of coordinates is.
  | NegIdx !A.ShapeL ![Int] !Int  -- ^ Last Int indicates the coordinate index that is negative.
  | Bounds !A.ShapeL ![Int] !Int  -- ^ Last Int indicates the coordinate index that is out of bounds.
  deriving stock (Eq, Ord, Show, Read, Generic)


short ∷ ∀ sh. (Shape sh) ⇒ Proxy sh → [Int] → Either [CoordsError] ()
short sh cs =
  let s    = A.shapeP sh
      lsh  = length s
      lcs  = length cs
      diff = lcs - lsh
  in  bool (Left . pure $ Short s cs diff) (Right ()) (diff < 0)


long ∷ ∀ sh. (Shape sh) ⇒ Proxy sh → [Int] → Either [CoordsError] ()
long sh cs =
  let s    = A.shapeP sh
      lsh  = length s
      lcs  = length cs
      diff = lcs - lsh
  in  bool (Left . pure $ Long s cs diff) (Right ()) (diff > 0)


bounds ∷ ∀ sh. (Shape sh) ⇒ Proxy sh → [Int] → Either [CoordsError] ()
bounds sh cs =
  let s    = A.shapeP sh
      idxs = P.zipWith P.const [0..] cs
      ics  = zipWith3 (\i c s' → (i,c,s', s' <= (c + 1))) idxs cs s
      oobs = filter (\(_,_,_,b) → b) ics
      mkErr (i,_,_,_) = Bounds s cs i
      errs = mkErr <$> oobs
  in  bool (Left errs) (Right ()) (not $ null errs)


negIdxs ∷ ∀ sh. (Shape sh) ⇒ Proxy sh → [Int] → Either [CoordsError] ()
negIdxs sh cs =
  let s    = A.shapeP sh
      idxs = P.zipWith P.const [0..] cs
      ic   = P.zipWith (\i c → (i,c, c < 0)) idxs cs
      negs = filter (\(_,_,b) → b) ic
      mkErr (i,_,_) = NegIdx s cs i
      errs = mkErr <$> negs
  in  bool (Left errs) (Right ()) (not $ null errs)


validCoords ∷ ∀ sh. (Shape sh) ⇒ Proxy sh → [Int] → Either [CoordsError] ()
validCoords sh cs =
  let fs   = uncurry <$> [short, long, bounds, negIdxs]
      errs = concat . lefts $ fs <*> [(sh,cs)]
  in  bool (Left errs) (Right ()) (not $ null errs)



instance (Shape sh) ⇒ Distributive (Array sh) where
  distribute = R.distributeRep

{- | NOTE: 'index' is unsafe, and only use of sized heterogeneously-typed
collections could change this. For particular ranks, the 'indexes1',
'indexes2', ... are safe alternatives.

> tabulate ≝ generate
> index arr coords ≝ fromJust $ indexes arr coords
-}
instance (Shape sh) ⇒ Representable (Array sh) where

  type Rep (Array sh) = [Int]
  tabulate = generate
  index = fromJust .: indexes



type Pointed    sh a = Store  (Array sh)   a
type PointedT w sh a = StoreT (Array sh) w a


{- | Construct a 'Store' comonad ("pointed Array") with the 'Identity' functor. -}
pointed ∷ ∀ sh a. Array sh a → [Int] → Pointed sh a
pointed = StoreT @(Array sh) ∘ Identity

{- | Unpack an 'Array'-backed 'Store' comonad with the 'Identity' functor. -}
unPointed ∷ ∀ sh a. Pointed sh a → (Array sh a, [Int])
unPointed (StoreT (Identity a) coords) = (a, coords)

{- | Construct a 'StoreT' comonad wrapped with an arbitrary comonad. -}
pointedT ∷ ∀ w sh a. (Comonad w) ⇒ w (Array sh a) → [Int] → PointedT w sh a
pointedT = StoreT

{- | Unpack an 'Array'-backed 'StoreT' comonad wrapped with an arbitrary comonad. -}
unPointedT ∷ ∀ w sh a. (Comonad w) ⇒ PointedT w sh a → (w (Array sh a), [Int])
unPointedT (StoreT wa coords) = (wa, coords)

{- | Lift a function on a pointed 'Array' into an 'extend'-able function. -}
stencil ∷ ∀ sh a b. (Shape sh) ⇒ (Array sh a → [Int] → b) → (Pointed sh a → b)
stencil f = uncurry f ∘ unPointed

{- | Pointed variation on 'tabulate'. -}
tabulate' ∷ ∀ sh a. (Shape sh) ⇒ ([Int] → a) → [Int] → Pointed sh a
tabulate' = store





{- | Broadcast a generation function @n@ levels down: if @f@ is a function of @m@
coordinates and @Rank sh ~ (n + m)@, then @sufgenerate @n @sh f@ is essentially
a call to @generate (f ∘ drop m)@, i.e. where the behavior of the function
passed to 'generate' is /independent/ of the first @m@ coordinates and instead
only depends on a /suffix/ of complete coordinates.

>>> :t sufgenerate @1 @[5,2,4] @[2,4]
sufgenerate @1 @[5,2,4] @[2,4]
  :: (Shape [5, 2, 4], KnownNat 1, Shape [2, 4],
      Drop 1 [5, 2, 4] ~ [2, 4]) =>
     ([Int] -> a) -> Array [5, 2, 4] a
>>> pp $ sufgenerate @1 @[5,2,4] @[2,4] (\[y,z] -> ginnerIndex [4,1] 0 [y,z])
┌───────┐
│0 1 2 3│
│4 5 6 7│
│       │
│0 1 2 3│
│4 5 6 7│
│       │
│0 1 2 3│
│4 5 6 7│
│       │
│0 1 2 3│
│4 5 6 7│
│       │
│0 1 2 3│
│4 5 6 7│
└───────┘
-}
sufgenerate ∷ ∀ n sh i a.
            (KnownNat n, Shape sh, Shape i, Drop n sh ~ i)
            ⇒ ([Int] → a) → Array sh a
sufgenerate f =
  generate (f ∘ ( drop
                  ∘ fromIntegral
                  ∘ natVal
                  $ SNat @n
                  )
             )


-- TODO Performance: Current implementation is simple and expensive.
{- | Where @sufgenerate@ essentially is a call to @generate@ with a function that
is insensitive to some prefix of the complete set of coordinates into the
generated 'Array', 'pregenerate' lets blocks or slices of the resulting 'Array' be
generated from a prefix of complete coordinates into the resulting 'Array'.

>>> :t pregenerate @1 @[5,2,4] @[2,4] @'[5]
pregenerate @1 @[5,2,4] @[2,4] @'[5]
  :: (Shape [5, 2, 4], KnownNat 1, Shape [2, 4],
      Drop 1 [5, 2, 4] ~ [2, 4], Take 1 [5, 2, 4] ~ '[5], Shape '[5]) =>
     ([Int] -> Array [2, 4] a) -> Array [5, 2, 4] a
>>> pp $ pregenerate @1 @[5,2,4] @[2,4] @'[5] (\[x] -> A.constant x)
┌───────┐
│0 0 0 0│
│0 0 0 0│
│       │
│1 1 1 1│
│1 1 1 1│
│       │
│2 2 2 2│
│2 2 2 2│
│       │
│3 3 3 3│
│3 3 3 3│
│       │
│4 4 4 4│
│4 4 4 4│
└───────┘
-}
pregenerate ∷ ∀ n sh i o a.
            (KnownNat n, Shape sh, Shape i, Shape o, Drop n sh ~ i, Take n sh ~ o)
            ⇒ ([Int] → Array i a) → Array sh a
pregenerate f =
  let n' = fromIntegral $ natVal $ SNat @n ∷ Int
      -- TODO revise
      -- Very simple, very inefficient initial implementation:
      -- 1. Create a nested array.
      subs ∷ Array o (Array i a)
      subs = generate f
      -- 2. And then essentially *regenerate it* into a non-nested
      --    version.
      f' ∷ [Int] → a
      f' = uncurry ($)
         ∘ first (fromJust .: indexes)     -- Index into the inner array
         ∘ first (fromJust ∘ indexes subs) -- Index into the outer array
         ∘ L.splitAt n'                    -- (outer coords, inner coords)
  in  generate f'




-- TODO consider renaming it to 'irerank'?
{- | Indexed variant of @orthotope@'s 'rerank' with a more Haskell-transparent
name: @isubmap \@n f as@ applies @f@ @n@ ranks deep into @as@. -}
isubmap ∷ ∀ n sh i o a b.
        (Shape sh, KnownNat n, Shape i, Drop n sh ~ i, Take n sh ~ o, Shape o)
        ⇒ ([Int] → Array i a → Array i b) → Array sh a → Array sh b
isubmap f = ravelN @n @sh @i @o
          ∘ A.fromList
          ∘ P.zipWith f (coordsOf @o)
          ∘ subarraysL @n



{- | Variation on 'indexes': where 'indexes' takes a /complete/ set of coordinates and
returns the value at that location, 'subindexes' takes partial (prefix) coordinates
and returns the subarray at that location.

>>> as = A.reshape @[5,2,4] $ A.iota @40 @Int
>>> pp as
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
>>> pp $ fromJust $ subindexes @1 as [0]
┌───────┐
│0 1 2 3│
│4 5 6 7│
└───────┘
>>> pp $ fromJust $ subindexes @1 as [1]
┌───────────┐
│ 8  9 10 11│
│12 13 14 15│
└───────────┘
>>> pp $ fromJust $ subindexes @2 as [0,0]
┌───────┐
│0 1 2 3│
└───────┘
>>> pp $ fromJust $ subindexes @2 as [1,0]
┌───────────┐
│ 8  9 10 11│
└───────────┘
>>> pp $ fromJust $ subindexes @2 as [2,0]
┌───────────┐
│16 17 18 19│
└───────────┘
-}
subindexes ∷ ∀ n sh i a.
          (KnownNat n, Shape sh, Shape i, Drop n sh ~ i, Shape (Take n sh))
          ⇒ Array sh a → [Int] → Maybe (Array i a)
subindexes = indexes ∘ subarrays @n @sh @i


{- | @getSubindex \@n \@sh \@i coords@ is a getter suitable for creating a lens
over @Array sh@. -}
getSubindex ∷ ∀ n sh i a.
            (KnownNat n, Shape sh, Shape i, Drop n sh ~ i, Shape (Take n sh))
            ⇒ [Int] → Array sh a → Array i a
getSubindex = fromJust .: flip (subindexes @n @sh @i)


-- TODO Does @orthotope@'s internal 'Vector' interface permit a non-O(n) update?
{- | @setSubindex \@n \@sh \@i coords@ is a setter suitable for creating a lens
over @Array sh@. -}
setSubindex ∷ ∀ n sh i a.
            (KnownNat n, Shape sh, Shape i, Drop n sh ~ i, Shape (Take n sh))
            ⇒ [Int] → Array sh a → Array i a → Array sh a
setSubindex coords arr =
  let f ∷ Array i a → [Int] → Array i a → Array i a
      f subarr = let g coords' subarr'
                       | coords' == coords = subarr
                       | otherwise         = subarr'
                 in g
  in flip (isubmap @n @sh @i) arr ∘ f


{- | Specify a list of axes for permutation with @Data.Array.Dynamic.transpose@
that slips the first /n/ axes to the end. If the input 'Array' has less than /n/
axes, this returns a vacuous "permutation": it does not result in a runtime
error. -}
slipNr ∷ Nat → D.Array a → [Int]
slipNr n = uncurry (flip (++))           -- Flip makes the swap happen.
         ∘ L.splitAt (fromIntegral n)
         ∘ (\x → [0..(D.rank x - 1)])  -- Axes in ascending order.


{- | Specify a list of axes for permutation with @Data.Array.Dynamic.transpose@
that slips the last /n/ axes to the start. If the input 'Array' has less than
/n/ axes, this returns a vacuous "permutation": it does not result in a runtime
error. -}
slipNl ∷ Nat → D.Array a → [Int]
slipNl n = uncurry (flip (++))
         ∘ (flip L.splitAt <*> (subtract (fromIntegral n) ∘ length))
         ∘ (\x → [0..(D.rank x - 1)])


-- {- | Specify a list of axes for transposition that slips the first two axes to the
-- end. If the input 'Array' has less than two axes, this returns a vacuous
-- "transposition": it does not result in a runtime error. -}
-- slip2r ∷ D.Array a → [Int]
-- slip2r = uncurry (flip (++))           -- Flip makes the swap happen.
--        ∘ L.splitAt 2
--        ∘ (\x → [0..((D.rank x) - 1)])  -- Axes in ascending order.


-- {- | Specify a list of axes for transposition that slips the last two axes to the
-- start. If the input 'Array' has less than two axes, this returns a vacuous
-- "transposition": it does not result in a runtime error. -}
-- slip2l ∷ D.Array a → [Int]
-- slip2l = uncurry (flip (++))
--         ∘ (flip L.splitAt <*> (subtract 2 ∘ length))
--         ∘ (\x → [0..((D.rank x) - 1)])


-- {- | Specify a list of axes for transposition that swaps the second and third
-- axes. If the input 'Array' has less than three axes, this returns a vacuous
-- "transposition": it does not result in a runtime error. -}
-- flip32 ∷ D.Array a → [Int]
-- flip32 = uncurry (++)
--        ∘ first ( uncurry (++)
--                ∘ second reverse
--                ∘ L.splitAt 1
--                )
--        ∘ L.splitAt 3
--        ∘ (\x → [0..((D.rank x) - 1)])




{- | Per the @orthotope@ docs, this is mostly convenient as a development and
debugging aid; it offers an APL-like pretty printed view of a multidimensional
array. Examples of what it offers are found throughout this module and in the
package documentation for @orthotope@. -}
pp ∷ (Pretty a) ⇒ a → IO ()
pp = putStrLn . prettyShow










{- | Concatenate two 'Arrays' along their first (outermost) dimension (rows).

Synonym for @orthotope@'s 'append'. -}
vappend ∷ ∀ m n sh a.
        ( A.Shape sh, KnownNat m, KnownNat n, KnownNat (m + n))
        ⇒ Array (m : sh) a
        → Array (n : sh) a
        → Array ((m + n) : sh) a
vappend = A.append


-- TODO generalize for rank ≥ 2
{- | Concatenate two arrays with a common first dimension along their second
dimension.

>>> exm = A.fromList [2, 8, 3, 5, 4, 1] :: Array [2,3] Int
>>> pp exm
┌─────┐
│2 8 3│
│5 4 1│
└─────┘
>>> exn = A.fromList [4, 1, 6, 3, 2, 4, 5, 7] :: Array [2,4] Int
>>> pp exn
┌───────┐
│4 1 6 3│
│2 4 5 7│
└───────┘
>>> pp $ happend exm exn
┌─────────────┐
│2 8 3 4 1 6 3│
│5 4 1 2 4 5 7│
└─────────────┘
-}
happend ∷ ∀ m n o a.
        (KnownNat m, KnownNat n, KnownNat (m + n), KnownNat o)
        ⇒ Array '[o, m] a
        → Array '[o, n] a
        → Array '[o, m + n] a
happend = transpose @[1,0]
        ∘ uncurry vappend
        ∘ (transpose @[1,0] ⁂ transpose @[1,0])
       .: (,)


