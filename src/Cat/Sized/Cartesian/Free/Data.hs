{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Cartesian.Free.Data
  ( Cart ( Emb
         , Id
         , Of
         , Par
         , Mul
         , Ith
         , Ith'
         , Join
         , Split
         , Assoc
         , Sing
         , Unsing
         , Lift1
         , Bising
         , Bisplit
         , Bijoin
         , Biassoc
         , Swap
         -- , Swap'
         -- , Permute
         , Dup
         , Dup'
         , Fork
         , Fork'
         , Idx
         , Del
         , Sel
         , Zip
         , ZipWith
         )

  , HasObject (ObjectOf)
  , HasProxy  (ProxyOf)
  , HasSwap   (SwapObjectOf)
  , HasPerm   (PermObjectOf)
  , HasDup    (DupObjectOf)
  , HasDel    (DelObjectOf)
  , HasProj   (ProjObjectOf)
  , HasSelect (SelectObjectOf)

  , foldMap

    -- * Recursion schemes
  , CartF ( EmbF
          , IdF
          , OfF
          , ParF
          , MulF
          , IthF
          , IthF'
          , JoinF
          , SplitF
          , AssocF
          , SingF
          , UnsingF
          , Lift1F
          , BisingF
          , BisplitF
          , BijoinF
          , BiassocF
          , SwapF
          -- , SwapF'
          -- , PermuteF
          , DupF
          , DupF'
          , ForkF
          , ForkF'
          , IdxF
          , DelF
          , SelF
          , ZipF
          , ZipWithF
          )
  , Cart'
  , CartesianFunctor
  , fixed'
  , unfixed'
  , mkAlg
  , foldMap'
  ) where

{- TODO

- The extra constraints associated wiht substructural combinators require some
  extra work to make recursion schemes typecheck compared to e.g. 'Monoidal'.
-}

import Prelude hiding
  ( id
  , (.)
  , Functor
  , fmap
  , foldMap
  , zip
  , zipWith
  )
-- import Prelude.Unicode ((∘))

import Data.Kind
  ( Type
  -- , Constraint
  )

import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  -- , pattern SNat
  , type (+)
  , type (-)
  , type (*)
  , type (<=)
  )

import Data.Finite (Finite)
-- import Data.Proxy (Proxy(Proxy))

-- import Data.Functor.Rep (Representable, Rep)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Functor
  ( -- NT
    NT'
  , HFunctor ( hfmap
             , HFunctorObj
             )
  , Fix ( In
        , out
        )
  , cata
  -- , ana
  )

import Cat.Sized.Functor.Monoidal qualified as MF
import Cat.Sized.Functor.Monoidal (zip, zipWith)

import Cat.Sized.Semigroupoid.Class
  ( Object
  , Object'
  , (⊙)
  )
import Cat.Sized.Category.Class
  ( id
  )

import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , (***)
             , mul
             , ith
             , ith'
             , join
             , split
             , assoc
             , sing
             , unsing
             , lift1
             , bising
             , bisplit
             , bijoin
             , biassoc
             )
  , (⊗)
  -- , ProdK
  )
import Cat.Sized.Braided.Class
  ( Braided ( SwapObject
            , swap
            -- , swap'
            )
  , SwapObject'
  -- , Permutable ( PermObject
  --              , permute
  --              )
  -- , PermObject'
  )
import Cat.Sized.Diagonal.Class
  ( Diagonal ( DupObject
             , dup
             , dup'
             -- , (&&&)
             , fork
             )
  , DupObject'
  , (△)
  )
import Cat.Sized.Semicartesian.Class
  ( Semicartesian ( ProjObject
                  , idx
                  )
  -- , index
  -- , π
  , ProjObject'
  , Delete ( DelObject
           , del
           )
  , DelObject'
  , Select ( SelectObject
           , sel
           )
  -- , unfork
  , SelectObject'
  )
import Cat.Sized.Cartesian.Class
  ( Cartesian
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( HasObject ( ObjectOf
              )
  )

import Cat.Sized.Monoidal.Free.Data
  ( HasProxy (ProxyOf)
  )
import Cat.Sized.Braided.Free.Data
  ( HasSwap (SwapObjectOf)
  , HasPerm (PermObjectOf)
  , BraidedFunctor
  )
import Cat.Sized.Diagonal.Free
  ( HasDup (DupObjectOf)
  , DiagonalFunctor
  )
import Cat.Sized.Semicartesian.Free
  ( HasDel(DelObjectOf)
  , HasProj(ProjObjectOf)
  , HasSelect(SelectObjectOf)
  , SemicartesianFunctor
  , DeleteFunctor
  , SelectFunctor
  )





data Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   where

  Emb ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a
      , ObjectOf φ k m b
      -- TODO constrain k to be a category or monoidal?
      )
      ⇒ a -|      k φ n m |-> b  -- ^ A /k/-morphism to lift into a symmetric monoidal category.
      → a -| Cart k φ n m |-> b

  Id ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a
     )
     ⇒ Cart k φ n n a a  -- ^ The lifted identity morphism for any given size /n/.

  Of ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
           (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a
     , ObjectOf φ k m b
     , ObjectOf φ k l x
     )
     ⇒ x -| Cart k φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -| Cart k φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| Cart k φ n m |-> b

  Par ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ a -| Cart k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Cart k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Cart k φ (n + n') (m + m') |-> b

  Mul ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -| Cart k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Cart k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Cart k φ (n + n') (m + m') |-> b

  Ith ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a
      , ObjectOf φ k n a
      )
      ⇒ Finite n                 -- ^ The position to place the singleton-to-singleton morphism.
      → a -| Cart k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| Cart k φ n n |-> a

  Ith' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a
       , ObjectOf φ k n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                 -- ^ The position to place the singleton-to-singleton morphism.
       → a -| Cart k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| Cart k φ n n |-> a

  Join ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| Cart k φ n (n * m) |-> a
       ⇒ (φ m a) -| Cart k φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  Split ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a
        , ObjectOf φ k      n  (φ m a)
        )
        -- ⇒ a -| Cart k φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| Cart k φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  Assoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a)
        , ObjectOf φ k m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| Cart k φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| Cart k φ n m |-> (φ n a)  -- ^ A size-preserving morphism that re-associates (and hence preserving the order of) a nested product.

  Sing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a
        , ObjectOf φ k 1 (φ n a)
        )
        ⇒ a -| Cart k φ n 1 |-> φ n a

  Unsing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a)
        , ObjectOf φ k n      a
        )
        ⇒ φ n a -| Cart k φ 1 n |-> a

  Lift1 ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a
        , ObjectOf φ k m      b
        , ObjectOf φ k n (φ 1 a)
        , ObjectOf φ k m (φ 1 b)
        )
        ⇒     a -| Cart k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| Cart k φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  Bising ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a
         , ObjectOf φ k m      b
         , ObjectOf φ k 1 (φ n a)
         , ObjectOf φ k 1 (φ m b)
         )
         ⇒     a -| Cart k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| Cart k φ 1 1 |-> φ m b

  Bisplit ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒     a -| Cart k φ (i * n) (j * m) |->     b  -- ^ A /k/ morphism whose products on either side can be factored.
    → φ i a -| Cart k φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  Bijoin ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (i ∷ Nat) (j ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒ φ i a -| Cart k φ      n       m  |-> φ j b  -- ^ A /k/ morphism with nested products.
    →     a -| Cart k φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  Biassoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n  ∷ Nat) (m  ∷ Nat)
                (i  ∷ Nat) (j  ∷ Nat)
                (n' ∷ Nat) (m' ∷ Nat)
                (i' ∷ Nat) (j' ∷ Nat)
                (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a
    , ObjectOf φ k (j' * m')      b
    )
    ⇒ φ i  a -| Cart k φ n  m  |-> φ j  b  -- ^ A /k/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| Cart k φ n' m' |-> φ j' b

  Swap ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n a
        , SwapObjectOf φ k n a
        )
        ⇒ Finite n
        → Finite n
        → a -| Cart k φ n n |-> a  -- ^ A morphism that swaps the two selected indices in an /n/-product.

  -- Swap' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --             (n ∷ Nat) (a ∷ κ).
  --        ( KnownNat n
  --        , ObjectOf φ k n a
  --        , SwapObjectOf φ k n a
  --        )
  --        ⇒ (Proxy φ k) n
  --        → Finite n
  --        → Finite n
  --        → a -| Cart k φ n n |-> a


  -- TODO Adding this requires a custom show instance def: there's no guarantee
  -- that γ (Finite n) is Showable, and adding a Show constraint here would
  -- prevent a 'Permutable' instance...
  -- Permute ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --               γ (n ∷ Nat) (a ∷ κ).
  --         ( KnownNat n
  --         , ObjectOf φ k n a
  --         , PermObjectOf φ k n a
  --         , Representable γ
  --         , Rep γ ~ Finite n
  --         -- , Representable (Perm φ k n)
  --         -- , Rep (Perm φ k n) ~ Finite n
  --         )
  --         ⇒ γ (Finite n)              -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.

  --         -- -- ⇒ Perm φ Cart k n (Finite n)  -- -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.
  --         → a -| Cart k φ n n |-> a

  {- | 'dup' maps an input length-/n/ product to one of length /m = s⋅n/. -}
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (b ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (m ∷ Nat) (a ∷ κ).
  Dup ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , KnownNat s
      -- , KnownNat m
      -- , KnownNat b
      , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
      -- , m ~ s * n
      -- , m ~ (s * n) + b
      , ObjectOf φ k      n  a
      , ObjectOf φ k (s * n) a
      , DupObjectOf φ k n (s * n) a a
      -- , Object φ k ((s * n) + b) a
      -- , DupObject φ k n ((s * n) + b) a a
      )
      ⇒ a -| Cart k φ n (s * n) |-> a  -- ^ A morphism that creates /s/ copies of each element in the source /n/-product.
      -- ⇒ a -| k φ n ((s * n) + b) |-> a

  Dup' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , KnownNat s
       , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
       , ObjectOf φ k      n  a
       , ObjectOf φ k (s * n) a
       , DupObjectOf φ k n (s * n) a a
       )
       ⇒ (ProxyOf φ k) n  -- ^ A proxy for the length of the source /n/-product.
       → (ProxyOf φ k) s  -- ^ A proxy for the number of copies /s/ of each element of the source to make.
       → a -| Cart k φ n (s * n) |-> a  -- ^ A morphism that creates /s/ copies of each element in the source /n/-product.


  Fork ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        , ObjectOf φ k l a
        , ObjectOf φ k n b
        , ObjectOf φ k m b
        , ObjectOf φ k (n + m) b
        , DupObjectOf φ k l n a b
        , DupObjectOf φ k l m a b
        , DupObjectOf φ k l (n + m) a b
        )
        ⇒ a -| Cart k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| Cart k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
        → a -| Cart k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.

  Fork' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        , ObjectOf φ k l a
        , ObjectOf φ k n b
        , ObjectOf φ k m b
        , ObjectOf φ k (n + m) b
        , DupObjectOf φ k l n a b
        , DupObjectOf φ k l m a b
        , DupObjectOf φ k l (n + m) a b
        )
        ⇒ (ProxyOf φ k) l
        → (ProxyOf φ k) n
        → (ProxyOf φ k) m
        → a -| Cart k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| Cart k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
        → a -| Cart k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.


  Idx ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k n a
      , ObjectOf φ k 1 a
      , ProjObjectOf φ k n a
      )
      ⇒ Finite n            -- ^ The index to project out of an /n/-product.
      → a -| Cart k φ n 1 |-> a


  Del ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , 1 <= n
      , ObjectOf φ k  n      a
      , ObjectOf φ k (n - 1) a
      , DelObjectOf φ k n a
      )
      ⇒ Finite n                  -- ^ The index to remove from an /n/-product.
      → a -| Cart k φ n (n - 1) |-> a


  Sel ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
      ( KnownNat l, KnownNat n
      , l <= n
      , ObjectOf φ k n a
      , ObjectOf φ k l a
      , SelectObjectOf φ k l n a
      )
      ⇒ Finite ((n - l) + 1) -- ^ The starting index of the length /l/ "slice".
      → a -| Cart k φ n l |-> a


  -- TODO Having a 'Cartesian' instance ought to be sufficient for being able to
  -- define a 'Zip' instance, but that's not currently cashed out with instances
  -- or newtypes besides 'Permutable'.
  Zip ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n (φ m a)
      , ObjectOf φ k m (φ n a)
      )
      ⇒ φ m a -| Cart k φ n m |-> φ n a  -- ^ A /k/-morphism taking an /n/-product of /m/-products to an aligned ("zipped") /m/-product of /n/-products.


  ZipWith ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (a ∷ κ)   (b ∷ κ)
                (l ∷ Nat).
          ( KnownNat n, KnownNat m, KnownNat l
          , ObjectOf φ k      n      a  , ObjectOf φ k      m      b
          , ObjectOf φ k      n (φ l a)
          , ObjectOf φ k      l (φ n a) , ObjectOf φ k      l (φ m b)
          -- , MonoidalEndo (φ l) φ k
          )
          ⇒     a -| Cart k φ n m |->     b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
          → φ l a -| Cart k φ n l |-> φ m b  -- ^ Zip an /n/ product of /(φ l a)/s together and then map the morphism over the resulting /l/ product.


deriving instance ( p ~ ProxyOf φ k
                  , ∀ i. Show (p i)
                  , ∀ i j x y. Show (k φ i j x y)
                  ) ⇒ Show (Cart k φ n m a b)



foldMap ∷ ∀ κ
          (φ ∷  Nat → κ → κ)
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( ObjectOf φ k n a, ObjectOf φ k m b
        , Object   φ t n a, Object   φ t m b
        , ∀ i x. ObjectOf φ k i x ⇒ Object' φ t i x
        -- , SwapObjectOf φ k n a, SwapObjectOf φ k n b
        -- , SwapObject   φ t n a, SwapObject   φ t n b
        , ∀ n' x. SwapObjectOf φ k n' x ⇒ SwapObject' φ t n' x
        , ∀ n' m' x y. DupObjectOf φ k n' m' x y ⇒ DupObject' φ t n' m' x y
        , ∀ n' x. ProjObjectOf φ k n' x ⇒ ProjObject' φ t n' x
        , ∀ n' x. DelObjectOf  φ k n' x ⇒ DelObject'  φ t n' x
        , ∀ n' l' x. SelectObjectOf φ k l' n' x ⇒ SelectObject' φ t l' n' x
        , Delete φ (Cart k), Delete φ t
        , Select φ (Cart k), Select φ t
        , Cartesian φ (Cart k), Cartesian φ t, MF.Zip φ t
        )
        ⇒ (∀ i. (ProxyOf φ k) i → (Proxy φ t) i)
        → (∀ i j x y.
           ( ObjectOf φ k i x, ObjectOf φ k j y
           , Object   φ t i x, Object   φ t j y
           -- , SwapObjectOf φ k i x, SwapObjectOf φ k j y
           -- , SwapObject   φ t i x, SwapObject   φ t j y
           )
           ⇒ x -| k φ i j |-> y
           → x -| t φ i j |-> y
        )                            -- ^ A function maps primitive morphisms into the target category.
        → a -| (Cart k) φ n m |-> b  -- ^ A path in the free symmetric monoidal category over @k@.
        → a -|  t      φ n m |-> b   -- ^ The resulting morphism in @t@.
foldMap _ α (Emb f)     = α f
foldMap _ _  Id         = id
foldMap π α (g `Of` f)  = foldMap π α g  ⊙  foldMap π α f
foldMap π α (f `Par` g) = foldMap π α f  ⊗  foldMap π α g
foldMap π α (Mul pn pm pn' pm' f g) = mul (π pn) (π pm) (π pn') (π pm')
                                          (foldMap π α f) (foldMap π α g)
foldMap π α (i `Ith` f)   = i `ith` (foldMap π α f)
foldMap π α (Ith' pn i f) = ith' (π pn) i (foldMap π α f)
foldMap _ _ Join   = join
foldMap _ _ Split  = split
foldMap _ _ Assoc  = assoc
foldMap _ _ Sing   = sing
foldMap _ _ Unsing = unsing
foldMap π α (Lift1   f)  = lift1   (foldMap π α f)
foldMap π α (Bising  f)  = bising  (foldMap π α f)
foldMap π α (Bisplit f)  = bisplit (foldMap π α f)
foldMap π α (Bijoin  f)  = bijoin  (foldMap π α f)
foldMap π α (Biassoc f)  = biassoc (foldMap π α f)
foldMap _ _ (Swap i j)   = swap i j
foldMap _ _ Dup          = dup
foldMap π _ (Dup' pn ps) = dup' (π pn) (π ps)
foldMap π α (Fork           f g) = (foldMap π α f) △ (foldMap π α g)
foldMap π α (Fork' pl pn pm f g) = fork (π pl) (π pn) (π pm) (foldMap π α f) (foldMap π α g)
foldMap _ _ (Idx fn)    = idx fn
foldMap _ _ (Del fn)    = del fn
foldMap _ _ (Sel fn)    = sel fn
foldMap _ _ Zip         = MF.zip
foldMap π α (ZipWith f) = MF.zipWith (foldMap π α f)


-- TODO Permit change of tensor product in foldMap





{- | Pattern functor for 'Cart'. -}
data CartF (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (φ ∷ Nat → κ → κ)
           (n ∷ Nat) (m ∷ Nat)
           (a ∷ κ)   (b ∷ κ)   where

  EmbF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a, ObjectOf φ k m b
      , Object   φ t n a, Object   φ t m b
      )
      ⇒ a -|       k   φ n m |-> b  -- ^ A /k/-morphism to lift into a monoidal category.
      → a -| CartF k t φ n m |-> b

  IdF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat)
            (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a, Object φ t n a
     )
     ⇒ a -| CartF k t φ n n |-> a  -- ^ The lifted identity morphism for any given size /n/.

  OfF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
            (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
     , Object   φ t n a, Object   φ t m b, Object   φ t l x
     )
     ⇒ x -|         t φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -|         t φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| CartF k t φ n m |-> b

  ParF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ a -|         t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|         t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| CartF k t φ (n + n') (m + m') |-> b

  MulF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -|         t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|         t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| CartF k t φ (n + n') (m + m') |-> b

  IthF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a, ObjectOf φ k n a
      , Object   φ t 1 a, Object   φ t n a
      )
      ⇒ Finite n                    -- ^ The position to place the singleton-to-singleton morphism.
      → a -|         t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| CartF k t φ n n |-> a

  IthF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a, ObjectOf φ k n a
       , Object   φ t 1 a, Object   φ t n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                    -- ^ The position to place the singleton-to-singleton morphism.
       → a -|         t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| CartF k t φ n n |-> a

  JoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       , Object   φ t  n      (φ m a)
       , Object   φ t (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| CartF k t φ n (n * m) |-> a
       ⇒ (φ m a) -| CartF k t φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  SplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a , Object   φ t (m * n)      a
        , ObjectOf φ k      n  (φ m a), Object   φ t      n  (φ m a)
        )
        -- ⇒ a -| CartF k t φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| CartF k t φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  AssocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a), ObjectOf φ k m (φ n a)
        , Object   φ t n (φ m a), Object   φ t m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| CartF k t φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| CartF k t φ n m |-> (φ n a)  -- ^ A size-preserving morphism that swaps nesting.

  SingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a , Object   φ t n      a
        , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
        )
        ⇒ a -| CartF k t φ n 1 |-> φ n a

  UnsingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
        , ObjectOf φ k n      a , Object   φ t n      a
        )
        ⇒ φ n a -| CartF k t φ 1 n |-> a

  Lift1F ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a , Object   φ t n      a
        , ObjectOf φ k m      b , Object   φ t m      b
        , ObjectOf φ k n (φ 1 a), Object   φ t n (φ 1 a)
        , ObjectOf φ k m (φ 1 b), Object   φ t m (φ 1 b)
        )
        ⇒     a -|         t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| CartF k t φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  BisingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a , Object   φ t n      a
         , ObjectOf φ k m      b , Object   φ t m      b
         , ObjectOf φ k 1 (φ n a), Object   φ t 1 (φ n a)
         , ObjectOf φ k 1 (φ m b), Object   φ t 1 (φ m b)
         )
         ⇒     a -|        t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| CartF k t φ 1 1 |-> φ m b

  BisplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n ∷ Nat) (m ∷ Nat)
                 (i ∷ Nat) (j ∷ Nat)
                 (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a , Object   φ t (i * n)     a
    , ObjectOf φ k (j * m)     b , Object   φ t (j * m)     b
    , ObjectOf φ k      n (φ i a), Object   φ t      n (φ i a)
    , ObjectOf φ k      m (φ j b), Object   φ t      m (φ j b)
    )
    ⇒     a -|         t φ (i * n) (j * m) |->     b  -- ^ A /t/ morphism whose products on either side can be factored.
    → φ i a -| CartF k t φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  BijoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a , Object   φ t (i * n)     a
    , ObjectOf φ k (j * m)     b , Object   φ t (j * m)     b
    , ObjectOf φ k      n (φ i a), Object   φ t      n (φ i a)
    , ObjectOf φ k      m (φ j b), Object   φ t      m (φ j b)
    )
    ⇒ φ i a -|         t φ      n       m  |-> φ j b  -- ^ A /t/ morphism with nested products.
    →     a -| CartF k t φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  BiassocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n  ∷ Nat) (m  ∷ Nat)
                 (i  ∷ Nat) (j  ∷ Nat)
                 (n' ∷ Nat) (m' ∷ Nat)
                 (i' ∷ Nat) (j' ∷ Nat)
                 (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a), Object   φ t       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b), Object   φ t       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a), Object   φ t       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b), Object   φ t       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a , Object   φ t (i' * n')      a
    , ObjectOf φ k (j' * m')      b , Object   φ t (j' * m')      b
    )
    ⇒ φ i  a -|         t φ n  m  |-> φ j  b  -- ^ A /t/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| CartF k t φ n' m' |-> φ j' b

  SwapF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n a, SwapObjectOf φ k n a
        , Object   φ t n a, SwapObject   φ t n a
        )
        ⇒ Finite n
        → Finite n
        → a -| CartF k t φ n n |-> a  -- ^ A morphism that swaps the two selected indices in an /n/-product.

  -- SwapF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --              (n ∷ Nat) (a ∷ κ).
  --        ( KnownNat n
  --        , ObjectOf φ k n a, SwapObjectOf φ k n a
  --        , Object   φ t n a, SwapObject   φ t n a
  --        )
  --        ⇒ (Proxy φ k) n
  --        → Finite n
  --        → Finite n
  --        → a -| CartF k t φ n n |-> a


  -- TODO Adding this requires a custom show instance def: there's no guarantee
  -- that γ (Finite n) is Showable, and adding a Show constraint here would
  -- prevent a 'Permutable' instance...
  -- Permute ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  --               γ (n ∷ Nat) (a ∷ κ).
  --         ( KnownNat n
  --         , ObjectOf φ k n a
  --         , PermObjectOf φ k n a
  --         , Representable γ
  --         , Rep γ ~ Finite n
  --         -- , Representable (Perm φ k n)
  --         -- , Rep (Perm φ k n) ~ Finite n
  --         )
  --         ⇒ γ (Finite n)              -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.

  --         -- -- ⇒ Perm φ Cart k n (Finite n)  -- -- ^ A permutation on an /n/-product specified by a permutation of /n/ indices.
  --         → a -| Cart k φ n n |-> a

  {- | 'dup' maps an input length-/n/ product to one of length /m = s⋅n/. -}
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (b ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (m ∷ Nat) (a ∷ κ).
  DupF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , KnownNat s
      -- , KnownNat m
      -- , KnownNat b
      , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
      -- , m ~ s * n
      -- , m ~ (s * n) + b
      , ObjectOf φ k      n  a       , Object φ t      n  a
      , ObjectOf φ k (s * n) a       , Object φ t (s * n) a
      , DupObjectOf φ k n (s * n) a a, DupObject φ t n (s * n) a a
      -- , Object φ k ((s * n) + b) a
      -- , DupObject φ k n ((s * n) + b) a a
      )
      ⇒ a -| CartF k t φ n (s * n) |-> a  -- ^ A morphism that creates /s/ copies of each element in the source /n/-product.
      -- ⇒ a -| k φ n ((s * n) + b) |-> a

  DupF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , KnownNat s
       , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
       , ObjectOf φ k      n  a       , Object φ t      n  a
       , ObjectOf φ k (s * n) a       , Object φ t (s * n) a
       , DupObjectOf φ k n (s * n) a a, DupObject φ t n (s * n) a a
       )
       ⇒ (ProxyOf φ k) n  -- ^ A proxy for the length of the source /n/-product.
       → (ProxyOf φ k) s  -- ^ A proxy for the number of copies /s/ of each element of the source to make.
       → a -| CartF k t φ n (s * n) |-> a  -- ^ A morphism that creates /s/ copies of each element in the source /n/-product.


  ForkF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        , ObjectOf φ k l a             , Object φ t l a
        , ObjectOf φ k n b             , Object φ t n b
        , ObjectOf φ k m b             , Object φ t m b
        , ObjectOf φ k (n + m) b       , Object φ t (n + m) b
        , DupObjectOf φ k l n a b      , DupObject φ t l n a b
        , DupObjectOf φ k l m a b      , DupObject φ t l m a b
        , DupObjectOf φ k l (n + m) a b, DupObject φ t l (n + m) a b
        )
        ⇒ a -|         t φ l  n      |-> b  -- ^ A /t/-morphism from /φ l a/ to /φ n b/.
        → a -|         t φ l      m  |-> b  -- ^ A /t/-morphism from /φ l a/ to /φ m b/.
        → a -| CartF k t φ l (n + m) |-> b  -- ^ A     morphism from /φ l a/ to /φ (n + m) b/.

  ForkF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        , ObjectOf φ k l a             , Object φ t l a
        , ObjectOf φ k n b             , Object φ t n b
        , ObjectOf φ k m b             , Object φ t m b
        , ObjectOf φ k (n + m) b       , Object φ t (n + m) b
        , DupObjectOf φ k l n a b      , DupObject φ t l n a b
        , DupObjectOf φ k l m a b      , DupObject φ t l m a b
        , DupObjectOf φ k l (n + m) a b, DupObject φ t l (n + m) a b
        )
        ⇒ (ProxyOf φ k) l
        → (ProxyOf φ k) n
        → (ProxyOf φ k) m
        → a -|         t φ l  n      |-> b  -- ^ A /t/-morphism from /φ l a/ to /φ n b/.
        → a -|         t φ l      m  |-> b  -- ^ A /t/-morphism from /φ l a/ to /φ m b/.
        → a -| CartF k t φ l (n + m) |-> b  -- ^ A     morphism from /φ l a/ to /φ (n + m) b/.


  IdxF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k n a    , Object φ t n a
      , ObjectOf φ k 1 a    , Object φ t 1 a
      , ProjObjectOf φ k n a, ProjObject φ t n a
      )
      ⇒ Finite n                 -- ^ The index to project out of an /n/-product.
      → a -| CartF k t φ n 1 |-> a


  DelF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , 1 <= n
      , ObjectOf φ k  n      a , Object φ t  n      a
      , ObjectOf φ k (n - 1) a , Object φ t (n - 1) a
      , DelObjectOf φ k n a    , DelObject φ t n a
      )
      ⇒ Finite n                  -- ^ The index to remove from an /n/-product.
      → a -| CartF k t φ n (n - 1) |-> a


  SelF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (l ∷ Nat) (n ∷ Nat) (a ∷ κ).
      ( KnownNat l, KnownNat n
      , l <= n
      , ObjectOf φ k n a        , Object φ t n a
      , ObjectOf φ k l a        , Object φ t l a
      , SelectObjectOf φ k l n a, SelectObject φ t l n a
      )
      ⇒ Finite ((n - l) + 1)     -- ^ The starting index of the length /l/ "slice".
      → a -| CartF k t φ n l |-> a


  -- TODO Having a 'Cartesian' instance ought to be sufficient for being able to
  -- define a 'Zip' instance, but that's not currently cashed out with instances
  -- or newtypes besides 'Permutable'.
  ZipF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n (φ m a), Object φ t n (φ m a)
      , ObjectOf φ k m (φ n a), Object φ t m (φ n a)
      )
      ⇒ φ m a -| CartF k t φ n m |-> φ n a  -- ^ A     morphism taking an /n/-product of /m/-products to an aligned ("zipped") /m/-product of /n/-products.


  ZipWithF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n ∷ Nat) (m ∷ Nat)
                 (a ∷ κ)   (b ∷ κ)
                 (l ∷ Nat).
          ( KnownNat n, KnownNat m, KnownNat l
          , ObjectOf φ k      n      a  , ObjectOf φ k      m      b
          , ObjectOf φ k      n (φ l a)
          , ObjectOf φ k      l (φ n a) , ObjectOf φ k      l (φ m b)
          , Object   φ t      n      a  , Object   φ t      m      b
          , Object   φ t      n (φ l a)
          , Object   φ t      l (φ n a) , Object   φ t      l (φ m b)
          -- , MonoidalEndo (φ l) φ k
          )
          ⇒     a -|         t φ n m |->     b  -- ^ A /t/-morphism from /φ n a/ to /φ m b/.
          → φ l a -| CartF k t φ n l |-> φ m b  -- ^ Zip an /n/ product of /(φ l a)/s together and then map the morphism over the resulting /l/ product.




deriving instance ( ∀ i j x y. Show (x -| k φ i j |-> y)
                  , ∀ i j x y. Show (x -| t φ i j |-> y)
                  -- , ∀ i p. (p ~ ProxyOf φ k) ⇒ Show (p i)
                  , ProxyOf φ k ~ SNat
                  )
  ⇒ Show (a -| CartF k t φ n m |-> b)


type Cart' k = Fix (CartF k)


class    ( BraidedFunctor       η φ p q
         , DiagonalFunctor      η φ p q
         , SemicartesianFunctor η φ p q
         , DeleteFunctor        η φ p q
         , SelectFunctor        η φ p q
         )
  ⇒ CartesianFunctor            η φ p q
instance ( BraidedFunctor       η φ p q
         , DiagonalFunctor      η φ p q
         , SemicartesianFunctor η φ p q
         , DeleteFunctor        η φ p q
         , SelectFunctor        η φ p q
         )
  ⇒ CartesianFunctor            η φ p q


instance (Cartesian φ (η (Fix η))) ⇒ Cartesian φ (Fix η)



instance HFunctor (CartF k) where
  type HFunctorObj (CartF k) φ p q = CartesianFunctor (CartF k) φ p q

  hfmap _ (EmbF m)    = EmbF m
  hfmap _ IdF         = IdF
  hfmap α (g `OfF`  f) = α g `OfF`  α f
  hfmap α (f `ParF` g) = α f `ParF` α g
  hfmap α (MulF pn pm pn' pm' f g) = MulF pn pm pn' pm' (α f) (α g)
  hfmap α (IthF     i f) = IthF     i (α f)
  hfmap α (IthF' pn i f) = IthF' pn i (α f)
  hfmap _ JoinF   = JoinF
  hfmap _ SplitF  = SplitF
  hfmap _ AssocF  = AssocF
  hfmap _ SingF   = SingF
  hfmap _ UnsingF = UnsingF
  hfmap α (Lift1F   f) = Lift1F   (α f)
  hfmap α (BisingF  f) = BisingF  (α f)
  hfmap α (BisplitF f) = BisplitF (α f)
  hfmap α (BijoinF  f) = BijoinF  (α f)
  hfmap α (BiassocF f) = BiassocF (α f)
  hfmap _ (SwapF i j) = SwapF i j
  -- -- hfmap _ (SwapF') =
  -- -- hfmap α (PermuteF) =
  hfmap _  DupF       = DupF
  hfmap _ (DupF' n s) = DupF' n s
  hfmap α (ForkF        f g) = ForkF (α f) (α g)
  hfmap α (ForkF' l n m f g) = ForkF' l n m (α f) (α g)
  hfmap _ (IdxF i) = IdxF i
  hfmap _ (DelF i) = DelF i
  hfmap _ (SelF i) = SelF i
  hfmap _  ZipF    = ZipF
  hfmap α (ZipWithF f) = ZipWithF (α f)


-- TODO As with 'Cat._.Category.Free.Data', rewrite in terms of an
-- anamorphism/catamorphism ± sort out why that's more painful/awkward
{- | Convert a 'Cart k' morphism to a 'Cart\' k' morphism. -}
fixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ       k  i x ⇒ Object' φ (Cart  k) i x
  , ∀ i x. Object   φ (Cart k) i x ⇒ Object' φ (Cart' k) i x
  , ∀ i   x.   SwapObjectOf   φ k i   x   ⇒ SwapObject'   φ (Cart' k) i   x
  , ∀ i   x.   ProjObjectOf   φ k i   x   ⇒ ProjObject'   φ (Cart' k) i   x
  , ∀ i   x.   DelObjectOf    φ k i   x   ⇒ DelObject'    φ (Cart' k) i   x
  , ∀ i l x.   SelectObjectOf φ k i l x   ⇒ SelectObject' φ (Cart' k) i l x
  , ∀ i j x y. DupObjectOf    φ k i j x y ⇒ DupObject'    φ (Cart' k) i j x y
  )
  ⇒ a -| Cart  k φ n m |-> b  -- ^ A 'Cart k' morphism.
  → a -| Cart' k φ n m |-> b  -- ^ An equivalent 'Fix (CartF k)' morphism.
fixed' Id         = In IdF
fixed' (Emb m)    = In (EmbF m)
fixed' (g `Of` f) = In (fixed' g `OfF` fixed' f)
fixed' (f `Par` g) = In $ fixed' f `ParF` fixed' g
fixed' (Mul pn pm pn' pm' f g) = In $ MulF pn pm pn' pm' (fixed' f) (fixed' g)
fixed' (Ith     i f) = In $ IthF     i (fixed' f)
fixed' (Ith' pn i f) = In $ IthF' pn i (fixed' f)
fixed' Join   = In $ JoinF
fixed' Split  = In $ SplitF
fixed' Assoc  = In $ AssocF
fixed' Sing   = In $ SingF
fixed' Unsing = In $ UnsingF
fixed' (Lift1   f) = In $ Lift1F   (fixed' f)
fixed' (Bising  f) = In $ BisingF  (fixed' f)
fixed' (Bisplit f) = In $ BisplitF (fixed' f)
fixed' (Bijoin  f) = In $ BijoinF  (fixed' f)
fixed' (Biassoc f) = In $ BiassocF (fixed' f)
fixed' (Swap  i j) = In $ SwapF i j
-- fixed' (Swap' ) =
-- fixed' (Permute ) =
fixed'  Dup        = In $ DupF
fixed' (Dup'  n s) = In $ DupF' n s
fixed' (Fork        f g) = In $ ForkF        (fixed' f) (fixed' g)
fixed' (Fork' l n m f g) = In $ ForkF' l n m (fixed' f) (fixed' g)
fixed' (Idx i) = In $ IdxF i
fixed' (Del i) = In $ DelF i
fixed' (Sel i) = In $ SelF i
fixed'  Zip    = In $ ZipF
fixed' (ZipWith  f) = In $ ZipWithF (fixed' f)


{- | Convert a 'Cart\' k' morphism to a 'Cart k' morphism. -}
unfixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ k i x ⇒ Object' φ (Cart k) i x
  , ∀ i x. Object φ (Cart k) i x ⇒ Object' φ (Cart' k) i x
  )
  ⇒ a -| Cart' k φ n m |-> b  -- ^ A 'Fix (CartF k)' morphism.
  → a -| Cart  k φ n m |-> b  -- ^ An equivalent 'Cart k' morphism.
unfixed' (In IdF)         = Id
unfixed' (In (EmbF m))    = Emb m
unfixed' (In (g `OfF`  f)) = unfixed' g `Of`  unfixed' f
unfixed' (In (f `ParF` g)) = unfixed' f `Par` unfixed' g
unfixed' (In (MulF pn pm pn' pm' f g)) = Mul pn pm pn' pm' (unfixed' f) (unfixed' g)
unfixed' (In (IthF     i f)) = Ith     i (unfixed' f)
unfixed' (In (IthF' pn i f)) = Ith' pn i (unfixed' f)
unfixed' (In (JoinF))   = Join
unfixed' (In (SplitF))  = Split
unfixed' (In (AssocF))  = Assoc
unfixed' (In (SingF))   = Sing
unfixed' (In (UnsingF)) = Unsing
unfixed' (In (Lift1F   f)) = Lift1   (unfixed' f)
unfixed' (In (BisingF  f)) = Bising  (unfixed' f)
unfixed' (In (BisplitF f)) = Bisplit (unfixed' f)
unfixed' (In (BijoinF  f)) = Bijoin  (unfixed' f)
unfixed' (In (BiassocF f)) = Biassoc (unfixed' f)
unfixed' (In (SwapF i j)) = Swap i j
-- unfixed' (In SwapF') =
-- unfixed' (In PermuteF) =
unfixed' (In  DupF      ) = Dup
unfixed' (In (DupF' n s)) = Dup' n s
unfixed' (In (ForkF        f g)) = Fork        (unfixed' f) (unfixed' g)
unfixed' (In (ForkF' l n m f g)) = Fork' l n m (unfixed' f) (unfixed' g)
unfixed' (In (IdxF i)) = Idx i
unfixed' (In (DelF i)) = Del i
unfixed' (In (SelF i)) = Sel i
unfixed' (In  ZipF  )  = Zip
unfixed' (In (ZipWithF f)) = ZipWith (unfixed' f)



-- TODO lift constraint that the Proxy be the same before and after/make an alternative version?
{- | Given a function that maps primitive morphisms to morphisms in a target
category /t/, this constructs an algebra for recursion schemes. -}
mkAlg ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type).
  ( Cartesian φ t, MF.Zip φ t, Select φ t, Delete φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy   φ t
  -- ∀ x. ObjectOf k x ⇒ Object' t x
  )
  ⇒ (∀ n m a b. (
              -- ∀ x. ObjectOf k x ⇒ Object' t x
              ObjectOf φ k n a
            , ObjectOf φ k m b
            , Object   φ t n a
            , Object   φ t m b
            )
     ⇒ a -| k φ n m |-> b
     → a -| t φ n m |-> b
     )                            -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → NT' φ (CartF k t) t -- NatR
  -- → (CartF k) t :~> t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @φ @t
mkAlg _ (g `OfF` f)      = g ⊙ f
mkAlg α (EmbF    f)      = α f
mkAlg _ (f `ParF` g) = f *** g
mkAlg _ (MulF pn pm pn' pm' f g) = mul pn pm pn' pm' f g
mkAlg _ (IthF     i f) = ith     i f
mkAlg _ (IthF' pn i f) = ith' pn i f
mkAlg _  JoinF   = join
mkAlg _  SplitF  = split
mkAlg _  AssocF  = assoc
mkAlg _  SingF   = sing
mkAlg _  UnsingF = unsing
mkAlg _ (Lift1F   f) = lift1   f
mkAlg _ (BisingF  f) = bising  f
mkAlg _ (BisplitF f) = bisplit f
mkAlg _ (BijoinF  f) = bijoin  f
mkAlg _ (BiassocF f) = biassoc f
mkAlg _ (SwapF i j)  = swap i j
-- mkAlg _ SwapF' =
-- mkAlg _ PermuteF =
mkAlg _  DupF       = dup
mkAlg _ (DupF' n s) = dup' n s
mkAlg _ (ForkF        f g) = (△)        f g
mkAlg _ (ForkF' l n m f g) = fork l n m f g
mkAlg _ (IdxF i) = idx i
mkAlg _ (DelF i) = del i
mkAlg _ (SelF i) = sel i
mkAlg _  ZipF    = zip
mkAlg _ (ZipWithF f) = zipWith f



foldMap' ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (n ∷ Nat) (m ∷ Nat)
  (a ∷ κ) (b ∷ κ).
  ( Cartesian φ t, MF.Zip φ t, Select φ t, Delete φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy φ t
  -- , Object φ (Fix (CartF k)) n a
  -- , Object φ (Fix (CartF k)) m b
  -- , (∀ i x. Object φ (Fix (CartF k)) i x ⇒ Object' φ t i x)
  , (∀ i x. Object φ (Fix (CartF k)) i x ⇒ Object' φ t i x)
  , CartesianFunctor (CartF k) φ (Fix (CartF k)) t
  )
  ⇒ (∀ i j x y. (
                  ObjectOf φ k i x
                , ObjectOf φ k j y
                , Object   φ t i x
                , Object   φ t j y
                )
     ⇒ x -| k φ i j |-> y
     → x -| t φ i j |-> y
     )                            -- ^ A function mapping primitives (/k/-morphisms) into the target category.
  → (  a -| Fix (CartF k) φ n m |-> b
    →  a -|        t     φ n m |-> b
    )
foldMap' α = cata (mkAlg α)
