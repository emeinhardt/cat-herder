{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- |

module Cat.Sized.Diagonal.Class
  ( Diagonal ( DupObject
             , dup
             , dup'
             , (&&&)
             , fork
             )
  , DupObject'
  , (△)
  , dupRep
  , fork2
  , fork3
  ) where

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zip
  )

import Data.Kind (Type, Constraint)
import Data.Constraint.Trivial
  ( Unconstrained6 )

import Data.Proxy qualified as P
import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , natVal
  , pattern SNat
  , type (+)
  , type (*)
  , type (<=)
  )

import Data.Functor.Rep qualified as R
import Data.Functor.Rep
  ( Representable
  , Rep
  , tabulate
  )

import Cat.Operators (type (-|), type (|->))

import Cat.Sized.Category.Class
  ( Object
  , Sub (Sub)
  , (⊙)
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             )
  , (|.|), split
  )
import Cat.Sized.Semigroupoid (Object')
import qualified Data.List as L



{- | A monoidal category with diagonals permits "copying" an object.

Minimal definition if @Proxy φ k ~ SNat@: @(dup | dup'), ((&&&) | fork)@.
Minimal definition otherwise: @dup, (&&&)@. -}
class (Monoidal φ k) ⇒ Diagonal (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Extra constraints on mapping an object already in /φ/ with one
  multipicity to another multiplicity. -}
  type DupObject φ k (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ) ∷ Constraint
  type DupObject φ k n m a b = Unconstrained6 φ k n m a b


  -- TODO Figure out if it's best to expose a more general set of variables.
  {- | 'dup' maps an input length-/n/ product to one of length /m = s⋅n/.

  The default definition is in terms of @dup'@ when @Proxy φ k ~ SNat@. This
  can be useful when defining an instance with @deriving via@ or using a generic
  implementation like 'dupRep'. -}
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (b ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (a ∷ κ).
  -- dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (m ∷ Nat) (a ∷ κ).
  dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , KnownNat s
      -- , KnownNat m
      -- , KnownNat b
      , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
      -- , m ~ s * n
      -- , m ~ (s * n) + b
      , Object φ k      n  a
      , Object φ k (s * n) a
      , DupObject φ k n (s * n) a a
      -- , Object φ k ((s * n) + b) a
      -- , DupObject φ k n ((s * n) + b) a a
      )
      ⇒ a -| k φ n (s * n) |-> a
      -- ⇒ a -| k φ n ((s * n) + b) |-> a

  -- default dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (b ∷ Nat) (a ∷ κ).
  -- default dup ∷ ∀ (n ∷ Nat) (m ∷ Nat) (s ∷ Nat) (a ∷ κ).
  -- default dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (m ∷ Nat) (a ∷ κ).
  default dup ∷ ∀ (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , KnownNat s
      -- , KnownNat m
      -- , KnownNat b
      , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
      -- , m ~ s * n
      -- , m ~ (s * n) + b
      , Object φ k      n  a
      , Object φ k (s * n) a
      , DupObject φ k n (s * n) a a
      -- , Object φ k ((s * n) + b) a
      -- , DupObject φ k n ((s * n) + b) a a
      , SNat ~ Proxy φ k
      )
      ⇒ a -| k φ n (s * n) |-> a
      -- ⇒ a -| k φ n ((s * n) + b) |-> a
  dup = dup' @κ @φ @k @n @s @a (SNat @n) (SNat @s)
  -- dup =
  --   let f ∷ a -| k φ n (2 * n) |-> a
  --       f = id &&& id
  --       g ∷ a -| k φ n (m `Div` 2) |-> a
  --       g = undefined
  --       h ∷ a -| k φ n (m `Mod` 2) |-> a
  --       h = undefined
  --   in  undefined
  -- dup = let -- n_ = natVal (SNat @n)
  --           -- m_ = natVal (SNat @m)
  --           s_ = natVal (SNat @s)
  --       in  if   s_ > 1
  --           then (id @κ @φ @k @n @a) &&& (dup @κ @φ @k @n @(s - 1))
  --           else (id @κ @φ @k @n @a)
  -- dup = (id @κ @φ @k @1 @a) &&& (dup @κ @φ @k @(n - 1) @(m - 1))

  {-| Default implementation is in terms of 'dup'. -}
  dup' ∷ ∀ (n ∷ Nat) (s ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , KnownNat s
       , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
       , Object φ k      n  a
       , Object φ k (s * n) a
       , DupObject φ k n (s * n) a a
       )
       ⇒ (Proxy φ k) n
       → (Proxy φ k) s
       → a -| k φ n (s * n) |-> a
  dup' (_ ∷ (Proxy φ k) n) (_ ∷ (Proxy φ k) s) = dup @κ @φ @k @n @s @a

  infixr 3 &&&
  {- | The default implementation of is in terms of 'dup', provided that
  @Object φ k (l + l) a, Object φ k l (l + l) a a@ hold:

  >>> f &&& g = (f |.| g) . dup
  -}
  (&&&) ∷ ∀ (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        -- , l <= n + m
        , Object φ k l a
        , Object φ k n b
        , Object φ k m b
        , Object φ k (n + m) b
        , DupObject φ k l n a b
        , DupObject φ k l m a b
        , DupObject φ k l (n + m) a b
        )
        ⇒ a -| k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
        → a -| k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.

  default (&&&) ∷ ∀ (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
         ( KnownNat l, KnownNat n, KnownNat m
         -- , l <= n + m
         , Object φ k l a
         , Object φ k n b
         , Object φ k m b
         , Object φ k (n + m) b
         -- , DupObject φ k l n a b
         -- , DupObject φ k l m a b
         -- , DupObject φ k l (n + m) a b
         , Object φ k (l + l) a
         , DupObject φ k l (l + l) a a
         )
         ⇒ a -| k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
         → a -| k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
         → a -| k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.
  f &&& g = (f |.| g) ⊙ dup

  fork ∷ ∀ (l ∷ Nat) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
       ( KnownNat l, KnownNat n, KnownNat m
       , Object φ k l a
       , Object φ k n b
       , Object φ k m b
       , Object φ k (n + m) b
       , DupObject φ k l n a b
       , DupObject φ k l m a b
       , DupObject φ k l (n + m) a b
       )
       ⇒ (Proxy φ k) l
       → (Proxy φ k) n
       → (Proxy φ k) m
       → a -| k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
       → a -| k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
       → a -| k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.
  fork (_ ∷ (Proxy φ k) l) (_ ∷ (Proxy φ k) n) (_ ∷ (Proxy φ k) m) (f ∷ a -| k φ l n |-> b) (g ∷ a -| k φ l m |-> b)
    = (&&&) @κ @φ @k @l @n @m @a @b f g

  {-# MINIMAL (dup | dup'), ((&&&) | fork) #-}


{- | This is a "class synonym" for the type family 'DupObject'; it's often needed
to write quantified constraints. -}
class    (DupObject φ k n m a b)
  ⇒ DupObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ)
instance (DupObject φ k n m a b)
  ⇒ DupObject' (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ)


infixr 3 △
{- | Synonym for 'fork'/'&&&' that avoids clashing with "Control.Arrow". -}
(△) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (l ∷ Nat) (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( KnownNat l, KnownNat n, KnownNat m
        , Object φ k l a
        , Object φ k n b
        , Object φ k m b
        , Object φ k (n + m) b
        , DupObject φ k l n a b
        , DupObject φ k l m a b
        , DupObject φ k l (n + m) a b
        , Diagonal φ k
        )
        ⇒ a -| k φ l  n      |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l      m  |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ m b/.
        → a -| k φ l (n + m) |-> b  -- ^ A /k/-morphism from /φ l a/ to /φ (n + m) b/.
(△) = (&&&)



instance (Diagonal φ k, Proxy φ k ~ Proxy φ (o `Sub` k)) ⇒ Diagonal φ (o `Sub` k) where
  type DupObject φ (o `Sub` k) n m a b = DupObject φ k n m a b
  dup = Sub dup
  -- dup'  = Sub .:   dup'
  (Sub f) &&& (Sub g) = Sub (f &&& g)
  fork pl pn pm (Sub f) (Sub g) = Sub $ fork pl pn pm f g



{- | This is a generic implementation for 'dup' in @Sized (->)@ in terms of
'tabulate' and 'index' for for any sized functor /φ/ with suitable
[Representable](https://hackage.haskell.org/package/adjunctions-4.4.2/docs/Data-Functor-Rep.html#t:Representable)
instances. -}
dupRep ∷ ∀ (φ ∷ Nat → Type → Type) (n ∷ Nat) (s ∷ Nat) (a ∷ Type).
       ( KnownNat n
       , KnownNat s
       , 1 <= s                       -- GHC (unhelpfully) warns about this being redundant
       , Representable (φ n)
       , Representable (φ (s * n))
       , Integral (Rep (φ n))
       , Integral (Rep (φ (s * n)))
       )
       ⇒ φ      n  a
       → φ (s * n) a
dupRep fa =
  let m = fromIntegral $ natVal (P.Proxy @(s * n))
      tab i = fa `R.index` (fromIntegral (i `div` m))
  in  tabulate tab


{- | Specialized variant of '&&&' for pairs of functions with same-sized output
products that separates the outputs.

>>> fork2 f g = split ⊙ (f &&& g)
-}
fork2 ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (l ∷ Nat) (n ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( KnownNat l, KnownNat n
        , Object φ k l a
        , Object φ k n b
        , Object φ k (n + n) b
        , Object φ k 2 (φ n b)
        , DupObject φ k l  n      a b
        , DupObject φ k l (n + n) a b
        , Diagonal φ k
        )
        ⇒ a -| k φ l n |-> b        -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l n |-> b        -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l 2 |-> (φ n b)  -- ^ A /k/-morphism from /φ l a/ to /φ 2 (φ n b)/.
fork2 f g = split ⊙ (f &&& g)


{- | Specialized variant of '&&&' for pairs of functions with same-sized output
products that separates the outputs.

>>> fork3 f g h = split ⊙ (f &&& g &&& h)  -- NB &&& associates to the right
-}
fork3 ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (l ∷ Nat) (n ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( KnownNat l, KnownNat n
        , Object φ k l a
        , Object φ k n b
        , Object φ k (2 * n) b
        , Object φ k (3 * n) b
        , Object φ k 2 (φ n b)
        , Object φ k 3 (φ n b)
        , DupObject φ k l      n  a b
        , DupObject φ k l (2 * n) a b
        , DupObject φ k l (3 * n) a b
        , Diagonal φ k
        )
        ⇒ a -| k φ l n |-> b        -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l n |-> b        -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l n |-> b        -- ^ A /k/-morphism from /φ l a/ to /φ n b/.
        → a -| k φ l 3 |-> (φ n b)  -- ^ A /k/-morphism from /φ l a/ to /φ 3 (φ n b)/.
fork3 f g h = split ⊙ (f &&& g &&& h)
