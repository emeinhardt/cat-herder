{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{- |

-}

module Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , Unit
             , (***)
             , mul
             , ith
             , ith'
               -- * Nested product combinators
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

    -- * Alternate operators/sugar
  , (+++)
  , (|.|)
  , (|+|)
  , (⊗)
  , (⊕)

    -- * Endofunctor combinators
  , omap
  , gmap

    -- ** Newtypes for endofunctor instances
  , Solo   (Solo  , unSolo)
  , Factor (Factor, unFactor)
  -- , ProdK
  ) where

{- TODO Move join, split, dist etc — anything that assumes nested products are possible
into a subclass for monoidal categories with monadic product functors where nested products
are permitted as objects. -}

{- TODO I think it's reasonable to expect that every (/every/?) plausible monoidal
product functor /φ/ used with the 'Monoidal' class will be

 - Traversable
 - Distributive + Representable

Check if this expectation is warranted, and if so, add typeclasses to this package.
-}

{- TODO foldMap

Figure out how something like 'ProdK'/'ProdF' might be useful for 'foldMap' /
recursion schemes (ensuring/helping to map products to products) or remove it.
-}

import Prelude hiding
  ( id
  , (.)
  , Functor
  , fmap
  , zip
  , zipWith
  )
-- Module convention: Use '∘' for composition in Hask
import Prelude.Unicode ((∘))


import Data.Kind (Type)

import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , pattern SNat
  , type (+)
  , type (*)
  )
import Data.Finite
  ( Finite
  )


import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Category.Class
    ( Category
    , Semigroupoid (Object
                   )
    , (⊙)
    , Sub (Sub, unSub)
    )


import Cat.Sized.Functor
  ( Functor
  , fmap
  )


-- -- TODO @stub: type family for functors between monoidal categories with
-- -- different product functors lets you write (φ n a) as ((ProdK φ n) a)
-- type family ProdK (φ ∷ Nat → κ → κ) (n ∷ Nat) where
--   ProdK φ n = (φ n)

-- -- TODO @stub: type family for functors between monoidal categories with
-- -- different product functors lets you write (φ n a) as ((ProdK φ n) a)
-- {- |

-- >>> import Cat.Sized.Semigroupoid.Free.Data (N(..))
-- >>> :k! (ProdF VS.Vector N Bool)
-- >> (ProdF VS.Vector N Bool) ∷ Type
-- >> = Bool
-- >>> :k! (ProdF VS.Vector N (VS.Vector 3 Bool))
-- >> (ProdF VS.Vector N (VS.Vector 3 Bool)) ∷ Type
-- >> = N 3 Bool
-- >>> :k! (ProdF VS.Vector N (VS.Vector 3 (VS.Vector 2 Bool)))
-- (ProdF VS.Vector N (VS.Vector 3 (VS.Vector 2 Bool))) :: Type
-- = N 3 (N 2 Bool)
-- -}
-- type family ProdF (φ ∷ Nat → κ → κ) (γ ∷ Nat → κ → κ) (a ∷ κ) where
--   ProdF φ γ (φ n x) = (γ n (ProdF φ γ x))
--   ProdF φ γ (    x) = (               x )
--   -- ProdF φ γ (φ n)   = (γ n)



{- |

=== What does this typeclass model?

As explained in the package description, README, and "Cat", this does not quite
model a monoidal category per se: where a monoidal category is a category that
has a distinguished associated bifunctor — conventionally called the /tensor
product/ and denoted with the infix operator ⊗ — this typeclass /only/ models
morphisms between finite products of objects.

Consequently, (polychromatic) [PROPs](https://ncatlab.org/nlab/show/PROP) or
[concategories](https://www.cl.cam.ac.uk/events/syco/2/slides/levy.pdf) are a
better description of what this typeclass models; nevertheless, for continuity,
discoverability, principle of least surprise, etc. this typeclass is named
\"Monoidal\".

In more Haskell-adjacent terms, any product functor /φ/ in a @Monoidal φ k@
instance probably ought to have instances for @Applicative@, @Traversable@, and
@Representable@. (In cartesian closed categories — like @->@ — @Applicative@ is
synonymous with being a monoidal endofunctor.)

All of the methods besides @***@\/@mul@ and @ith@\/@ith\'@ only make sense for
monadic functors; that may be inappropriate for modelling some domains and such
methods may be split off into a separate typeclass.


=== Minimal definition

Minimal definition if @Proxy k ~ SNat@: @(((***) | mul), (ith | ith'), join, split@.

Minimal definition otherwise: @(***), ith, join, split@. -}
class (Category φ k) ⇒ Monoidal (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | A proxy type for lengths. -}
  type Proxy (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) ∷ Nat → Type
  type Proxy (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) = SNat

  {- | The unit object with respect to the tensor product. -}
  type Unit (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ κ
  type Unit φ k n a = φ 0 a


  infixr 3 ***
  {- | The tensor operation composing two morphisms in parallel, enforcing that
  multiplicities add.

  The default definition is in terms of 'mul', the variant that uses proxies. -}
  (***) ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
        ( KnownNat n , KnownNat m
        , KnownNat n', KnownNat m'
        , Object φ k  n       a, Object φ k  m       b
        , Object φ k      n'  a, Object φ k      m'  b
        , Object φ k (n + n') a, Object φ k (m + m') b
        )
        ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
        → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
        → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".

  default (***) ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
                    (n' ∷ Nat) (m' ∷ Nat)
                    (a  ∷ κ)   (b  ∷ κ).
        ( KnownNat n , KnownNat m
        , KnownNat n', KnownNat m'
        , Object φ k  n       a, Object φ k  m       b
        , Object φ k      n'  a, Object φ k      m'  b
        , Object φ k (n + n') a, Object φ k (m + m') b
        , SNat ~ Proxy φ k
        )
        ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
        → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
        → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
  (***) = mul (SNat @n) (SNat @m) (SNat @n') (SNat @m')

  {- | Variant of '***' that accepts explicit runtime proxies for lengths.

  Default definition is in terms of '***'. -}
  mul ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
          (n' ∷ Nat) (m' ∷ Nat)
          (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      )
      ⇒ (Proxy φ k) n  → (Proxy φ k) m
      → (Proxy φ k) n' → (Proxy φ k) m'
      → a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".

  default mul ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
                  (n' ∷ Nat) (m' ∷ Nat)
                  (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      , SNat ~ Proxy φ k
      )
      ⇒ (Proxy φ k) n  → (Proxy φ k) m
      → (Proxy φ k) n' → (Proxy φ k) m'
      → a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".

  mul (SNat @n_) (SNat @m_) (SNat @n_') (SNat @m_') =
    (***) @κ @φ @k @n_ @m_ @n_' @m_'
  -- Triggers a non-exhaustive pattern matches warning because of UnsafeSNat

  {- | Analogue of 'first' and 'second' from 'Control.Arrow': lift a morphism /f/
  from /a/ to /b/ to one on /n/ copies of /a/ to /n/ copies of /b/, with
  /f ∷ a -| k φ 1 1 |-> a/ at position /i/ in the /n/-length stack of morphisms,
  sandwiched between stacks of the identity morphism.

  The default definition is in terms of the variant that takes an explicit proxy
  for size. -}
  ith ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , Object φ k 1 a
      , Object φ k n a
      )
      ⇒ Finite n
      → a -| k φ 1 1 |-> a  -- ^ A /k/-morphism that acts on a single index of an /n/-product.
      → a -| k φ n n |-> a

  default ith ∷ ∀ (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , Object φ k 1 a
      , Object φ k n a
      , SNat ~ Proxy φ k
      )
      ⇒ Finite n
      → a -| k φ 1 1 |-> a
      → a -| k φ n n |-> a
  ith (fn ∷ Finite n) (f ∷ k φ 1 1 a a) = ith' (SNat @n) fn f

  {- | Variant of 'ith' that takes a proxy for communicating length information.

  Default implementation is in terms of 'ith'. -}
  ith' ∷ ∀ (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , Object φ k 1 a
       , Object φ k n a
       )
       ⇒ (Proxy φ k) n
       → Finite n
       → a -| k φ 1 1 |-> a  -- ^ A /k/-morphism that acts on a single index of an /n/-product.
       → a -| k φ n n |-> a
  ith' (_ ∷ (Proxy φ k) n) (fn ∷ Finite n) (f ∷ k φ 1 1 a a)
    = ith @κ @φ @k @n @a fn f

  {- | An analogue of @pure@ or @singleton@ for values already wrapped in the
   monoidal product /φ/: introduce a single size- and order-preserving layer of
   nesting such that

  >>> unsing ⊙ sing ≡ id

  The default implementation is @sing ≝ split@. -}
  sing ∷ ∀ (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , Object φ k n      a
        , Object φ k 1 (φ n a)
        )
        ⇒ a -| k φ n 1 |-> φ n a
  sing = split

  {- | An analogue of @extract@ for values already wrapped in a trivial layer of the
  monoidal product /φ/: remove a single size- and order-preserving layer of nesting
  such that

  >>> unsing ⊙ sing ≡ id

  The default implementation is @unsing ≝ join@; for a @Semicartesian@ category,
  @idx 0@ is probably a better choice. -}
  unsing ∷ ∀ (n ∷ Nat) (a ∷ κ).
         ( KnownNat n
         , Object φ k 1 (φ n a)
         , Object φ k n      a
         )
         ⇒ φ n a -| k φ 1 n |-> a
  unsing = join

  {- | Inverse of 'split'. Collapse a layer of nesting such that

  >>> join ⊙ split ≡ id

  If /φ/ has a @Monad@ instance, this will likely coincide with the monadic join
  (hence the name) — probably implemented by default as @bind id@. -}
  join ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , Object φ k      n (φ m a)
       , Object φ k (m * n)     a
       )
       ⇒ φ m a -| k φ n (n * m) |-> a

  {- | Inverse of 'join'. Factor an /n/-ary /φ/ product into equal-sized chunks,
  preserving the overall size and order, such that

  >>> join ⊙ split ≡ id
  -}
  split ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , Object φ k (m * n)     a
        , Object φ k      n (φ m a)
        )
        -- ⇒ a -| k φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| k φ (n * m) n |-> φ m a

  -- TODO Consider renaming dist to something more transparent and less likely
  -- to clash — "assoc"?
  {- | Reassociate (i.e. preserving order) an /n/-product of /m/-products into an
   /m/-product of /n/-products.

  In other words, given a nested input @as' ∷ φ n (φ m a)@ whose flattened
  version is @as ∷ φ (n * m) a = join as'@, this method returns
  @as'' ∷ φ m (φ n a)@ such that @join as' ≡ join as''@: it maps equal sized
  factorings of @as@ of one granularity — an /n/-product of /m/-products — to the
  dual regrouping — an /m/-product of /n/-products.

  For example, a nested 3-sequence of 2-sequences schematically represented as
  @(ab)(cd)(ef)@ should be mapped to @(abc)(def)@, a 2-sequence of 3-sequences.

  Note that this has the same type signature as @zip@ in
  "Cat.Sized.Functor.Monoidal" but @zip@ is /not/ order-preserving: @zip@ should
  map the schematic example @(ab)(cd)(ef)@ to @(ace)(bdf)@.

  Default definition when @Object φ k (m * n) a@ and @(n * m) ~ (m * n)@ hold:
  @assoc = split ⊙ join@. -}
  assoc ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
        ( KnownNat n, KnownNat m
        , Object φ k n (φ m a)
        , Object φ k m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| k φ n m |-> (ProdK φ n) a
        ⇒ φ m a -| k φ n m |-> φ n a

  default assoc ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , Object φ k      n (φ m a)
        , Object φ k  m     (φ n a)
        , Object φ k (m * n)     a
        , (n * m) ~ (m * n)
        )
        -- ⇒ (ProdK φ m) a -| k φ n m |-> (ProdK φ n) a
        ⇒ φ m a -| k φ n m |-> φ n a
  assoc = split ⊙ join


  {- | Introduce a single size-preserving (and singleton) layer of
  nesting to each side of a morphism without changing the outermost product
  layer.

  Default:

  >>> lift1 f ≝ split ⊙ f ⊙ join
  -}
  lift1 ∷ ∀ (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , Object φ k n      a
        , Object φ k m      b
        , Object φ k n (φ 1 a)
        , Object φ k m (φ 1 b)
        )
        ⇒     a -| k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| k φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.
  lift1 f = split ⊙ f ⊙ join

  {- | Introduce a single size-preserving layer of nesting by
  wrapping the outermost product with a trivial singleton product.

  Default:

  >>> bising f ≝ sing ⊙ f ⊙ unsing
  -}
  bising ∷ ∀ (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , Object φ k n      a
         , Object φ k m      b
         , Object φ k 1 (φ n a)
         , Object φ k 1 (φ m b)
         )
         ⇒     a -| k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| k φ 1 1 |-> φ m b  -- ^ An equivalent morphism with one trivial /outer/ layer of nesting.
  bising f = sing ⊙ f ⊙ unsing


  {- | Introduce a single layer of nesting to each side of a morphism (while
  preserving the overall size of each and the original order) by factoring out
  some equal-sized grouping.

  Inverse of 'bijoin'.

  Default:

  >>> bisplit f ≝ split ⊙ f ⊙ join
  -}
  bisplit ∷ ∀ (n ∷ Nat) (m ∷ Nat)
              (i ∷ Nat) (j ∷ Nat)
              (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , Object φ k (i * n)     a
    , Object φ k (j * m)     b
    , Object φ k      n (φ i a)
    , Object φ k      m (φ j b)
    )
    ⇒     a -| k φ (i * n) (j * m) |->     b  -- ^ A /k/ morphism whose products on either side can be factored.
    → φ i a -| k φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").
  bisplit f = split ⊙ f ⊙ join


  {- | Remove a single layer of nesting on each side of a morphism (while preserving
  the overall size of each and the original order) by distributing in some equal
  sized grouping.

  Inverse of 'bisplit'.

  Default:

  >>> bijoin f ≝ join ⊙ f ⊙ split
  -}
  bijoin ∷ ∀ (n ∷ Nat) (m ∷ Nat)
             (i ∷ Nat) (j ∷ Nat)
             (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , Object φ k (i * n)     a
    , Object φ k (j * m)     b
    , Object φ k      n (φ i a)
    , Object φ k      m (φ j b)
    )
    ⇒ φ i a -| k φ      n       m  |-> φ j b  -- ^ A /k/ morphism with nested products.
    →     a -| k φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").
  bijoin f = join ⊙ f ⊙ split


  {- | Reassociate ("reshape") both the source and target in a size- and
  order-preserving fashion, taking any arrow

  >>> φ i a -| k φ n m |-> φ j b

  to an isomorphic arrow (i.e. @i * n ~ i' * n'@ and @j * m ~ j' * m'@ must hold)

  >>> φ i' a -| k φ n' m' |-> φ j' b

  Like 'bijoin' and 'bisplit', this sandwiches a monoidal arrow between regrouping
  operations — both 'split' and 'join'.

  Default:

  >>> biassoc f ≝ bisplit ∘ bijoin $ f ≡ split ⊙ join ⊙ f ⊙ split ⊙ join
  -}
  biassoc ∷ ∀ (n  ∷ Nat) (m  ∷ Nat)
              (i  ∷ Nat) (j  ∷ Nat)
              (n' ∷ Nat) (m' ∷ Nat)
              (i' ∷ Nat) (j' ∷ Nat)
              (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , Object φ k       n  (φ i  a)
    , Object φ k       m  (φ j  b)
    , Object φ k       n' (φ i' a)
    , Object φ k       m' (φ j' b)
    , Object φ k (i' * n')      a
    , Object φ k (j' * m')      b
    )
    ⇒ φ i  a -| k φ n  m  |-> φ j  b  -- ^ A /k/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| k φ n' m' |-> φ j' b
  biassoc = bisplit ∘ bijoin

  {-# MINIMAL ( (***) | mul ), ( ith | ith' ), join, split  #-}



infixr 2 +++
{- | A synonym for '(***)' intended for use in contexts where you may prefer to
distinguish between two monoidal structures on the same category. -}
(+++) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( Monoidal φ k
      , KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      )
      ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
(+++) = (***)


infixr 3 |.|
{- | Alternate synonym for '***' that avoids clashing with "Control.Arrow".

Mnemonic: parallel or horizontal composition.  -}
(|.|) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( Monoidal φ k ) ⇒
      ( KnownNat n , KnownNat m
      , KnownNat n', KnownNat m' ) ⇒
      ( Object φ k  n       a, Object φ k  m       b ) ⇒
      ( Object φ k      n'  a, Object φ k      m'  b ) ⇒
      ( Object φ k (n + n') a, Object φ k (m + m') b
      )
      -- ( Monoidal φ k
      -- , KnownNat n , KnownNat m
      -- , KnownNat n', KnownNat m'
      -- , Object φ k  n       a, Object φ k  m       b
      -- , Object φ k      n'  a, Object φ k      m'  b
      -- , Object φ k (n + n') a, Object φ k (m + m') b
      -- )
      ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
(|.|) = (***)


infixr 3 ⊗
{- | Alternate synonym for '***' that avoids clashing with "Control.Arrow" and emphasizes that
'***' is the tensor product for its category. -}
(⊗) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( Monoidal φ k
      , KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      )
      ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
(⊗) = (***)


infixr 2 |+|
{- | Alternate synonym for '+++' that avoids clashing with "Control.Arrow"; like
'+++', this is a synonym for '(***)' intended for use in contexts where you may
prefer to distinguish between two monoidal products in the same category or
otherwise emphasize its sum-like nature.

Mnemonic: parallel or horizontal composition.  -}
(|+|) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( Monoidal φ k
      , KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      )
      ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
(|+|) = (***)


infixr 3 ⊕
{- | Alternate synonym for '***' that avoids clashing with "Control.Arrow"; like
'+++', this is a synonym for '(***)' intended for use in contexts where you may
prefer to distinguish between two monoidal products in the same category or
otherwise emphasize its sum-like nature. -}
(⊕) ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( Monoidal φ k
      , KnownNat n , KnownNat m
      , KnownNat n', KnownNat m'
      , Object φ k  n       a, Object φ k  m       b
      , Object φ k      n'  a, Object φ k      m'  b
      , Object φ k (n + n') a, Object φ k (m + m') b
      )
      ⇒ a -| k φ  n        m       |-> b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
      → a -| k φ      n'       m'  |-> b  -- ^ A /k/-morphism from /φ n' a/ to /φ m' b/.
      → a -| k φ (n + n') (m + m') |-> b  -- ^ A /k/-morphism constructed by placing the first and second morphisms "side-by-side".
(⊕) = (***)



instance (Monoidal φ k) ⇒ Monoidal φ (o `Sub` k) where
  type Proxy φ (o `Sub` k) = Proxy φ k
  type Unit  φ (o `Sub` k) n a = Unit φ k n a

  (Sub f) *** (Sub g) = Sub (f *** g)

  mul pn pm pn' pm' (Sub f) (Sub g) = Sub $ mul pn pm pn' pm' f g

  ith i (Sub f) = Sub $ ith i f

  sing     = Sub   sing
  unsing   = Sub   unsing
  join     = Sub   join
  split    = Sub   split
  assoc    = Sub   assoc
  bisplit  = Sub ∘ bisplit ∘ unSub
  bijoin   = Sub ∘ bijoin  ∘ unSub
  biassoc  = Sub ∘ biassoc ∘ unSub



{- | This newtype (essentially a named derivation) provides an (unsized)
endofunctor /φ 1/ for /k φ n n/ when /k/ is a monoidal category with product
functor /φ/, i.e. it provides the functor instance associated with 'lift1'
where:

>>> fmap ≝ Solo ∘ lift1 ∘ unSolo

and hence transforms every arrow

>>> a -| k φ n m |-> b

to an arrow

>>> φ 1 a -| k φ n m |-> φ 1 b
-}
newtype Solo (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ) (b ∷ κ)
  = Solo { unSolo ∷ a -| k φ n m |-> b }

deriving newtype instance (Semigroupoid φ k) ⇒ Semigroupoid φ (Solo k)
deriving newtype instance (Category     φ k) ⇒ Category     φ (Solo k)
deriving newtype instance (Monoidal     φ k) ⇒ Monoidal     φ (Solo k)



{- | This newtype provides an (unsized) endofunctor @φ i@ for
@k φ (i * n) (i * n)@ when @k@ is a monoidal category with product functor @φ@,
i.e. it provides the functor instance associated with a symmetrized special
case of 'bisplit':

>>> fmap ≝ bisplit

Putting it punchily, this offers a kind of APL-style @reshape@ as a functor,
taking every arrow

>>> a -| φ k (i * n) (i * n) |-> b

to an arrow

>>> φ i a | φ k n n |-> φ i b

-}
newtype Factor (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ) (b ∷ κ)
  = Factor { unFactor ∷ a -| k φ n m |-> b }

deriving newtype instance (Semigroupoid φ k) ⇒ Semigroupoid φ (Factor k)
deriving newtype instance (Category     φ k) ⇒ Category     φ (Factor k)
deriving newtype instance (Monoidal     φ k) ⇒ Monoidal     φ (Factor k)


-- TODO Experiment with whether a newtype could solve this problem without layer
-- shuffling; alternatively, make this a @Monoidal@ method, introduce a
-- @Functor@ subclass: this is a common operation that should be low cost to
-- use.
{- | The need for this combinator is a (temporary) artifact of two things. First,
the basic morphism shape:

>>> a -| k φ n m |-> b  ≈  φ n a `k` φ m b

(NB @k@ can't actually have the same type on both sides of this ≈.)

Second, the current restriction in @Cat.Sized.Functor@ that @fmap@ must preserve
product cardinality.

If you want to lift a morphism from

  - @φ n a@ to @φ m b@

to a morphism from

  - @φ l (φ n a)@ to @φ l (φ m b)@

you can't simply use @fmap@ without any further combinators; on the other hand,
@fmap@ alone /would/ let you lift your morphism to map

  - @φ n (φ l a)@ to @φ m (φ l b)@.

This combinator wraps @fmap@ in extra combinators that let you use a @Functor@
instance to change the /outermost/ layer of a morphism:

>>> omap f ≝ bijoin $ fmap $ bising f

In words,

1. @bising f@ introduces an outer singleton layer of nesting, "pushing" the
   existing products to a position where they can be wrapped in a @φ l@ layer,
   — assuming @φ l@ has the relevant @Functor@ instance:

> (bising f) ∷ φ n a -| k φ 1 1 |-> φ m b
> ≡ sing  ⊙ f ⊙ unsing
> ≡ split ⊙ f ⊙ join

2. @fmap@ then introduces @φ l@ layers to the source and target:

> (fmap $ bising f) ∷ φ l (φ n a) -| k φ 1 1 |-> φ l (φ m b)

3. @bijoin@ then collapses the two outer layers of nesting just introduced by
@bising@ and @fmap@ into one layer with the same multiplicity as that introduced
by @fmap@:

> (bijoin $ fmap $ bising f) ∷ φ n a -| t φ l l |-> φ m b
> ≡ join ⊙ (fmap $  bising  f          ) ⊙ split
> ≡ join ⊙ (fmap $ (sing  ⊙ f ⊙ unsing)) ⊙ split
> ≡ join ⊙ (fmap $ (split ⊙ f ⊙ join  )) ⊙ split

This method (or its default implementation) should be obviated in the future.
-}
omap ∷ ∀ l φ r t n m a b.
     ( KnownNat l, KnownNat n, KnownNat m
     , Object φ r n           a  , Object φ r m           b
     , Object φ r 1      (φ n a) , Object φ r 1      (φ m b)
     , Object φ t 1 (φ l (φ n a)), Object φ t 1 (φ l (φ m b))
     , Object φ t l      (φ n a) , Object φ t l      (φ m b)
     , Functor (φ l) φ φ r t
     , Monoidal φ r, Monoidal φ t
     )
     ⇒     a -| r φ n m |->     b  -- ^ An /r/-morphism from /φ n a/ to /φ m b/.
     → φ n a -| t φ l l |-> φ m b  -- ^ A /t/-morphism from /φ l (φ n a)/ to /φ l (φ m b)/.
omap = bijoin ∘ gmap


{- | Generalized 'omap' that works with endofunctors /γ/ on a monoidal category /k φ/
besides /φ l/.

>>> gmap f ≝ fmap $ bising f
-}
gmap ∷ ∀ γ φ r t n m a b.
     ( KnownNat n, KnownNat m
     , Object φ r n         a  , Object φ r m         b
     , Object φ r 1    (φ n a) , Object φ r 1    (φ m b)
     , Object φ t 1 (γ (φ n a)), Object φ t 1 (γ (φ m b))
     , Functor γ φ φ r t
     , Monoidal φ r, Monoidal φ t
     )
     ⇒        a  -| r φ n m |->        b
     → γ (φ n a) -| t φ 1 1 |-> γ (φ m b)
gmap = fmap ∘ bising

