{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{- | A (lax) functor from one monoidal category /r/ with product /φ/ to another
category /t/ with product /γ/ that preserves the monoidal structure of /r/ is
defined by

 - A type constructor /η/.
 - A "Cat.Sized.Functor" instance mapping morphisms to morphisms in a
   size-preserving way.
 - A mapping from the unit /v/ of /t/ to /η u/, where /u/ is the unit of /r/.
 - A natural transformation for all /i/, /a/ from /γ i (η a)/ to /η (φ i a)/.

For now at least, the main use case of such a functor is defining an analogue of
/zip/. Accordingly, this module contains a typeclass for monoidal /endo/functors
and another typeclass for /zip/ further specialized to a monoidal category's own
product functor. -}

{- TODO
 - Traversable instances
 - Distributive instances
 - Consider renaming this to something less namespace-clash-y + transparent:
   "Preapplicative"?

-}

module Cat.Sized.Functor.Monoidal
  ( -- * Monoidal functors
    MonoidalEndo ( splat
                 )
  , OpMonoidalEndo ( unsplat
                   )
  , Zip ( zip
        , zipWith
        )

    -- * Traversable / Distributive
  , TraversableEndo ( sequence
                    , traverse
                    , consume
                    )
  , DistributiveEndo ( distribute
                     , collect
                     )
  ) where

import Prelude hiding
  ( Functor
  , fmap
  , zip
  , zipWith
  , Traversable
  , sequence
  , traverse
  , id
  )
import Prelude.Unicode ((∘))

import Data.Kind ( Type )
import GHC.TypeNats
  ( KnownNat
  , Nat
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

-- import Data.Functor qualified as F

import Cat.Sized.Functor
  ( Functor
  , fmap
  , Fix ( In
        , out
        )
  )
import Cat.Sized.Semigroupoid
  ( Object
  , (⊙)
  , (>>>)
  )
import Cat.Sized.Category
  ( id
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( -- Unit
               unsing
             )
  , omap
  )



{- | An endofunctor /γ/ with respect to a monoidal category /k/ whose finite,
/n/-ary, homogeneous product functor is /φ/ is an instance of this class iff it
preserves the monoidal properties of the product /φ/.

=== "It's @Applicative@, Jim — but not as we know it."

In the setting of `(->)` — a /Cartesian closed/ category — the analogue of this
typeclass is often presented as something perfectly equivalent to @Applicative@
but with fewer and much simpler laws. Below is an abbreviated presentation of
that provided as context for this typeclass.

> -- "Functor" here is the familiar "Data.Functor"
> class (Functor φ) ⇒ Monoidal φ where
>   (<**>) ∷ φ a → φ b → φ (a, b)  -- ≈ a "zip"-like operation; must be associative
>   unit   ∷ φ ()                  -- Law: ∀ φa ∷ φ a. unit <**> φa ≅ φa ≅ φa <**> unit

Unsurprisingly, @\<**\>@ is expected to be associative and have @unit@ as a
two-sided identity. Finally, there is a law that must hold describing how /φ/
acts on products of morphisms — /naturality/:

> -- (***) here is the familiar one from "Control.Arrow"
> fmap (f *** g) (φa <**> φb) ≡ fmap f φa <**> fmap g φb
>
> -- Equivalently re-expressed in point-free style for use further below:
> -- Assuming @f ∷ a → b, g ∷ c → d, π₁ ∷ (a,b) → a, π₂ ∷ (a,b) → b@,
> fmap (f *** g) ≡ (uncurry <**>)         -- ∷ (φ c, φ d) → φ (c, d)
>                . (fmap f  *** fmap g)   -- ∷ (φ a, φ b) → (φ c, φ d)
>                . (fmap π₁ &&& fmap π₂)  -- ∷ φ (a, b)   → (φ a, φ b)
>

Every @Applicative@ instance has an instance of the @Monoidal@ typeclass above,
and vice versa:

> instance (Applicative φ) ⇒ Monoidal φ where
>   φa <**> φb  = (,) <$> φa <*> φb
>   unit        = pure ()
>
> instance (Monoidal φ) ⇒ Applicative φ where
>   (φab ∷ φ (a → b)) <*> φa = uncurry ($) <$> (φab <**> φa)  -- NOTE: "uncurry" and "$" indicate we are in a closed category
>   pure                     = fmap (const a) unit

However, outside of the context of categories where every morphism is an object
of the category (i.e. closed categories), the type of @\<*\>@ doesn't make
sense, and hence we won't in general be able to define an instance for
@Monoidal@ in terms of @Applicative@ in such settings.

Similarly, outside of the context of monoidal categories where the tensor is
Cartesian (or outside of contexts where it's literally @(,)@), we need to adapt
the usual presentation of @Monoidal@ to express the general idea of "preserves
the monoidal properties of the monoidal product" — or to express the specific
adaptation relevant for the current setting.

Next, note that outside of the context of monoidal categories that are /both/
Cartesian and closed, the curried form of @\<**\>@ is not equivalent to the
uncurried form, and the uncurried form is a little more transparent for seeing
what an appropriate generalization should be:

> (<**>) ∷  φ a → φ b  → φ (a, b)
>        ≅ (φ a , φ b) → φ (a, b)

In our setting of interest, below is a further sequence of type transformations
that takes you the rest of the way to this typeclass's @splat@ method:


>  φ a → φ b  → φ (a, b)
> (φ a , φ b) → φ (a, b)        -- Uncurrying
> (γ a , γ b) → γ (a, b)        -- Renaming φ to γ
> (γ a , γ a) → γ (a, a)        -- (,) is the product for ->; we want *homogeneous* products
>  γ a ⊗ γ a  → γ (a ⊗ a)       -- We don't nessarily want (,); we want some other notion of tensor product
>  φ 2 (γ a)  → γ (φ 2 a)       -- Instead of (,) or any ⊗, we want a finite /n/-ary homogeneous product φ in particular
> γ a -| k φ 2 1 |-> γ (φ 2 a)  -- Isomorphism in our setting, plus, instead of ->, we're in some monoidal category /k/ with product φ where all morphisms are between objects in an /n/-ary /φ/ product
> γ a -| k φ n 1 |-> γ (φ n a)  -- Generalize binary products to /n/-ary products


The extra @φ 1@ layer on the target is a a mild deviation from the most
transparent analogue of the @Monoidal@ type. (We can imagine adding a final call
to @Data.Tuple.Solo@'s constructor on the right-hand-side of the laws earlier.)
Besides that, associativity and unit laws should follow from the definition of
@φ@ for any lawful @Monoidal φ k@ instance. That leaves naturality. What should
the naturality law look like?

Staying close to the setting of binary products for clarity, the law is

> -- fmap is from "Cat.Sized.Functor"
> -- Other combinators are from "Cat.Sized.Monoidal" or "Cat.Sized.Diagonal"
> fmap (f *** g) ≅ splat
>                ⊙ ( fmap  f    ***  fmap  g   )  -- There should be a way to express this without recourse to &&&.
>                ⊙ ( fmap (π 1) &&&  fmap (π 2))

where

> f ∷ a -| p φ 1 1 |-> b
> g ∷ a -| p φ 1 1 |-> b
> π ∷ Finite n → a -| p φ n 1 |-> a
> (***) ∷ (a -| p φ i j |-> b) → (a -| p φ k l |-> b) → (a -| p φ (i + k) (j + l) |-> b)
> (&&&) ∷ (a -| p φ i j |-> b) → (a -| p φ i k |-> b) → (a -| p φ  i      (j + k) |-> b)
> splat ∷ γ a -| p φ n 1 |-> γ (φ n a)
> fmap  ∷ (a -| p φ i j |-> b) → (γ a -| p φ i j |-> γ b)

and hence:

> -- LHS of the law:
>  (f *** g) ∷ a -| p φ 2 2 |->   b
> -- so
> lhs ∷ γ a -| p φ 2 2 |-> γ b
> lhs = fmap (f *** g)
>
> -- RHS of the law:
>  fmap (π i)                 ∷ γ a -| p φ n 1 |-> γ a
> (fmap (π 1) &&& fmap (π 2)) ∷ γ a -| p φ n 2 |-> γ a
>  fmap f                     ∷ γ a -| p φ 1 1 |-> γ b
> (fmap f *** fmap g)         ∷ γ a -| p φ 2 2 |-> γ b
>
> rhs ∷ γ a -| p φ 2 1 |-> γ (φ 2 b)
> rhs = splat ⊙ (fmap f *** fmap g) ⊙ (fmap (π 1) &&& fmap (π 2))

The type of the LHS is (or must be for a lawful instance) isomorphic to that of
the RHS in our setting of interest:

>   γ a -| p φ 2 2 |-> γ      b
> ≅ γ a -| p φ 2 2 |-> γ (φ 1 b)
> ≅ γ a -| p φ 2 1 |-> γ (φ 2 b)



=== From 'MonoidalEndo' to 'Zip'

Recall the annotation above that @\<**\>@ is roughly @zip@-like. We arrive at the
@Zip@ typeclass below by further exploring what happens when /γ ≡ φ m/ for some
/m/ and /φ n a ≅ φ 1 (φ n a) ≅ φ n (φ 1 a)/:

@
γ   a -| k φ n 1 |-> γ   (φ n a)
φ m a -| k φ n 1 |-> φ m (φ n a)  -- Substitution
φ m a -| k φ n m |-> φ n a        -- Isomorphism
@

Setting /n = 2/:

@
φ m a -| k φ 2 m |-> φ 2 a
@

We see we have an analogue of the familiar @zip@ combinator: a /k/-morphism that
maps a pair of /m/-products to an /m/-product of pairs. Hence the @zip@ method
of the "Zip" typeclass offers an /n/-ary generalization of the familiar binary
zip, and offers the opportunity to replace the default definition with a bespoke
one that e.g. can skip the step of collapsing a layer of nesting a default
definition would use.
-}
class ( Functor  γ φ φ k k
      , Monoidal φ k
      )
  ⇒ MonoidalEndo (γ ∷ κ → κ) (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  splat ∷ ∀ (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , Object φ k n (γ      a )
        , Object φ k 1 (γ (φ n a))
        )
        ⇒ γ a -| k φ n 1 |-> γ (φ n a)

  -- TODO When would this be useful? Free monoidal constructions wrt Day convolution?
  -- unit ∷ ∀ (n ∷ Nat) (a ∷ κ).
  --      ( KnownNat n
  --      , Object φ k 1 (Unit φ k n a)
  --      , Object φ k 1 (γ (Unit φ k n a))
  --      )
  --      ⇒ Unit φ k n a -| k φ 1 1 |-> γ (Unit φ k n a)


class ( Functor  γ φ φ k k
      , Monoidal φ k
      )
  ⇒ OpMonoidalEndo (γ ∷ κ → κ) (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Inverse of 'splat': 'splat' distributes a monoidal category's product /φ/ over a
  product-preserving functor /γ/; 'unsplat' (un)distributes /γ/ over /φ/. -}
  unsplat ∷ ∀ (n ∷ Nat) (a ∷ κ).
          ( KnownNat n
          , Object φ k 1 (γ (φ n a))
          , Object φ k n (γ      a )
          )
          ⇒ γ (φ n a) -| k φ 1 n |-> γ a


-- TODO Morally, this should probably require a 'MonoidalEndo' instance
class Zip (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  {- | Default:

  >>> zip ≝ unsing ⊙ splat

  Note that the default requires a 'MonoidalEndo' instance, but an
  'OpMonoidalEndo' instance ought to also suffice.

  I suspect that in the context of finitary @Traversable@ + @Representable@
  product functors that is this package's remit, everything with a
  'MonoidalEndo' instance also has an 'OpMonoidalEndo' instance and vice versa.

  You will probably need to be in a symmetric monoidal (@Braided@; see @zipPerm@
  in "Cat.Sized.Braided") or cartesian/closed category to define an instance of @Zip@
  in terms of other available combinators.
  -}
  zip ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
      ( KnownNat n, KnownNat m
      , Object φ k n (φ m a)
      , Object φ k m (φ n a)
      )
      ⇒ φ m a -| k φ n m |-> φ n a  -- ^ A /k/-morphism taking an /n/-product of /m/-products to an aligned ("zipped") /m/-product of /n/-products.

  default zip ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
      ( KnownNat n, KnownNat m
      , Object φ k n (φ m a)
      , Object φ k 1 (φ m (φ n a))
      , Object φ k m (φ n a)
      , MonoidalEndo (φ m) φ k
      )
      ⇒ φ m a -| k φ n m |-> φ n a  -- ^ A /k/-morphism taking an /n/-product of /m/-products to an aligned ("zipped") /m/-product of /n/-products.
  zip = unsing ⊙ splat


  {- | 'zip' /n/ /φ l a/s together and then map a morphism over the resulting
  /l/-product.

  Default when object constraints hold:

  >>> zipWith f ≝ omap f ⊙ zip

  === 'zipWith'?

  Consider the type of the familiar Prelude 'zipWith' plus the following
  transformations:

  >   (a → b   → c) →  [a] → [b]  →         [c]          -- :t Prelude.zipWith
  > ( (a , b)  → c) → ([a] , [b]) →         [c]          -- Uncurrying
  > ( (a , a)  → b) → ([a] , [a]) →         [b]          -- Renaming c to b + we're interested in homogeneous products
  > (φ 2 a →     b) → φ 2 (φ l a) → φ l      b           -- Convert /(,)/ to /φ 2 -/ and /[-]/ to /φ l -/
  > (φ 2 a → φ 1 b) → φ 2 (φ l a) → φ l (φ 1 b)          -- Our morphisms of interest must map φ-products to φ-products
  > (φ n a → φ m b) → φ n (φ l a) → φ l (φ m b)          -- Generalize from binary products to /n/-ary products and from returning a single /b/ to /m/ /b/s.
  > (a -| k φ n m |-> b) → (φ l a -| k φ n l |-> φ m b)  -- Our morphisms are in /k/, not ->.
  -}
  zipWith ∷ ∀ (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ)   (b ∷ κ)
              (l ∷ Nat).
          ( KnownNat n, KnownNat m, KnownNat l
          , Object φ k      n      a  , Object φ k      m      b
          , Object φ k      n (φ l a)
          , Object φ k      l (φ n a) , Object φ k      l (φ m b)
          )
          ⇒     a -| k φ n m |->     b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
          → φ l a -| k φ n l |-> φ m b  -- ^ Zip an /n/ product of /(φ l a)/s together and then map the morphism over the resulting /l/ product.

  default zipWith ∷ ∀ (n ∷ Nat) (m ∷ Nat)
                      (a ∷ κ)   (b ∷ κ)
                      (l ∷ Nat).
          ( KnownNat n, KnownNat m, KnownNat l
          , Object φ k      n      a  , Object φ k      m      b
          , Object φ k      n (φ l a)
          , Object φ k      l (φ n a) , Object φ k      l (φ m b)
          , Object φ k      1 (φ n a) , Object φ k      1 (φ m b)
          , Object φ k 1 (φ l (φ n a)), Object φ k 1 (φ l (φ m b))
          , MonoidalEndo (φ l) φ k
          )
          ⇒     a -| k φ n m |->     b  -- ^ A /k/-morphism from /φ n a/ to /φ m b/.
          → φ l a -| k φ n l |-> φ m b  -- ^ Zip /n/ /(φ l a)/s together and then map the morphism over the resulting /l/ product.
  zipWith = (zip >>>) ∘ omap
  -- zipWith f = omap f ⊙ zip


instance (Zip φ (η (Fix η))) ⇒ Zip φ (Fix η) where
  zip = In zip
  zipWith = In ∘ zipWith ∘ out


{- | See Jaskelioff & Rypacek 2012,
[/An Investigation of the Laws of Traversals/](https://arxiv.org/abs/1202.2919).

-}
class (MonoidalEndo γ φ k)
  ⇒ TraversableEndo (γ ∷ κ → κ) (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Default:

  >>> sequence ≝ consume id
  -}
  sequence ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (a ∷ κ).
           ( KnownNat n
           , Object φ k n (γ (η a))
           , Object φ k n (η (γ a))
           , MonoidalEndo η φ k
           )
           ⇒ γ (η a) -| k φ n n |-> η (γ a)

  default sequence ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (a ∷ κ).
           ( KnownNat n
           , Object φ k n (γ (η a))
           , Object φ k n (η (γ a))
           , Object φ k n (γ a)
           , MonoidalEndo η φ k
           )
           ⇒ γ (η a) -| k φ n n |-> η (γ a)
  sequence = consume id

  {- | Default:

  >>> traverse ≝ sequence ⊙ fmap f
  -}
  traverse ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
           ( KnownNat n, KnownNat m
           , Object φ k n       a
           , Object φ k m (η    b)
           , Object φ k n    (γ a)
           , Object φ k m (η (γ b))
           , MonoidalEndo η φ k
           )
           ⇒   a -| k φ n m |-> η    b
           → γ a -| k φ n m |-> η (γ b)

  default traverse ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
           ( KnownNat n, KnownNat m
           , Object φ k n       a
           , Object φ k m (η    b)
           , Object φ k n    (γ a)
           , Object φ k m (η (γ b))
           , Object φ k m (γ (η b))
           , MonoidalEndo η φ k
           )
           ⇒   a -| k φ n m |-> η    b
           → γ a -| k φ n m |-> η (γ b)
  traverse = (sequence ⊙) ∘ fmap

  {- | Default:

  >>> consume f ≝ fmap f ⊙ traverse id
  -}
  consume ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
          ( KnownNat n, KnownNat m
          , Object φ k n (γ (η a))
          , Object φ k m (η    b)
          , Object φ k n    (γ a)
          , Object φ k m       b
          , MonoidalEndo η φ k
          )
          ⇒ γ    a  -| k φ n m |->   b
          → γ (η a) -| k φ n m |-> η b

  default consume ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
          ( KnownNat n, KnownNat m
          , Object φ k n (γ (η a))
          , Object φ k m (η    b)
          , Object φ k n    (γ a)
          , Object φ k m       b
          , Object φ k n    (η a)
          , Object φ k n (η (γ a))
          , MonoidalEndo η φ k
          )
          ⇒ γ    a  -| k φ n m |->   b
          → γ (η a) -| k φ n m |-> η b
  consume f = fmap f ⊙ traverse id


-- TODO follow up on the note at the top of https://hackage.haskell.org/package/distributive-0.6.2.1/docs/Data-Distributive.html
{- | This is currently a direct translation of 'Distributive' from @distributive@;
per the note at the top of the
[@Distributive@ module](https://hackage.haskell.org/package/distributive-0.6.2.1/docs/Data-Distributive.html#t:Distributive)
that typeclass (at least its superclass requirement) is premised on the
(Cartesian ± closed) setting of `(->)`, in particular on `(->)` having a
comonoid (the same one) available for every object (at least outside of the
linear types extension):

  - In `(->)`, we can always freely duplicate a value of any (inhabited) type: @dup x = (x,x)@.
  - In `(->)`, we can always freely destroy a value of any (inhabited) type: @zap _ = ()@.

In the setting of this package (cf. @Diagonal@, @Semicartesian@), neither of
these things is true for arbitrary categories, it's not clear what exactly the
space of possible "@Coapplicative@s" is or more to the point what use cases
there are for monoidal category EDSLs that aren't necessarily either Cartesian
or closed where (co)products are finitary containers, etc.

All of which is to say, this typeclass should at least intended to be useful for
working with @Representable@ functors in @(->)@ and categories that can hold or
(e.g. profunctorily) absorb terms from  @(->)@. -}
class (Functor γ φ φ k k)
  ⇒ DistributiveEndo (γ ∷ κ → κ) (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where

  {- | Default:

  >>> distribute = collect id
  -}
  distribute ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (a ∷ κ).
           ( KnownNat n
           , Object φ k n (η (γ a))
           , Object φ k n (γ (η a))
           , Functor η φ φ k k
           )
           ⇒ η (γ a) -| k φ n n |-> γ (η a)

  default distribute ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (a ∷ κ).
           ( KnownNat n
           , Object φ k n (η (γ a))
           , Object φ k n (γ (η a))
           , Object φ k n (γ    a)
           , Functor η φ φ k k
           )
           ⇒ η (γ a) -| k φ n n |-> γ (η a)
  distribute = collect id

  {- | Default:

  >>> collect f = distribute ⊙ fmap f
  -}
  collect ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
           ( KnownNat n, KnownNat m
           , Object φ k n       a
           , Object φ k m (γ    b)
           , Object φ k n    (η a)
           , Object φ k n    (η a)
           , Object φ k m (γ (η b))
           , Functor η φ φ k k
           )
           ⇒   a -| k φ n m |->    γ b
           → η a -| k φ n m |-> γ (η b)

  default collect ∷ ∀ (η ∷ κ → κ) (n ∷ Nat) (m ∷ Nat) (a ∷ κ) (b ∷ κ).
           ( KnownNat n, KnownNat m
           , Object φ k n       a
           , Object φ k m (γ    b)
           , Object φ k n    (η a)
           , Object φ k m (η (γ b))
           , Object φ k n    (η a)
           , Object φ k m (γ (η b))
           , Functor η φ φ k k
           )
           ⇒   a -| k φ n m |->    γ b
           → η a -| k φ n m |-> γ (η b)
  collect = (distribute ⊙) ∘ fmap

  -- TODO consider: what's the parallel to consume?
