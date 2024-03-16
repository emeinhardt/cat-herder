{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Distributive.Class
  ( DistributiveLR ( distlr
                   , undistlr
                   )
  ) where

{- TODO
1. Fix latex in class doc

2. Write instances to test constraints + gather more data about profunctors

-}

import Data.Kind (Type)
import GHC.TypeNats
  ( -- KnownNat
    Nat
  )
import Data.Finite (Finite)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Profunctor
  ( Profunctor
  )
-- import Cat.Sized.Semigroupoid.Class (Object)
import Cat.Sized.Monoidal.Class (Monoidal)
import Cat.Sized.Braided.Class (Braided)



-- TODO fix latex
{- | In a setting with binary products and coproducts, the familiar form of a
law for distributivity of products over sums is /a⋅(b+c) = a⋅b + a⋅c/.

When binary products and sums

 - are generalized to operations with /≥ 2/ inputs ("/n/-semigroups", etc.)...
 - and the sum operation is commutative...

...then the analogous form of the distributive law for an /(n,m)-semiring/ is
that, for an /n/-ary product with a term /a_i/ that is an /m-/ary sum:

/a_1 ⋅ a_2 ⋅ ... ⋅ a_i ⋅ ... ⋅ a_n/

where /a_i = b_1 + b_2 + ... + b_m/

is equivalent to distributing both /(a_1 ⋅ ... ⋅ a_{i-1})/ and
/(a_{i+1} ⋅ ... ⋅ a_n)/ inwards into each of the /m/ terms of the sum:

/\sigma_{j \in 1...m} a_1 ⋅ ... ⋅ a_{i-1} ⋅ b_j ⋅ a_{i+1} ⋅ ... ⋅ a_n/

This generalizes such a distributive law to categories with finite monoidal
products, finite symmetric monoidal coproducts, and where all morphisms map
homogeneous /n/-ary (co)products to /m/-ary (co)products.

In this context, 'distlr' maps a product-of-sums to a sum-of-products by
distributing a circumfix of product terms into one term in the product;
'undistlr' is the inverse:

>>> undistlr i . distlr i ≡ id

should always hold.
-}
class ( Braided  γ (k γ)
      , Monoidal φ (k φ)
      , Profunctor φ (k φ) γ (k γ) k
      , Profunctor γ (k γ) φ (k φ) k
      )
 ⇒ DistributiveLR
    (φ ∷  Nat → κ → κ)
    (γ ∷  Nat → κ → κ)
    (k ∷ (Nat → κ → κ) → (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  where

  distlr ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
         ( -- KnownNat n, KnownNat m
         -- , Object φ γ k n
         -- , Object γ k m a
         -- , Object γ k m (φ n a)
         -- , Object φ k n (γ m a)
         -- , Object γ k m a
         -- , Object γ k m (φ n a)
         )
         ⇒ Finite n                   -- ^ The distinguished index of a particular /m/-coproduct in the /n/-product of /m/-coproducts.
         → γ m a -| k φ γ n m |-> φ n a
         -- ⇒ γ m a -| k φ γ n m |-> a      -- ^ A projection function that picks out an /m/-coproduct term from the /n/ terms of a product-of-coproducts.
         -- → γ m a -| k φ γ n m |-> φ n a  -- ^ A function that distributes the /n-1/ product terms into each of the /m/ coproduct terms.
         -- ⇒ γ m a -| k φ n 1 |-> γ m a        -- ^ A projection function that picks out an /m/-coproduct term from the /n/ terms of a product-of-coproducts.
         -- → γ m a -| k φ n 1 |-> γ m (φ n a)  -- ^ A function that distributes the /n-1/ product terms into each of the /m/ coproduct terms.
         -- ⇒ φ n a `k` γ m a        -- ^ A projection function that picks out an /m/-coproduct term from the /n/ terms of a product.
         -- → φ n a `k` γ m (φ n a)  -- ^ A function that distributes the /n-1/ product terms into each of the /m/ coproduct terms.

  undistlr ∷ ∀ (n ∷ Nat) (m ∷ Nat) (a ∷ κ).
           ( -- KnownNat n, KnownNat m
           -- , Object k (φ n a)
           -- , Object k (γ m (φ n a))
           -- , Object φ k n a
           -- , Object γ k m (φ n a)
           )
           ⇒ Finite n                 -- ^ A distinguished index into each of the /m/ /n/-products.
           → φ n a -| k γ φ m n |-> γ m a
           -- ⇒ γ m (φ n a) `k` φ n a  -- ^ A function that undistributes the /n-1/ coproduct terms into each of the /m/ product terms.
