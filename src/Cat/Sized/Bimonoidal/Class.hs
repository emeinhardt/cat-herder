{-# OPTIONS_HADDOCK show-extensions #-}
{- | The 'Bimonoidal' typeclass describes categories /k/ where

 - There are two (in general distinct) monoidal functor structures on /k/.
 - Composition and identities are available as one would expect.

There are *no* associated laws requiring commutativity, distributivity, or
special behavior of identities.

In contrast, my impression is that "bimonoidal" is (always?) a synonym for "rig"
("semiring") in the category theory literature.

I see that as an unfortunate artifact of the relative attention that "more
nicely behaved" algebraic objects like rings, fields, modules etc. get
(particularly in mathematics vs. in computer science) compared to the ones that
are more often available or relevant in a computational setting — cf. the
various meanings of "bimonoid" or "bisemigroup" and
"nearsemiring"/"seminearring".

For want of a better alternative and given that

 - "Rig category" is already in use.
 - "Rig category" is more transparent than "bimonoid" as a term for a rig-like
   category.
 - "Bimonoidal category" as used here overlaps with uses of "bimonoid" in some
   (non-categorical) literature.
 - A typeclass hierarchy motivates finer-grained distinctions.

"bimonoidal" seems a reasonably appropriate name for the typeclass described here.
-}

{- TODO instances for 'Sub'
-}

module Cat.Sized.Bimonoidal.Class
  ( Bimonoidal
  ) where

import Data.Kind (Type)
import GHC.TypeNats (Nat)

import Cat.Sized.Profunctor
  ( Profunctor
  , ProSG
  , ProCat
  )

import Cat.Sized.Monoidal.Class
  ( Monoidal ( -- Unit
             )
  )
-- import Cat.Sized.Semicartesian.Class
--   ( HasTerminal (terminal)
--   )
-- import Cat.Sized.Semicocartesian.Class
--   ( HasInitial (initial)
--   )

-- import Cat.Operators
--   ( type (-|)
--   , type (|->)
--   )


{- | "/k/ is bimonoidal" here means

 - There are two (in general distinct) monoidal functor structures on /k/.
 - Composition and identities are available as one would expect.

There are *no* associated laws requiring commutativity, distributivity, or
special behavior of identities.
-}
class ( Monoidal   φ (k φ)
      , Monoidal   γ (k γ)
      , Profunctor φ (k φ) γ (k γ) k
      , Profunctor γ (k γ) φ (k φ) k
      -- The four instances below are derivable from the constraints above.
      -- , ProSG      φ (k φ) φ (k φ) φ (k φ) k
      -- , ProSG      γ (k γ) γ (k γ) γ (k γ) k
      -- , ProSG      φ (k φ) φ (k φ) γ (k γ) k
      -- , ProSG      γ (k γ) φ (k φ) φ (k φ) k
      )
  ⇒ Bimonoidal
    (φ ∷  Nat → κ → κ)
    (γ ∷  Nat → κ → κ)
    (k ∷ (Nat → κ → κ) → (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
