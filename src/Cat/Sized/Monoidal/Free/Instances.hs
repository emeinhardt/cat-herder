{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Monoidal.Free.Instances
  (
  ) where

import Prelude hiding
  ( (.)
  , id
  )
import Prelude.Unicode
  ( (∘)
  )

import Data.Kind    (Type)
import GHC.TypeNats (Nat)


import Cat.Sized.Functor
  ( Fix (In)
  )

import Cat.Sized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  )
import Cat.Sized.Category.Class
  ( Category ( id
             )
  )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , (***)
             , mul
             , ith
             , ith'
             , sing
             , unsing
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
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( ObjectOf
  )
import Cat.Sized.Monoidal.Free.Data
 ( HasProxy ( ProxyOf )
 , Mon ( Id
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
       )
 , MonF ( IdF
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
        )
 , Mon'
 )


instance Semigroupoid (φ ∷ Nat → κ → κ) (Mon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Object φ (Mon k) n a = ObjectOf φ k n a
  (.) = Of

instance Category (φ ∷ Nat → κ → κ) (Mon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  id = Id

instance Monoidal (φ ∷ Nat → κ → κ) (Mon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Proxy φ (Mon k) = ProxyOf φ k
  (***)   = Par
  mul     = Mul
  ith     = Ith
  ith'    = Ith'
  join    = Join
  split   = Split
  assoc   = Assoc
  unsing  = Unsing
  sing    = Sing
  lift1   = Lift1
  bising  = Bising
  bisplit = Bisplit
  bijoin  = Bijoin
  biassoc = Biassoc

instance Semigroupoid φ (MonF k (Mon' k)) where
  type Object φ (MonF k (Mon' k)) n a = ObjectOf φ k n a
  g . f = In g `OfF` In f

instance Category φ (MonF k (Mon' k)) where
  id = IdF

instance Monoidal φ (MonF k (Mon' k)) where
  type Proxy φ (MonF k (Mon' k)) = ProxyOf φ k
  f *** g = In f `ParF` In g
  mul pn pm pn' pm' f g = MulF pn pm pn' pm' (In f) (In g)
  ith     i f = IthF i (In f)
  ith' pn i f = IthF' pn i (In f)
  join    = JoinF
  split   = SplitF
  assoc   = AssocF
  unsing  = UnsingF
  sing    = SingF
  lift1   = Lift1F ∘ In
  bising  = BisingF ∘ In
  bisplit = BisplitF ∘ In
  bijoin  = BijoinF ∘ In
  biassoc = BiassocF ∘ In
