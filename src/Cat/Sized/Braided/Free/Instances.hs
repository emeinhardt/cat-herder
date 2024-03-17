{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Braided.Free.Instances
  (
  ) where

import Prelude.Unicode ((∘))

import Data.Kind    (Type)
import GHC.TypeNats (Nat)


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
import Cat.Sized.Braided.Class
  ( Braided ( SwapObject
          , swap
          )
  ,
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( ObjectOf
  )
import Cat.Sized.Monoidal.Free.Data
  ( HasProxy ( ProxyOf )
  )
import Cat.Sized.Braided.Free.Data
  ( HasSwap ( SwapObjectOf )
  , Swap ( Par
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
         , Id
         , Of
         )
  , SwapF ( IdF
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
          )
  , Swap'
  )
import Cat.Sized.Functor (Fix(In))



instance Semigroupoid (φ ∷ Nat → κ → κ) (Swap (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Object φ (Swap k) n a = ObjectOf φ k n a
  (.) = Of


instance Category (φ ∷ Nat → κ → κ) (Swap (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  id = Id


instance Monoidal (φ ∷ Nat → κ → κ) (Swap (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Proxy φ (Swap k) = ProxyOf φ k
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


instance Braided (φ ∷ Nat → κ → κ) (Swap (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type SwapObject φ (Swap k) n a = SwapObjectOf φ k n a
  swap = Swap


instance Semigroupoid φ (SwapF k (Swap' k)) where
  type Object φ (SwapF k (Swap' k)) n a = ObjectOf φ k n a
  g . f = In g `OfF` In f

instance Category φ (SwapF k (Swap' k)) where
  id = IdF

instance Monoidal φ (SwapF k (Swap' k)) where
  type Proxy φ (SwapF k (Swap' k)) = ProxyOf φ k
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


instance Braided (φ ∷ Nat → κ → κ) (SwapF k (Swap' k)) where
  type SwapObject φ (SwapF k (Swap' k)) n a = SwapObjectOf φ k n a
  swap = SwapF
