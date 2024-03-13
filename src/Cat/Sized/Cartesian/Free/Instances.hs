{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Cartesian.Free.Instances
  (
  ) where

import Prelude hiding
  ( zip
  , zipWith
  )
import Prelude.Unicode ((∘))

import Data.Kind    (Type)
import GHC.TypeNats (Nat)

import Cat.Sized.Functor.Monoidal qualified as MF

import Cat.Sized.Functor (Fix(In))

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
import Cat.Sized.Diagonal.Class
  ( Diagonal ( DupObject
             , (&&&)
             , dup
             , dup'
             , fork
             )
  )
import Cat.Sized.Semicartesian.Class
  ( Semicartesian ( ProjObject
                  , idx
                  )
  , Delete ( DelObject
           , del
           )
  , Select  ( SelectObject
            , sel
            )
  )
import Cat.Sized.Cartesian.Class
  ( Cartesian
  )

import Cat.Sized.Semigroupoid.Free.Data
  ( ObjectOf
  )
import Cat.Sized.Monoidal.Free.Data
  ( ProxyOf
  )
import Cat.Sized.Braided.Free.Data
  ( SwapObjectOf
  )
import Cat.Sized.Diagonal.Free
  ( DupObjectOf
  )
import Cat.Sized.Semicartesian.Free
  ( ProjObjectOf
  , DelObjectOf
  , SelectObjectOf
  )
import Cat.Sized.Cartesian.Free.Data
  ( Cart ( Id
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
  , CartF ( IdF
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
  -- , CartesianFunctor
  )



instance Semigroupoid (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Object φ (Cart k) n a = ObjectOf φ k n a
  (.) = Of


instance Category (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  id = Id


instance Monoidal (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Proxy φ (Cart k) = ProxyOf φ k
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


instance Braided (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type SwapObject φ (Cart k) n a = SwapObjectOf φ k n a
  swap = Swap


instance Diagonal (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type DupObject φ (Cart k) n m a b = DupObjectOf φ k n m a b
  dup = Dup
  dup' = Dup'
  (&&&) = Fork
  fork = Fork'


instance Semicartesian (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type ProjObject φ (Cart k) n a = ProjObjectOf φ k n a
  idx = Idx


instance Delete (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type DelObject φ (Cart k) n a = DelObjectOf φ k n a
  del = Del


instance Select (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type SelectObject φ (Cart k) l n a = SelectObjectOf φ k l n a
  sel = Sel

instance Cartesian φ (Cart k)

instance MF.Zip φ (Cart k) where
  zip = Zip
  zipWith = ZipWith



instance Semigroupoid φ (CartF k (Cart' k)) where
  type Object φ (CartF k (Cart' k)) n a = ObjectOf φ k n a
  g . f = In g `OfF` In f

instance Category φ (CartF k (Cart' k)) where
  id = IdF

instance Monoidal φ (CartF k (Cart' k)) where
  type Proxy φ (CartF k (Cart' k)) = ProxyOf φ k
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

instance Braided (φ ∷ Nat → κ → κ) (CartF k (Cart' k)) where
  type SwapObject φ (CartF k (Cart' k)) n a = SwapObjectOf φ k n a
  swap = SwapF

instance Diagonal (φ ∷ Nat → κ → κ) (CartF k (Cart' k)) where
  type DupObject φ (CartF k (Cart' k)) n m a b = DupObjectOf φ k n m a b
  dup = DupF
  dup' = DupF'
  f &&& g = In f `ForkF` In g
  fork l n m f g = ForkF' l n m (In f) (In g)


instance Semicartesian (φ ∷ Nat → κ → κ) (CartF k (Cart' k)) where
  type ProjObject φ (CartF k (Cart' k)) n a = ProjObjectOf φ k n a
  idx = IdxF


instance Delete (φ ∷ Nat → κ → κ) (CartF k (Cart' k)) where
  type DelObject φ (CartF k (Cart' k)) n a = DelObjectOf φ k n a
  del = DelF


instance Select (φ ∷ Nat → κ → κ) (CartF k (Cart' k)) where
  type SelectObject φ (CartF k (Cart' k)) l n a = SelectObjectOf φ k l n a
  sel = SelF

instance Cartesian φ (CartF k (Cart' k))

instance MF.Zip φ (CartF k (Cart' k)) where
  zip = ZipF
  zipWith f = ZipWithF (In f)
