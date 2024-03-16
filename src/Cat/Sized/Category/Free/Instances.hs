{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Category.Free.Instances
  (
  ) where

import Prelude hiding
  ( (.)
  , id
  )

import GHC.TypeNats (Nat)
import Data.Kind (Type)

import Cat.Sized.Functor
  ( Fix ( In
        )
  )

import Cat.Sized.Category.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Category ( id )
  )
import Cat.Sized.Category.Free.Data
  ( Cat ( Of
        , Id
       )
  , HasObject ( ObjectOf
              )
  , Cat'
  , CatF ( IdF
         , OfF
         )
  )


instance Semigroupoid (φ ∷ Nat → κ → κ) (Cat (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  type Object φ (Cat k) n a = ObjectOf φ k n a
  (.) = Of

instance Category (φ ∷ Nat → κ → κ) (Cat (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
  id = Id


instance Semigroupoid φ (CatF k (Cat' k)) where
  type Object φ (CatF k (Cat' k)) n a = ObjectOf φ k n a
  g . f = In g `OfF` In f

instance Category φ (CatF k (Cat' k)) where
  id = IdF
