{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Unsized.Semigroupoid.Free.Instances
  (
  ) where

import Prelude hiding ((.))

import Data.Kind (Type)

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  )
import Cat.Unsized.Semigroupoid.Free.Data
  ( SG ( Of
       )
  , HasObject ( ObjectOf
              )
  )




instance Semigroupoid (SG (k ∷ κ → κ → Type)) where
  type Object (SG k) a = ObjectOf k a
  (.) = Of
