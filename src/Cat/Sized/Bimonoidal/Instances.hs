{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Sized.Bimonoidal.Instances
  (
  ) where

import Cat.Sized.Bimonoidal.Class ( Bimonoidal )

import Cat.Sized.Monoidal.Instances ()
import Cat.Sized.Profunctor
  ( SizedPro
  )

import Data.Vector.Sized qualified as VS
import Cat.Orthotope
  ( R1 )

instance Bimonoidal VS.Vector VS.Vector (SizedPro (->))
instance Bimonoidal R1        R1        (SizedPro (->))
