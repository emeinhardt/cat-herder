{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) Cartesian monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Cartesian
  ( module Cat.Sized.Cartesian.Class
  , module Cat.Sized.Cartesian.Instances
  ) where

import Cat.Sized.Cartesian.Class
import Cat.Sized.Cartesian.Instances ()
