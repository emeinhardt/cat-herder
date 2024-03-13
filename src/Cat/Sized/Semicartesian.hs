{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) semicartesian monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Semicartesian
  ( module Cat.Sized.Semicartesian.Class
  , module Cat.Sized.Semicartesian.Instances
  ) where

import Cat.Sized.Semicartesian.Class
import Cat.Sized.Semicartesian.Instances ()
