{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) semicocartesian monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Semicocartesian
  ( module Cat.Sized.Semicocartesian.Class
  , module Cat.Sized.Semicocartesian.Instances
  ) where

import Cat.Sized.Semicocartesian.Class
import Cat.Sized.Semicocartesian.Instances ()
