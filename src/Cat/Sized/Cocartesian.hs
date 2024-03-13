{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{- | This module exports the (sized) cocartesian monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Cocartesian
  ( module Cat.Sized.Cocartesian.Class
  , module Cat.Sized.Cocartesian.Instances
  ) where


import Cat.Sized.Cocartesian.Class
import Cat.Sized.Cocartesian.Instances ()
