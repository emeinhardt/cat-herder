{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) diagonal monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Diagonal
  ( module Cat.Sized.Diagonal.Class
  , module Cat.Sized.Diagonal.Instances
  ) where

import Cat.Sized.Diagonal.Class
import Cat.Sized.Diagonal.Instances ()
