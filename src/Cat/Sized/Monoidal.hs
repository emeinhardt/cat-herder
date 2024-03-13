{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) monoidal category class and instances; it does not
export anything related to free categories. -}

module Cat.Sized.Monoidal
  ( module Cat.Sized.Monoidal.Class
  , module Cat.Sized.Monoidal.Instances
  ) where

import Cat.Sized.Monoidal.Class
import Cat.Sized.Monoidal.Instances ()
