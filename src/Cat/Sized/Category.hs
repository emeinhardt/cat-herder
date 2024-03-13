{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) category class and instances; it does not
export anything related to free categories. -}

module Cat.Sized.Category
  ( module Cat.Sized.Category.Class
  , module Cat.Sized.Category.Instances
  ) where

import Cat.Sized.Category.Class
import Cat.Sized.Category.Instances ()
