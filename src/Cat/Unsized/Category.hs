{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (unsized) category class and instances; it does not
export anything related to free categories. -}

module Cat.Unsized.Category
  ( module Cat.Unsized.Category.Class
  , module Cat.Unsized.Category.Instances
  ) where

import Cat.Unsized.Category.Class
import Cat.Unsized.Category.Instances ()
