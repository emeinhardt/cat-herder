{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) semiadditive category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Semiadditive
  ( module Cat.Sized.Semiadditive.Class
  , module Cat.Sized.Semiadditive.Instances
  ) where

import Cat.Sized.Semiadditive.Class
import Cat.Sized.Semiadditive.Instances ()
