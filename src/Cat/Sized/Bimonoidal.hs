{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) bimonoidal category class and instances; it does not
export anything related to free categories. -}

module Cat.Sized.Bimonoidal
  ( module Cat.Sized.Bimonoidal.Class
  , module Cat.Sized.Bimonoidal.Instances
  ) where

import Cat.Sized.Bimonoidal.Class
import Cat.Sized.Bimonoidal.Instances ()
