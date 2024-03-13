{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) distributve monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Distributive
  ( module Cat.Sized.Distributive.Class
  , module Cat.Sized.Distributive.Instances
  ) where

import Cat.Sized.Distributive.Class
import Cat.Sized.Distributive.Instances ()
