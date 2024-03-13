{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) codiagonal monoidal category class and
instances; it does not export anything related to free categories. -}

module Cat.Sized.Codiagonal
  ( module Cat.Sized.Codiagonal.Class
  , module Cat.Sized.Codiagonal.Instances
  ) where

import Cat.Sized.Codiagonal.Class
import Cat.Sized.Codiagonal.Instances ()
