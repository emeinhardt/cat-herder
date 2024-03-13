{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the typeclass for monoidal categories with a zero object,
plus instances. -}

module Cat.Sized.Zero
  ( module Cat.Sized.Zero.Class
  , module Cat.Sized.Zero.Instances
  ) where

import Cat.Sized.Zero.Class
import Cat.Sized.Zero.Instances ()
