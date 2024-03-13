{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}

{- | This module exports the namespaces for both
"Cat.Sized.Category.Free.Data" and
"Cat.Sized.Category.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Sized.Category.Free
  ( module Cat.Sized.Category.Free.Data
  , module Cat.Sized.Category.Free.Instances
  ) where

import Cat.Sized.Category.Free.Data
import Cat.Sized.Category.Free.Instances ()
