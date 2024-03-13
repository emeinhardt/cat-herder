{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the namespaces for both
"Cat.Sized.Monoidal.Free.Data" and
"Cat.Sized.Monoidal.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Sized.Monoidal.Free
  ( module Cat.Sized.Monoidal.Free.Data
  , module Cat.Sized.Monoidal.Free.Instances
  ) where

import Cat.Sized.Monoidal.Free.Data
import Cat.Sized.Monoidal.Free.Instances ()
