{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the namespaces for both
"Cat.Sized.Cartesian.Free.Data" and
"Cat.Sized.Cartesian.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Sized.Cartesian.Free
  ( module Cat.Sized.Cartesian.Free.Data
  , module Cat.Sized.Cartesian.Free.Instances
  ) where

import Cat.Sized.Cartesian.Free.Data
import Cat.Sized.Cartesian.Free.Instances ()
