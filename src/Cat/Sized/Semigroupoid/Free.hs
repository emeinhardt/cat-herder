{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}

{- | This module exports the namespaces for both
"Cat.Sized.Semigroupoid.Free.Data" and
"Cat.Sized.Semigroupoid.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}


module Cat.Sized.Semigroupoid.Free
  ( module Cat.Sized.Semigroupoid.Free.Data
  , module Cat.Sized.Semigroupoid.Free.Instances
  ) where

import Cat.Sized.Semigroupoid.Free.Data
import Cat.Sized.Semigroupoid.Free.Instances ()
