{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}

{- | This module exports the namespaces for both
"Cat.Unsized.Semigroupoid.Free.Data" and
"Cat.Unsized.Semigroupoid.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Unsized.Semigroupoid.Free
  ( module Cat.Unsized.Semigroupoid.Free.Data
  , module Cat.Unsized.Semigroupoid.Free.Instances
  ) where


import Cat.Unsized.Semigroupoid.Free.Data
import Cat.Unsized.Semigroupoid.Free.Instances ()
