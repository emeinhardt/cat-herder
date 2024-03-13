{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the namespaces for both
"Cat.Sized.Braided.Free.Data" and
"Cat.Sized.Braided.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Sized.Braided.Free
  ( module Cat.Sized.Braided.Free.Data
  , module Cat.Sized.Braided.Free.Instances
  ) where

import Cat.Sized.Braided.Free.Data
import Cat.Sized.Braided.Free.Instances ()
