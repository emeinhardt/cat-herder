{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}

{- | This module exports the namespaces for both
"Cat.Unsized.Category.Free.Data" and
"Cat.Unsized.Category.Free.Data.Instances".

These are separated by default to allow deviation from the expected workflow.
Until you know why you should do otherwise, you should simply import this module. -}

module Cat.Unsized.Category.Free
  ( module Cat.Unsized.Category.Free.Data
  , module Cat.Unsized.Category.Free.Instances
  ) where

import Cat.Unsized.Category.Free.Data
import Cat.Unsized.Category.Free.Instances ()
