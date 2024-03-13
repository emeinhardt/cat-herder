{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (unsized) semigroupoid class and instances; it does
not export anything related to free semigroupoids. -}

module Cat.Unsized.Semigroupoid
 ( module Cat.Unsized.Semigroupoid.Class
 , module Cat.Unsized.Semigroupoid.Instances
 ) where

import Cat.Unsized.Semigroupoid.Class
import Cat.Unsized.Semigroupoid.Instances ()
