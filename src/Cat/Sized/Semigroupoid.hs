{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
{- | This module exports the (sized) semigroupoid class and instances; it does
not export anything related to free semigroupoids. -}

module Cat.Sized.Semigroupoid
 ( module Cat.Sized.Semigroupoid.Class
 , module Cat.Sized.Semigroupoid.Instances
 ) where

import Cat.Sized.Semigroupoid.Class
import Cat.Sized.Semigroupoid.Instances
