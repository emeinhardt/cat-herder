{-# OPTIONS_HADDOCK show-extensions #-}
{- | This module exports class and instance namespaces for @Sized@ (pro)functors,
semigroupoids, and various types of categories, excluding anything related to
free semigroupoids or free categories. -}

-- TODO document the "import Prelude hiding ..." most likely to be useful with this

module Cat.Sized
  ( module Cat.Sized.Functor
  , module Cat.Sized.Profunctor
  , module Cat.Sized.Semigroupoid
  , module Cat.Sized.Category
  , module Cat.Sized.Monoidal
  , module Cat.Sized.Braided
  , module Cat.Sized.Diagonal
  , module Cat.Sized.Semicartesian
  , module Cat.Sized.Cartesian
  , module Cat.Sized.Codiagonal
  , module Cat.Sized.Semicocartesian
  , module Cat.Sized.Cocartesian
  , module Cat.Sized.Distributive
  , module Cat.Sized.Bimonoidal
  , module Cat.Sized.Semiadditive
  -- , module Cat.Sized.Bicartesian
  ) where

import Cat.Sized.Functor
import Cat.Sized.Profunctor hiding ((.))
import Cat.Sized.Semigroupoid
import Cat.Sized.Category
import Cat.Sized.Monoidal
import Cat.Sized.Braided
import Cat.Sized.Diagonal
import Cat.Sized.Semicartesian
import Cat.Sized.Cartesian
import Cat.Sized.Codiagonal
import Cat.Sized.Semicocartesian
import Cat.Sized.Cocartesian
import Cat.Sized.Distributive
import Cat.Sized.Bimonoidal
import Cat.Sized.Semiadditive
-- import Cat.Sized.Bicartesian
