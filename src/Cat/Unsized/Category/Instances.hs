{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Unsized.Category.Instances
  (
  ) where

import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  )



import Cat.Unsized.Semigroupoid.Instances ()
import Cat.Unsized.Category.Class
  ( Category ( id
             )
  )


instance Category (->) where
  id  = P.id
