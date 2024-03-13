{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.Unsized.Category.Free.Instances
  (
  ) where

import Prelude hiding
  ( id
  , (.)
  )

import Cat.Unsized.Functor
  ( Fix ( In
        )
  )


import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  )
import Cat.Unsized.Category.Class
  ( Category  ( id
              )
  )
import Cat.Unsized.Semigroupoid.Free.Data
  ( HasObject(ObjectOf)
  )
import Cat.Unsized.Category.Free.Data
  ( Cat ( Id
        , Of
        )
  , Cat'
  , CatF ( IdF
         , OfF
         )
  )

import Cat.Unsized.Category.Instances ()



instance Semigroupoid (Cat k) where
  type Object (Cat k) a = ObjectOf k a
  (.) = Of

instance Category (Cat k) where
  id = Id


-- instance (Category t) ⇒ Semigroupoid (CatF k t) where
--   type Object (CatF k t) a = (ObjectOf k a, Object t a)

--   IdF . IdF = id `OfF` id
--   IdF . (g `OfF` f) = id `OfF` (g . f)
--   (g `OfF` f) . IdF = (g . f) `OfF` id
--   (i `OfF` h) . (g `OfF` f) = (i . h) `OfF` (g . f)
--   (EmbF m) . IdF = EmbF m
--   IdF . (EmbF m) = EmbF m
--   (EmbF m) . (g `OfF` f) = undefined `OfF` (g . f)
--   -- (EmbF m) . (EmbF n) = undefined

-- -- instance (Category t) ⇒ Category (CatF k t) where
-- --   id = IdF



instance Semigroupoid (CatF k (Cat' k)) where
  type Object (CatF k (Cat' k)) a = ObjectOf k a
  g . f = In g `OfF` In f

instance Category (CatF k (Cat' k)) where
  id = IdF

-- instance Semigroupoid (Cat' k) where
--   type Object (Cat' k) a = ObjectOf k a
--   g . f = In $ g `OfF` f

-- instance Category (Cat' k) where
--   id = In IdF
