{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- |

module Cat.Sized.Monoidal.Free.Data
  ( Mon ( Emb
        , Id
        , Of
        , Par
        , Mul
        , Ith
        , Ith'
        , Join
        , Split
        , Assoc
        , Sing
        , Unsing
        , Lift1
        , Bising
        , Bisplit
        , Bijoin
        , Biassoc
        )
  , HasProxy (ProxyOf)
  , foldMap

    -- * Recursion schemes
  , MonF ( EmbF
         , IdF
         , OfF
         , ParF
         , MulF
         , IthF
         , IthF'
         , JoinF
         , SplitF
         , AssocF
         , SingF
         , UnsingF
         , Lift1F
         , BisingF
         , BisplitF
         , BijoinF
         , BiassocF
         )
  , Mon'
  , foldMap'
  , mkAlg
  , fixed
  , fixedCoalg
  , fixed'
  , unfixed
  , unfixedAlg
  , unfixed'
  ) where

import Prelude hiding
  ( id
  , (.)
  , Functor
  , fmap
  , foldMap
  )
import Prelude.Unicode ((∘))

import Data.Kind (Type)

import GHC.TypeNats
  ( KnownNat
  , Nat
  , SNat
  , type (+)
  , type (*)
  )

import Data.Finite (Finite)

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Functor
  ( NT'
  , HFunctor ( hfmap
             , HFunctorObj
             )
  , Fix ( In
        , out
        )
  , cata
  , ana
  )

import Cat.Sized.Semigroupoid.Class
  ( Object
  , Object'
  , (⊙)
  )
import Cat.Sized.Category.Class
  ( id
  )

import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , (***)
             , mul
             , ith
             , ith'
             , join
             , split
             , assoc
             , sing
             , unsing
             , lift1
             , bising
             , bisplit
             , bijoin
             , biassoc
             )
  , (⊗)
  -- , ProdK
  )

import Cat.Sized.Semigroupoid.Free.Data
   ( HasObject ( ObjectOf
               )
   )



class HasProxy (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
  type ProxyOf (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) ∷ Nat → Type
  type ProxyOf φ k = SNat



data Mon (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (φ ∷ Nat → κ → κ)
         (n ∷ Nat) (m ∷ Nat)
         (a ∷ κ)   (b ∷ κ)   where

  Emb ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat)
            (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a
      , ObjectOf φ k m b
      )
      ⇒ a -|     k φ n m |-> b  -- ^ A /k/-morphism to lift into a monoidal category.
      → a -| Mon k φ n m |-> b

  Id ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat)
           (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a
     )
     ⇒ a -| Mon k φ n n |-> a  -- ^ The lifted identity morphism for any given size /n/.

  Of ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
           (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
           (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a
     , ObjectOf φ k m b
     , ObjectOf φ k l x
     )
     ⇒ x -| Mon k φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -| Mon k φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| Mon k φ n m |-> b

  Par ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ a -| Mon k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Mon k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Mon k φ (n + n') (m + m') |-> b

  Mul ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n  ∷ Nat) (m  ∷ Nat)
            (n' ∷ Nat) (m' ∷ Nat)
            (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -| Mon k φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -| Mon k φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| Mon k φ (n + n') (m + m') |-> b

  Ith ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a
      , ObjectOf φ k n a
      )
      ⇒ Finite n                -- ^ The position to place the singleton-to-singleton morphism.
      → a -| Mon k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| Mon k φ n n |-> a

  Ith' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a
       , ObjectOf φ k n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                -- ^ The position to place the singleton-to-singleton morphism.
       → a -| Mon k φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| Mon k φ n n |-> a

  Join ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| Mon k φ n (n * m) |-> a
       ⇒ (φ m a) -| Mon k φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  Split ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a
        , ObjectOf φ k      n  (φ m a)
        )
        -- ⇒ a -| Mon k φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| Mon k φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  Assoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a)
        , ObjectOf φ k m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| Mon k φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| Mon k φ n m |-> (φ n a)  -- ^ A size-preserving morphism that swaps nesting.

  Sing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a
        , ObjectOf φ k 1 (φ n a)
        )
        ⇒ a -| Mon k φ n 1 |-> φ n a

  Unsing ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a)
        , ObjectOf φ k n      a
        )
        ⇒ φ n a -| Mon k φ 1 n |-> a

  Lift1 ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a
        , ObjectOf φ k m      b
        , ObjectOf φ k n (φ 1 a)
        , ObjectOf φ k m (φ 1 b)
        )
        ⇒     a -| Mon k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| Mon k φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  Bising ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a
         , ObjectOf φ k m      b
         , ObjectOf φ k 1 (φ n a)
         , ObjectOf φ k 1 (φ m b)
         )
         ⇒     a -| Mon k φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| Mon k φ 1 1 |-> φ m b

  Bisplit ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒     a -| Mon k φ (i * n) (j * m) |->     b  -- ^ A /k/ morphism whose products on either side can be factored.
    → φ i a -| Mon k φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  Bijoin ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (i ∷ Nat) (j ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    )
    ⇒ φ i a -| Mon k φ      n       m  |-> φ j b  -- ^ A /k/ morphism with nested products.
    →     a -| Mon k φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  Biassoc ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n  ∷ Nat) (m  ∷ Nat)
                (i  ∷ Nat) (j  ∷ Nat)
                (n' ∷ Nat) (m' ∷ Nat)
                (i' ∷ Nat) (j' ∷ Nat)
                (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a
    , ObjectOf φ k (j' * m')      b
    )
    ⇒ φ i  a -| Mon k φ n  m  |-> φ j  b  -- ^ A /k/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| Mon k φ n' m' |-> φ j' b

deriving instance ( p ~ ProxyOf φ k
                  , ∀ i. Show (p i)
                  , ∀ i j x y. Show (k φ i j x y)
                  ) ⇒ Show (Mon k φ n m a b)



foldMap ∷ ∀ κ
          (φ ∷  Nat → κ → κ)
          (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ).
        ( ObjectOf φ k n a, ObjectOf φ k m b
        , Object   φ t n a, Object   φ t m b
        , ∀ i x. ObjectOf φ k i x ⇒ Object' φ t i x
        , Monoidal φ (Mon k), Monoidal φ t
        )
        ⇒ (∀ i. (ProxyOf φ k) i → (Proxy φ t) i)
        → (∀ i j x y.
           ( ObjectOf φ k i x, ObjectOf φ k j y
           , Object   φ t i x, Object   φ t j y
           )
           ⇒ x -| k φ i j |-> y
           → x -| t φ i j |-> y
        )                           -- ^ A function maps primitive morphisms into the target category.
        → a -| (Mon k) φ n m |-> b  -- ^ A path in the free monoidal category over @k@.
        → a -|  t      φ n m |-> b  -- ^ The resulting morphism in @t@.
foldMap _ α (Emb f)     = α f
foldMap _ _  Id         = id
foldMap π α (g `Of` f)  = foldMap π α g  ⊙  foldMap π α f
foldMap π α (f `Par` g) = foldMap π α f  ⊗  foldMap π α g
foldMap π α (Mul pn pm pn' pm' f g) = mul (π pn) (π pm) (π pn') (π pm')
                                          (foldMap π α f) (foldMap π α g)
foldMap π α (i `Ith` f)   = i `ith` (foldMap π α f)
foldMap π α (Ith' pn i f) = ith' (π pn) i (foldMap π α f)
foldMap _ _ Join   = join
foldMap _ _ Split  = split
foldMap _ _ Assoc  = assoc
foldMap _ _ Sing   = sing
foldMap _ _ Unsing = unsing
foldMap π α (Lift1   f) = lift1   (foldMap π α f)
foldMap π α (Bising  f) = bising  (foldMap π α f)
foldMap π α (Bisplit f) = bisplit (foldMap π α f)
foldMap π α (Bijoin  f) = bijoin  (foldMap π α f)
foldMap π α (Biassoc f) = biassoc (foldMap π α f)

-- TODO Permit change of tensor product
-- foldMap' ∷ ∀ κ
--           (φ ∷  Nat → κ → κ)
--           (γ ∷  Nat → κ → κ)
--           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (n ∷ Nat) (m ∷ Nat)
--           (a ∷ κ)   (b ∷ κ).
--         ( ObjectOf φ k n a, ObjectOf φ k m b
--         , Object   γ t n a, Object   γ t m b
--         , ∀ i x. ObjectOf φ k i x ⇒ Object' γ t i x
--         , Monoidal φ (Mon k), Monoidal γ t
--         , ∀ i. NatTrans (φ i) (γ i) φ γ k t
--         , ∀ i. NatTrans (γ i) (φ i) φ γ k t
--         , ∀ i j x. ObjectOf φ k i (φ j x) ⇒ Object' γ t i (φ j x)
--         , ∀ i j x. ObjectOf γ t i (γ j x) ⇒ Object' φ k i (γ j x)
--         )
--         ⇒ (∀ x. (ProxyOf φ k) x → (Proxy γ t) x)
--         → (∀ i j x y.
--            ( ObjectOf φ k i x, ObjectOf φ k j y
--            , Object   γ t i x, Object   γ t j y
--            )
--            ⇒ x -| k φ i j |-> y
--            → x -| t γ i j |-> y
--           )
--         → a -| (Mon k) φ n m |-> b
--         → a -|  t      γ n m |-> b
-- foldMap' _ α (Emb f)     = α f
-- foldMap' _ _  Id         = id
-- foldMap' π α (g `Of` f)  = foldMap' π α g   ⊙   foldMap' π α f
-- foldMap' π α (f `Par` g) = foldMap' π α f   ⊗  foldMap' π α g
-- foldMap' π α (Mul pn pm pn' pm' f g) = mul (π pn) (π pm) (π pn') (π pm')
--                                           (foldMap' π α f) (foldMap' π α g)
-- foldMap' π α (i `Ith` f)   = i `ith` (foldMap' π α f)
-- foldMap' π α (Ith' pn i f) = ith' (π pn) i (foldMap' π α f)
-- -- foldMap' _ _ (Join                    ) =         -- LHS   ∷ φ m a -| k φ n (n * m) |-> a
-- -- foldMap' _ _ (Join @κ_ @φ_ @k_        ) =         -- LHS   ∷ φ m a -| k φ n (n * m) |-> a
-- -- foldMap' _ _ (Join @κ_ @φ_ @k_ @n_ @m_) =         -- LHS   ∷ φ m a -| k φ n (n * m) |-> a
-- foldMap' _ _ (Join @κ_ @φ_ @k_ @n_ @m_) =         -- LHS   ∷ φ m a -| k φ n (n * m) |-> a
--     (join  @κ_ @γ @t @n_ @m_)                        -- join  ∷ γ m a -| t γ n (n * m) |-> a
--   ⊙ (comp @κ_ @κ_ @(φ_ m_) @(γ m_) @φ_ @γ @k_ @t @n_)  -- comp ∷ φ m a -| t γ n  n      |-> γ m a
--   --   (join  @κ @γ @t @n @m)                        -- join  ∷ γ m a -| t γ n (n * m) |-> a
--   -- ⊙ (comp @κ @κ @(φ m ) @(γ m ) @φ @γ @k @t @n)  -- comp ∷ φ m a -| t γ n  n      |-> γ m a
-- -- foldMap' _ _ Group = (comp) ⊙ split
-- -- foldMap' _ _ Assoc = assoc



-- type family Foo (φ ∷ Nat → κ → κ) (a ∷ κ) ∷ κ where
--   Foo φ (φ n a) = (φ n (Foo φ a))
--   Foo φ      a  = a

-- isoFoo ∷ ∀ (φ ∷ Nat → Type → Type) (γ ∷ Nat → Type → Type) (a ∷ Type).
--          Foo φ a
--        → Foo γ a
-- isoFoo = undefined

-- foldMap' ∷ ∀ κ
--           (φ ∷  Nat → κ → κ)
--           (γ ∷  Nat → κ → κ)
--           (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
--           (n ∷ Nat) (m ∷ Nat)
--           (a ∷ κ)   (b ∷ κ)
--           ffa fga ffb fgb.
--         ( ffa ~ Foo φ a, fga ~ Foo γ a
--         , ffb ~ Foo φ b, fgb ~ Foo γ b
--         , ObjectOf φ k n ffa, ObjectOf φ k m ffb
--         , Object   γ t n fga, Object   γ t m fgb
--         , ∀ i x ffx fgx. (ObjectOf φ k i ffx, ffx ~ Foo φ x, fgx ~ Foo γ x) ⇒ Object' γ t i fgx
--         -- ( ObjectOf φ k n a, ObjectOf φ k m b
--         -- , Object   γ t n a, Object   γ t m b
--         -- , ∀ i x. ObjectOf φ k i x ⇒ Object' γ t i x
--         , Monoidal φ (Mon k), Monoidal γ t
--         -- , NatTrans (φ n) (γ n) φ γ k t
--         -- , NatTrans (φ m) (γ m) φ γ k t
--         )
--         ⇒ (∀ i. (ProxyOf φ k) i → (Proxy γ t) i)
--         → (∀ i j x y ffx ffy fgx fgy.
--            ( ffx ~ Foo φ x, ffy ~ Foo φ y, fgx ~ Foo γ x, fgy ~ Foo γ y
--            , ObjectOf φ k i ffx, ObjectOf φ k j ffy
--            , Object   γ t i fgx, Object   γ t j fgy
--            -- ( ObjectOf φ k i x, ObjectOf φ k j y
--            -- , Object   γ t i x, Object   γ t j y
--            )
--            ⇒ ffx -| k φ i j |-> ffy
--            → fgx -| t γ i j |-> fgy
--            -- ⇒ (Foo φ x) -| k φ i j |-> (Foo φ y)
--            -- → (Foo γ x) -| t γ i j |-> (Foo γ y)
--            -- ⇒ x -| k φ i j |-> y
--            -- → x -| t γ i j |-> y
--           )
--         → ffa -| (Mon k) φ n m |-> ffb
--         → fga -|  t      γ n m |-> fgb
--         -- → (Foo φ a) -| (Mon k) φ n m |-> (Foo φ b)
--         -- → (Foo γ a) -|  t      γ n m |-> (Foo γ b)
--         -- → a -| (Mon k) φ n m |-> b
--         -- → a -|  t      γ n m |-> b
-- foldMap' _ α (Emb f)     = α f
-- foldMap' _ _  Id         = id
-- foldMap' π α (g `Of` f)  = foldMap' π α g   ⊙   foldMap' π α f
-- foldMap' π α (f `Par` g) = foldMap' π α f   ⊗   foldMap' π α g
-- foldMap' π α (Mul pn pm pn' pm' f g) = mul (π pn) (π pm) (π pn') (π pm')
--                                           (foldMap' π α f) (foldMap' π α g)
-- foldMap' π α (i `Ith` f)   = i `ith` (foldMap' π α f)
-- foldMap' π α (Ith' pn i f) = ith' (π pn) i (foldMap' π α f)
-- foldMap' _ _ Join  = join @κ @γ @t
-- -- foldMap' _ _ Group = split @κ @γ @t
-- -- foldMap' _ _ assoc = assoc @κ @γ @t

{-
joinK = join @κ @φ @k @n @m @a ∷ φ m a -| k φ n (n * m) |-> a
joinT = join @κ @γ @t @n @m @a ∷ γ m a -| t γ n (n * m) |-> a
preJoinT ∷  φ m a  -| t γ n n |-> γ m a
joinT ⊙ preJoinT ∷ φ m a -| t γ n (n * m) |-> a
splitK = split @κ @φ @k @n @m @a ∷ a -| k φ (n * m) n |-> φ m a
splitT = split @κ @γ @t @n @m @a ∷ a -| t γ (n * m) n |-> γ m a
postGroupT ∷ γ m a -| t γ n n |-> φ m a
postGroupT ⊙ splitT ∷ a -| t γ (n * m) n |-> φ m a

generally speaking, you want (at least) an arrow
φ i a -| t γ n n |-> γ i a
+ probably also
γ i a -| t γ n n |-> φ i a

which you'd get if there were instances
Functor  (φ i)       (k φ n n) (t γ n n)    -- not Data.Functor, not Cat.Sized.Functor
Functor        (γ i) (k φ n n) (t γ n n)    -- not Data.Functor, not Cat.Sized.Functor
NatTrans (φ i) (γ i) (k φ n n) (t γ n n)    -- not Cat.Sized.Functor
Functor  (γ i)       (k φ n n) (t γ n n)    -- not Data.Functor, not Cat.Sized.Functor
Functor        (φ i) (k φ n n) (t γ n n)    -- not Data.Functor, not Cat.Sized.Functor
NatTrans (γ i) (φ i) (k φ n n) (t γ n n)    -- not Cat.Sized.Functor
via comp

((φ m a) -| t γ n m |-> (γ m a))
((γ i a) -| t γ n m |-> (φ i a))
((φ i a) -| t γ n m |-> (γ i a))
-}


{- | Pattern functor for 'Mon'. -}
data MonF (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
          (φ ∷ Nat → κ → κ)
          (n ∷ Nat) (m ∷ Nat)
          (a ∷ κ)   (b ∷ κ)   where

  EmbF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (m ∷ Nat)
             (a ∷ κ)   (b ∷ κ).
      ( KnownNat n, KnownNat m
      , ObjectOf φ k n a, ObjectOf φ k m b
      , Object   φ t n a, Object   φ t m b
      )
      ⇒ a -|      k   φ n m |-> b  -- ^ A /k/-morphism to lift into a monoidal category.
      → a -| MonF k t φ n m |-> b

  IdF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat)
            (a ∷ κ).
     ( KnownNat n
     , ObjectOf φ k n a, Object φ t n a
     )
     ⇒ a -| MonF k t φ n n |-> a  -- ^ The lifted identity morphism for any given size /n/.

  OfF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
            (n ∷ Nat) (m ∷ Nat) (l ∷ Nat)
            (a ∷ κ)   (b ∷ κ)   (x ∷ κ).
     ( KnownNat n, KnownNat m, KnownNat l
     , ObjectOf φ k n a, ObjectOf φ k m b, ObjectOf φ k l x
     , Object   φ t n a, Object   φ t m b, Object   φ t l x
     )
     ⇒ x -|        t φ l m |-> b  -- ^ A morphism from /φ l x/ to /φ m b/.
     → a -|        t φ n l |-> x  -- ^ A morphism from /φ n a/ to /φ l xx/.
     → a -| MonF k t φ n m |-> b

  ParF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ a -|        t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|        t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| MonF k t φ (n + n') (m + m') |-> b

  MulF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n  ∷ Nat) (m  ∷ Nat)
             (n' ∷ Nat) (m' ∷ Nat)
             (a  ∷ κ)   (b  ∷ κ).
      ( KnownNat  n , KnownNat m
      , KnownNat  n', KnownNat m'
      , ObjectOf φ k  n       a, ObjectOf φ k  m       b
      , ObjectOf φ k      n'  a, ObjectOf φ k      m'  b
      , ObjectOf φ k (n + n') a, ObjectOf φ k (m + m') b
      , Object   φ t  n       a, Object   φ t  m       b
      , Object   φ t      n'  a, Object   φ t      m'  b
      , Object   φ t (n + n') a, Object   φ t (m + m') b
      )
      ⇒ (ProxyOf φ k) n  → (ProxyOf φ k) m
      → (ProxyOf φ k) n' → (ProxyOf φ k) m'
      → a -|        t φ  n        m       |-> b  -- ^ A morphism from /φ n a/ to /φ m b/.
      → a -|        t φ      n'       m'  |-> b  -- ^ A morphism from /φ n' a/ to /φ m' b/.
      → a -| MonF k t φ (n + n') (m + m') |-> b

  IthF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
             (n ∷ Nat) (a ∷ κ).
      ( KnownNat n
      , ObjectOf φ k 1 a, ObjectOf φ k n a
      , Object   φ t 1 a, Object   φ t n a
      )
      ⇒ Finite n                   -- ^ The position to place the singleton-to-singleton morphism.
      → a -|        t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
      → a -| MonF k t φ n n |-> a

  IthF' ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
       ( KnownNat n
       , ObjectOf φ k 1 a, ObjectOf φ k n a
       , Object   φ t 1 a, Object   φ t n a
       )
       ⇒ (ProxyOf φ k) n
       → Finite n                   -- ^ The position to place the singleton-to-singleton morphism.
       → a -|        t φ 1 1 |-> a  -- ^ A morphism from /φ 1 a/ to /φ 1 a/.
       → a -| MonF k t φ n n |-> a

  JoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (m ∷ Nat)
              (a ∷ κ).
       ( KnownNat n, KnownNat m, KnownNat (n * m)
       , ObjectOf φ k  n      (φ m a)
       , ObjectOf φ k (m * n)      a
       , Object   φ t  n      (φ m a)
       , Object   φ t (m * n)      a
       )
       -- ⇒ (ProdK φ m) a -| MonF k t φ n (n * m) |-> a
       ⇒ (φ m a) -| MonF k t φ n (n * m) |-> a  -- ^ A size-preserving morphism that collapses a layer of nesting.

  SplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m, KnownNat (n * m)
        , ObjectOf φ k (m * n)      a
        , ObjectOf φ k      n  (φ m a)
        , Object   φ t (m * n)      a
        , Object   φ t      n  (φ m a)
        )
        -- ⇒ a -| MonF k t φ (n * m) n |-> (ProdK φ m) a
        ⇒ a -| MonF k t φ (n * m) n |-> (φ m a)  -- ^ A size-preserving morphism that introduces a layer of nesting.

  AssocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n (φ m a), ObjectOf φ k m (φ n a)
        , Object   φ t n (φ m a), Object   φ t m (φ n a)
        )
        -- ⇒ (ProdK φ m) a -| MonF k t φ n m |-> (ProdK φ n) a
        ⇒ (φ m a) -| MonF k t φ n m |-> (φ n a)  -- ^ A size-preserving morphism that swaps nesting.

  SingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
              (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k n      a
        , ObjectOf φ k 1 (φ n a)
        , Object   φ t n      a
        , Object   φ t 1 (φ n a)
        )
        ⇒ a -| MonF k t φ n 1 |-> φ n a

  UnsingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (a ∷ κ).
        ( KnownNat n
        , ObjectOf φ k 1 (φ n a)
        , ObjectOf φ k n      a
        , Object   φ t 1 (φ n a)
        , Object   φ t n      a
        )
        ⇒ φ n a -| MonF k t φ 1 n |-> a

  Lift1F ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
               (n ∷ Nat) (m ∷ Nat)
               (a ∷ κ)   (b ∷ κ).
        ( KnownNat n, KnownNat m
        , ObjectOf φ k n      a
        , ObjectOf φ k m      b
        , ObjectOf φ k n (φ 1 a)
        , ObjectOf φ k m (φ 1 b)
        , Object   φ t n      a
        , Object   φ t m      b
        , Object   φ t n (φ 1 a)
        , Object   φ t m (φ 1 b)
        )
        ⇒     a -|        t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
        → φ 1 a -| MonF k t φ n m |-> φ 1 b  -- ^ An equivalent morphism with one trivial layer of nesting.

  BisingF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
         ( KnownNat n, KnownNat m
         , ObjectOf φ k n      a
         , ObjectOf φ k m      b
         , ObjectOf φ k 1 (φ n a)
         , ObjectOf φ k 1 (φ m b)
         , Object   φ t n      a
         , Object   φ t m      b
         , Object   φ t 1 (φ n a)
         , Object   φ t 1 (φ m b)
         )
         ⇒     a -|        t φ n m |->     b  -- ^ A morphism that does not necessarily have any nested products.
         → φ n a -| MonF k t φ 1 1 |-> φ m b

  BisplitF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n ∷ Nat) (m ∷ Nat)
                 (i ∷ Nat) (j ∷ Nat)
                 (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    , Object   φ t (i * n)     a
    , Object   φ t (j * m)     b
    , Object   φ t      n (φ i a)
    , Object   φ t      m (φ j b)
    )
    ⇒     a -|        t φ (i * n) (j * m) |->     b  -- ^ A /t/ morphism whose products on either side can be factored.
    → φ i a -| MonF k t φ      n       m  |-> φ j b  -- ^ An equivalent morphism with one layer of nesting introduced ("undistributed").

  BijoinF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                (n ∷ Nat) (m ∷ Nat)
                (i ∷ Nat) (j ∷ Nat)
                (a ∷ κ)   (b ∷ κ).
    ( KnownNat n, KnownNat m, KnownNat i, KnownNat j
    , ObjectOf φ k (i * n)     a
    , ObjectOf φ k (j * m)     b
    , ObjectOf φ k      n (φ i a)
    , ObjectOf φ k      m (φ j b)
    , Object   φ t (i * n)     a
    , Object   φ t (j * m)     b
    , Object   φ t      n (φ i a)
    , Object   φ t      m (φ j b)
    )
    ⇒ φ i a -|        t φ      n       m  |-> φ j b  -- ^ A /k/ morphism with nested products.
    →     a -| MonF k t φ (i * n) (j * m) |->     b  -- ^ An equivalent morphism with one layer of nesting removed ("distributed").

  BiassocF ∷ ∀ κ (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
                 (n  ∷ Nat) (m  ∷ Nat)
                 (i  ∷ Nat) (j  ∷ Nat)
                 (n' ∷ Nat) (m' ∷ Nat)
                 (i' ∷ Nat) (j' ∷ Nat)
                 (a  ∷ κ)   (b  ∷ κ).
    ( KnownNat n , KnownNat m , KnownNat i , KnownNat j
    , KnownNat n', KnownNat m', KnownNat i', KnownNat j'
    , i * n ~ i' * n'
    , j * m ~ j' * m'
    , ObjectOf φ k       n  (φ i  a)
    , ObjectOf φ k       m  (φ j  b)
    , ObjectOf φ k       n' (φ i' a)
    , ObjectOf φ k       m' (φ j' b)
    , ObjectOf φ k (i' * n')      a
    , ObjectOf φ k (j' * m')      b
    , Object   φ t       n  (φ i  a)
    , Object   φ t       m  (φ j  b)
    , Object   φ t       n' (φ i' a)
    , Object   φ t       m' (φ j' b)
    , Object   φ t (i' * n')      a
    , Object   φ t (j' * m')      b
    )
    ⇒ φ i  a -|        t φ n  m  |-> φ j  b  -- ^ A /t/ morphism from /n/ groups of /i/ @a@s to /m/ groups of /j/ @b@s.
    → φ i' a -| MonF k t φ n' m' |-> φ j' b



deriving instance ( ∀ i j x y. Show (x -| k φ i j |-> y)
                  , ∀ i j x y. Show (x -| t φ i j |-> y)
                  -- , ∀ i p. (p ~ ProxyOf φ k) ⇒ Show (p i)
                  , ProxyOf φ k ~ SNat
                  )
  ⇒ Show (a -| MonF k t φ n m |-> b)

type Mon' k = Fix (MonF k)

instance HFunctor (MonF k) where
  hfmap _ (EmbF m)    = EmbF m
  hfmap _ IdF         = IdF
  hfmap α (g `OfF`  f) = α g `OfF`  α f
  hfmap α (f `ParF` g) = α f `ParF` α g
  hfmap α (MulF pn pm pn' pm' f g) = MulF pn pm pn' pm' (α f) (α g)
  hfmap α (IthF     i f) = IthF     i (α f)
  hfmap α (IthF' pn i f) = IthF' pn i (α f)
  hfmap _ JoinF   = JoinF
  hfmap _ SplitF  = SplitF
  hfmap _ AssocF  = AssocF
  hfmap _ SingF   = SingF
  hfmap _ UnsingF = UnsingF
  hfmap α (Lift1F   f) = Lift1F   (α f)
  hfmap α (BisingF  f) = BisingF  (α f)
  hfmap α (BisplitF f) = BisplitF (α f)
  hfmap α (BijoinF  f) = BijoinF  (α f)
  hfmap α (BiassocF f) = BiassocF (α f)


instance (Monoidal φ (η (Fix η))) ⇒ Monoidal φ (Fix η) where
  type Proxy φ (Fix η) = Proxy φ (η (Fix η))
  (In f) *** (In g) = In $ f *** g
  -- f *** g = (In f) *** (In g)
  mul pn pm pn' pm' (In f) (In g) = In $ mul pn pm pn' pm' f g
  ith     i (In f) = In $ ith i f
  ith' pn i (In f) = In $ ith' pn i f
  join    = In join
  split   = In split
  assoc   = In assoc
  unsing  = In unsing
  sing    = In sing
  lift1 = In ∘ lift1 ∘ out
  bising  = In ∘ bising ∘ out
  bisplit (In f) = In $ bisplit f
  bijoin (In f)  = In $ bijoin f
  biassoc (In f) = In $ biassoc f



-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Mon k@ morphism to a @Mon' k@ morphism. -}
fixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ      k  i x ⇒ Object' φ (Mon  k) i x
  , ∀ i x. Object   φ (Mon k) i x ⇒ Object' φ (Mon' k) i x
  )
  ⇒ a -| Mon  k φ n m |-> b
  → a -| Mon' k φ n m |-> b
fixed' Id          = In IdF
fixed' (Emb m)     = In (EmbF m)
fixed' (g `Of` f)  = In (fixed' g `OfF` fixed' f)
fixed' (f `Par` g) = In $ fixed' f `ParF` fixed' g
fixed' (Mul pn pm pn' pm' f g) = In $ MulF pn pm pn' pm' (fixed' f) (fixed' g)
fixed' (Ith     i f) = In $ IthF     i (fixed' f)
fixed' (Ith' pn i f) = In $ IthF' pn i (fixed' f)
fixed' Join   = In $ JoinF
fixed' Split  = In $ SplitF
fixed' Assoc  = In $ AssocF
fixed' Sing   = In $ SingF
fixed' Unsing = In $ UnsingF
fixed' (Lift1   f) = In $ Lift1F   (fixed' f)
fixed' (Bising  f) = In $ BisingF  (fixed' f)
fixed' (Bisplit f) = In $ BisplitF (fixed' f)
fixed' (Bijoin  f) = In $ BijoinF  (fixed' f)
fixed' (Biassoc f) = In $ BiassocF (fixed' f)


{- | Coalgebra for converting a @Mon k@ morphism to a @Mon' k@ morphism. -}
fixedCoalg ∷ ∀ φ k n m a b.
  ( ∀ j x. ObjectOf φ k j x ⇒ Object' φ (Mon k) j x)  -- Constraint can be satisfied wherever instances from Cat.Sized.Monoidal.Free.Instances are in scope.
  ⇒ a -|         (Mon k)  φ n m |-> b
  → a -| (MonF k (Mon k)) φ n m |-> b
fixedCoalg Id          = IdF
fixedCoalg (Emb m)     = EmbF m
fixedCoalg (g `Of`  f) = g `OfF` f
fixedCoalg (f `Par` g) = f `ParF` g
fixedCoalg (Mul pn pm pn' pm' f g) = MulF pn pm pn' pm' f g
fixedCoalg (Ith     i f) = IthF     i f
fixedCoalg (Ith' pn i f) = IthF' pn i f
fixedCoalg Join   = JoinF
fixedCoalg Split  = SplitF
fixedCoalg Assoc  = AssocF
fixedCoalg Sing   = SingF
fixedCoalg Unsing = UnsingF
fixedCoalg (Lift1   f) = Lift1F   f
fixedCoalg (Bising  f) = BisingF  f
fixedCoalg (Bisplit f) = BisplitF f
fixedCoalg (Bijoin  f) = BijoinF  f
fixedCoalg (Biassoc f) = BiassocF f


{- | Convert a @Mon k@ morphism to a @Mon' k@ morphism. -}
fixed ∷ ∀ k φ n m a b.
  ( -- ∀ i x. ObjectOf φ k i x ⇒ Object' φ (MonF k (Mon k)) i x  -- Only this Constraint is necessary wherever instances from Cat.Sized.Monoidal.Free.Instances are in scope.
    ∀ i x. ObjectOf φ      k  i x ⇒ Object' φ (Mon  k) i x
  , ∀ i x. Object   φ (Mon k) i x ⇒ Object' φ (Mon' k) i x
  , HFunctorObj (MonF k) φ (Mon k) (Mon' k)
  )
  ⇒ a -| Mon  k φ n m |-> b  -- ^ A @Mon k@ morphism.
  → a -| Mon' k φ n m |-> b  -- ^ A @Fix (MonF k)@ morphism.
fixed = ana fixedCoalg


-- Keep this around as long as the dust hasn't settled around recursion schemes
-- and coupling of object constraints between primitives and free objects:
-- unlike @fixed@ this is independent of the recursion schemes implementation.
{- | Convert a @Mon' k@ morphism to a @Mon k@ morphism. -}
unfixed' ∷ ∀ k φ n m a b.
  ( ObjectOf φ k n a, ObjectOf φ k m b
  , ∀ i x. ObjectOf φ      k  i x ⇒ Object' φ (Mon  k) i x
  , ∀ i x. Object   φ (Mon k) i x ⇒ Object' φ (Mon' k) i x
  )
  ⇒ a -| Mon' k φ n m |-> b
  → a -| Mon  k φ n m |-> b
unfixed' (In IdF)         = Id
unfixed' (In (EmbF m))    = Emb m
unfixed' (In (g `OfF`  f)) = unfixed' g `Of`  unfixed' f
unfixed' (In (f `ParF` g)) = unfixed' f `Par` unfixed' g
unfixed' (In (MulF pn pm pn' pm' f g)) = Mul pn pm pn' pm' (unfixed' f) (unfixed' g)
unfixed' (In (IthF     i f)) = Ith     i (unfixed' f)
unfixed' (In (IthF' pn i f)) = Ith' pn i (unfixed' f)
unfixed' (In (JoinF))   = Join
unfixed' (In (SplitF))  = Split
unfixed' (In (AssocF))  = Assoc
unfixed' (In (SingF))   = Sing
unfixed' (In (UnsingF)) = Unsing
unfixed' (In (Lift1F   f)) = Lift1   (unfixed' f)
unfixed' (In (BisingF  f)) = Bising  (unfixed' f)
unfixed' (In (BisplitF f)) = Bisplit (unfixed' f)
unfixed' (In (BijoinF  f)) = Bijoin  (unfixed' f)
unfixed' (In (BiassocF f)) = Biassoc (unfixed' f)


{- | Algebra for converting a @Mon' k@ morphism to a @Mon k@ morphism. -}
unfixedAlg ∷ ∀ k φ n m a b.
    a -| MonF k (Mon k) φ n m |-> b
  → a -|        (Mon k) φ n m |-> b
unfixedAlg IdF          = Id
unfixedAlg (EmbF m)     = Emb m
unfixedAlg (g `OfF`  f) = g `Of` f
unfixedAlg (f `ParF` g) = f `Par` g
unfixedAlg (MulF pn pm pn' pm' f g) = Mul pn pm pn' pm' f g
unfixedAlg (IthF     i f) = Ith     i f
unfixedAlg (IthF' pn i f) = Ith' pn i f
unfixedAlg JoinF   = Join
unfixedAlg SplitF  = Split
unfixedAlg AssocF  = Assoc
unfixedAlg SingF   = Sing
unfixedAlg UnsingF = Unsing
unfixedAlg (Lift1F   f) = Lift1   f
unfixedAlg (BisingF  f) = Bising  f
unfixedAlg (BisplitF f) = Bisplit f
unfixedAlg (BijoinF  f) = Bijoin  f
unfixedAlg (BiassocF f) = Biassoc f


{- | Convert a @Mon' k@ morphism to a @Mon k@ morphism. -}
unfixed ∷ ∀ k φ n m a b.
  (∀ i x. Object φ (Mon' k) i x ⇒ Object' φ (Mon k) i x)  -- Constraint can be satisfied wherever instances from Cat.Sized.Monoidal.Free.Instances are in scope.
  ⇒ a -| Mon' k φ n m |-> b  -- ^ A @Mon' k@ morphism.
  → a -| Mon  k φ n m |-> b  -- ^ An equivalent @Mon k@ morphism.
unfixed = cata unfixedAlg


-- TODO lift constraint that the Proxy be the same before and after/make an alternative version?
{- | Given a function that maps primitive morphisms to morphisms in a target
category /t/, this constructs an algebra from the free category type. -}
mkAlg ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type).
  ( Monoidal φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy   φ t
  -- ∀ x. ObjectOf k x ⇒ Object' t x
  )
  ⇒ (∀ n m a b.
     ( -- ∀ x. ObjectOf k x ⇒ Object' t x
       ObjectOf φ k n a
     , ObjectOf φ k m b
     , Object   φ t n a
     , Object   φ t m b
     )
     ⇒ a -| k φ n m |-> b
     → a -| t φ n m |-> b
     )
  → NT' φ (MonF k t) t
mkAlg _ (IdF @k_ @t_ @a) = id @κ @φ @t
mkAlg _ (g `OfF` f)      = g ⊙ f
mkAlg α (EmbF    f)      = α f
mkAlg _ (f `ParF` g) = f *** g
mkAlg _ (MulF pn pm pn' pm' f g) = mul pn pm pn' pm' f g
mkAlg _ (IthF     i f) = ith     i f
mkAlg _ (IthF' pn i f) = ith' pn i f
mkAlg _ JoinF   = join
mkAlg _ SplitF  = split
mkAlg _ AssocF  = assoc
mkAlg _ SingF   = sing
mkAlg _ UnsingF = unsing
mkAlg _ (Lift1F   f) = lift1   f
mkAlg _ (BisingF  f) = bising  f
mkAlg _ (BisplitF f) = bisplit f
mkAlg _ (BijoinF  f) = bijoin  f
mkAlg _ (BiassocF f) = biassoc f


{- | Alternative to 'foldMap' based on 'cata'. -}
foldMap' ∷ ∀ κ (φ ∷ Nat → κ → κ)
  (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (t ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)
  (n ∷ Nat) (m ∷ Nat)
  (a ∷ κ)   (b ∷ κ).
  ( Monoidal φ t
  , ProxyOf φ k ~ ProxyOf φ t, ProxyOf φ t ~ Proxy φ t
  -- , Object φ (Fix (MonF k)) n a
  -- , Object φ (Fix (MonF k)) m b
  , (∀ i x. Object φ (Fix (MonF k)) i x ⇒ Object' φ t i x)
  )
  ⇒ (∀ i j x y.
     ( ObjectOf φ k i x
     , ObjectOf φ k j y
     , Object   φ t i x
     , Object   φ t j y
     )
     ⇒ x -| k φ i j |-> y
     → x -| t φ i j |-> y
     )
  → (  a -| Fix (MonF k) φ n m |-> b
    →  a -|        t     φ n m |-> b
    )
foldMap' α = cata (mkAlg α)
