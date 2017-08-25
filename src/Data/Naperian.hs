{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|
Module      : Data.Naperian
Description : Naperian and assorted typeclasses along with generic operations
Copyright   : © Nick Hu, 2017
                Austin Seipp, 2017
License     : BSD3
Maintainer  : Nick Hu <nick.hu@cs.ox.ac.uk>
Portability : unportable

This module contains the typeclasses which describe static-sized containers
algebraically.

Instances of Naperian ought to satisfy the law that:

@
  tabulate . lookup = id = lookup . tabulate
@

Some generic operations for working with Naperian types are also provided.
-}

module Data.Naperian where

import           Control.Applicative (liftA2)
import           Data.Foldable       (toList)
import           Data.Kind           (Constraint, Type)
import           GHC.TypeLits        (ErrorMessage (..), TypeError)
import           Prelude             hiding (lookup)

-- | \"'Applicative' zipping\". Synonym for @liftA2@.
azipWith :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
{-# INLINE azipWith #-}
azipWith = liftA2

-- | Synonym for @pure@.
areplicate :: Applicative f => a -> f a
{-# INLINE areplicate #-}
areplicate = pure

-- | Naperian functors.
-- A useful way of thinking about a Naperian functor is that if we have a value
-- of type @v :: f a@ for some @'Naperian' f@, then we can think of @f a@ as a
-- bag of objects, with the ability to pick out the @a@ values inside the bag,
-- for each and every @a@ inside @f@. For example, in order to look up a value
-- @a@ inside a list @[a]@, we could use a function @[a] -> Int -> a@, which is
-- exactly @'(Prelude.!!)'@
--
-- The lookup function acts like a logarithm of the @'Functor' f@. Intuitively,
-- a Haskell function @f :: a -> b@ acts like the exponential @b^a@ if we intuit
-- types as an algebraic quantity. The logarithm of some value @x = b^a@ is
-- defined as @log_b(x) = a@, so given @x@ and a base @b@, it finds the exponent
-- @a@. In Haskell terms, this would be like finding the input value @a@ to a
-- function @f :: a -> b@, given a @b@, so it is a reverse mapping from the
-- outputs of @f@ back to its inputs.
--
-- A @'Naperian'@ functor @f@ is precisely a functor @f@ such that for any value
-- of type @f a@, we have a way of finding every single @a@ inside.
class Functor f => Naperian f where
  {-# MINIMAL lookup, (tabulate | positions) #-}

  -- | The \"logarithm\" of @f@. This type represents the 'input' you use to
  -- look up values inside @f a@. For example, if you have a list @[a]@, and
  -- you want to look up a value, then you use an @'Int'@ to index into
  -- the list. In this case, @'Log' [a] = Int@. If you have a type-bounded
  -- Vector @'Vector' (n :: 'Nat') a@, then @'Log' ('Vector' n)@ is the
  -- range of integers @[0..n-1]@ (represented here as @'Finite' n@.)
  type Log f

  -- | Look up an element @a@ inside @f a@. If you read this function type in
  -- English, it says \"if you give me an @f a@, then I will give you a
  -- function, so you can look up the elements of @f a@ and get back an @a@\"
  lookup :: f a -> Log f -> a

  -- | Tabulate a @'Naperian'@. This creates @f a@ values by mapping the
  -- logarithm of @f@ onto every \"position\" inside @f a@
  tabulate :: (Log f -> a) -> f a

  -- | Find every position in the \"space\" of the @'Naperian' f@.
  positions :: f (Log f)
  tabulate h = h <$> positions
  positions = tabulate id

-- | The transposition of two @'Naperian'@ functors @f@ and @g@.
transpose :: (Naperian f, Naperian g) => f (g a) -> g (f a)
transpose = tabulate . fmap tabulate . flip . fmap lookup . lookup

class (Applicative f, Naperian f, Traversable f) => Dimension f where
  size :: f a -> Int
  size = length . toList

dotp :: (Num a, Dimension f) => f a -> f a -> a
dotp xs ys = sum (azipWith (*) xs ys)

matrixp :: (Num a, Dimension f, Dimension g, Dimension h)
        => f (g a) -> g (h a) -> f (h a)
matrixp xss yss =
  azipWith (azipWith dotp) (areplicate <$> xss) (areplicate (transpose yss))

-- | Arbitrary-rank hypercuboids, parameterised over their dimension.
data Hyper :: [Type -> Type] -> Type -> Type where
  Scalar :: a -> Hyper '[] a
  Prism :: (Dimension f, Shapely fs) => Hyper fs (f a) -> Hyper (f ': fs) a

point :: Hyper '[] a -> a
point (Scalar a) = a

crystal :: Hyper (f : fs) a -> Hyper fs (f a)
crystal (Prism x) = x

instance Show a => Show (Hyper fs a) where
  show (Scalar x) = show x
  show (Prism x)  = show $ toList <$> x

instance Eq a => Eq (Hyper '[] a) where
  Scalar x == Scalar y = x == y

instance (Eq a, Eq (Hyper fs (f a))) => Eq (Hyper (f ': fs) a) where
  Prism x == Prism y = x == y

instance Functor (Hyper fs) where
  fmap f (Scalar x) = Scalar (f x)
  fmap f (Prism x)  = Prism ((fmap . fmap) f x)

instance Shapely fs => Applicative (Hyper fs) where
  pure = hreplicate
  (<*>) = hzipWith ($)

instance Foldable (Hyper fs) where
  foldr f e (Scalar x) = f x e
  foldr f e (Prism x)  = foldr (flip (foldr f)) e x

instance Traversable (Hyper fs) where
  traverse f (Scalar x) = Scalar <$> f x
  traverse f (Prism x)  = Prism <$> traverse (traverse f) x

class Shapely fs where
  hreplicate :: a -> Hyper fs a
  hsize      :: Hyper fs a -> Int

instance Shapely '[] where
  hreplicate = Scalar
  hsize      = const 1

instance (Dimension f, Shapely fs) => Shapely (f ': fs) where
  hreplicate x    = Prism (hreplicate (areplicate x))
  hsize (Prism x) = size (first x) * hsize x

first :: (Shapely fs) => Hyper fs a -> a
first (Scalar x) = x
first (Prism x)  = head . toList $ first x

hzipWith :: (a -> b -> c) -> Hyper fs a -> Hyper fs b -> Hyper fs c
hzipWith f (Scalar x) (Scalar y) = Scalar (f x y)
hzipWith f (Prism x)  (Prism y)  = Prism (hzipWith (azipWith f) x y)

-- | Fold over a single dimension of a hypercuboid.
reduceBy :: (a -> a -> a) -> a -> Hyper (f ': fs) a -> Hyper fs a
reduceBy f e (Prism x) = foldr f e <$> x

-- | Generalized transposition over arbitrary-rank hypercuboids.
transposeHyper :: Hyper (f ': g ': fs) a -> Hyper (g ': f ': fs) a
transposeHyper (Prism (Prism x)) = Prism (Prism (transpose <$> x))

-- | Lift an unary function from values to hypercuboids of values.
unary :: Shapely fs => (a -> b) -> (Hyper fs a -> Hyper fs b)
{-# INLINE unary #-}
unary = fmap

class (Shapely fs, Shapely gs) => Alignable fs gs where
  align :: Hyper fs a -> Hyper gs a

instance Alignable '[] '[] where
  align = id

instance (Dimension f, Alignable fs gs) => Alignable (f ': fs) (f ': gs) where
  align (Prism x) = Prism (align x)

instance (Dimension f, Shapely fs) => Alignable '[] (f ': fs) where
  align (Scalar x) = hreplicate x

type family Max (fs :: [Type -> Type]) (gs :: [Type -> Type]) :: [Type -> Type] where
  Max '[]       '[]       = '[]
  Max '[]       gs        = gs
  Max fs        '[]       = fs
  Max (f ': fs) (f ': gs) = f ': Max fs gs

type family Compatible (fs :: [Type -> Type]) (gs :: [Type -> Type]) :: Constraint where
  Compatible '[]       '[]       = ()
  Compatible '[]       _         = ()
  Compatible _         '[]       = ()
  Compatible (f ': fs) (f ': gs) = Compatible fs gs
  Compatible a b                 = TypeError (
         'Text "Mismatched dimensions!"
   ':$$: 'Text "The dimension " ':<>: 'ShowType a
   ':<>: 'Text " can't be aligned with"
   ':$$: 'Text "the dimension " ':<>: 'ShowType b)

up :: (Shapely fs, Dimension f) => Hyper fs a -> Hyper (f : fs) a
up = Prism . fmap pure
-- | Generalized, rank-polymorphic inner product.
innerpHyper :: ( Compatible fs gs
               , Max fs gs ~  (f : hs)
               , Alignable fs (f : hs)
               , Alignable gs (f : hs)
               , Num a
               )
            => Hyper fs a -> Hyper gs a -> Hyper hs a
innerpHyper xs ys = reduceBy (+) 0 (binary (*) xs ys)

-- | Generalized, rank-polymorphic matrix product.
matrixpHyper :: ( Num a
                , Dimension f
                , Dimension g
                , Dimension h
                )
             => Hyper '[ g, f ] a -> Hyper '[ h, g ] a -> Hyper '[ h, f ] a
matrixpHyper x y = case (crystal x, transposeHyper y) of
  (xs, Prism (Prism ys)) -> hzipWith dotp (up xs) (Prism (up ys))

binary :: ( Compatible fs gs
          , Max fs gs ~ hs
          , Alignable fs hs
          , Alignable gs hs
          )
        => (a -> b -> c)
        -> (Hyper fs a -> Hyper gs b -> Hyper hs c)
binary f x y = hzipWith f (align x) (align y)
