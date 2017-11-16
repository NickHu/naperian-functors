{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Naperian.Accelerate where

import Data.Array.Accelerate
       ((:.)(..), Array, Elt, Shape, Z(..), arrayShape)
import qualified Data.Array.Accelerate as A
import qualified Data.Foldable as F
import Data.Kind (Type)
import Data.List.Split (chunksOf)
import Data.Naperian
import GHC.Exts (IsList(..))

-- 8 Flat representations
elements :: Hyper fs a -> [a]
elements = F.toList

-- elements (Scalar x) = [x]
-- elements (Prism x) = concatMap F.toList $ elements x
-- | Convert Hyper dimensions to its corresponding Array Shape (rank)
-- @
--    :kind! ToShape [Vector One, Vector Two, Vector Three]
--      = Z :. Int :. Int :. Int
-- @
type family ToShape (f :: [Type -> Type]) where
  ToShape '[] = Z
  ToShape (x ': xs) = ToShape xs :. Int

data Flat fs a where
  Flat :: (Shape (ToShape fs)) => Array (ToShape fs) a -> Flat fs a

-- | Convert a Hyper to a Flat, preserving type information
flatten :: (Shape (ToShape fs), Elt a) => Hyper fs a -> Flat fs a
flatten = Flat . toArray

-- | Extracts extent of top-level Hyper dimension
topDimension :: Hyper fs a -> Int
topDimension (Prism x) = F.length . head $ elements x

-- | Extracts extents of Hyper dimensions
dimensions :: Hyper fs a -> [Int]
dimensions (Scalar _) = []
dimensions (Prism x) = (F.length . F.toList $ first x) : dimensions x

-- | Convert a Hyper value to its corresponding Array Shape (dimensionality)
toShape :: Hyper fs a -> ToShape fs
toShape (Scalar _) = Z
toShape h@(Prism x) = toShape x :. topDimension h

-- | Convert a Hyper to an Array
toArray :: (Shape (ToShape fs), Elt a) => Hyper fs a -> Array (ToShape fs) a
toArray h = A.fromList (toShape h) (elements h)

-- | Convert a Flat to an Array
getArray :: Flat fs a -> Array (ToShape fs) a
getArray (Flat xs) = xs

-- | Convert a Flat to a Hyper, utilising type information
unflatten :: (Hyperise fs a, Shape (ToShape fs)) => Flat fs a -> Hyper fs a
unflatten f = hyperise (arrayShape arr) (A.toList arr)
  where
    arr = getArray f

-- | Conversion between type-level rank list and flat contents to Hyper
class Hyperise fs a where
  hyperise :: ToShape fs -> [a] -> Hyper fs a

instance Hyperise '[] a where
  hyperise Z [x] = Scalar x

instance ( Dimension f
         , Shapely fs
         , Hyperise fs (f a)
         , Item (f a) ~ a
         , IsList (f a)
         ) =>
         Hyperise (f ': fs) a where
  hyperise (ss :. s) xs =
    Prism . hyperise ss $ map GHC.Exts.fromList (chunksOf s xs)

-- TODO: Put this in separate conversions module
-- | Convert Array to nested list
type family ShapeToList s a where
  ShapeToList Z a = a
  ShapeToList (xs :. x) a = [ShapeToList xs a]

class Shape sh =>
      NestedList sh where
  toNestedList :: sh -> [a] -> ShapeToList sh a

instance NestedList (Z :. Int) where
  toNestedList (Z :. _) xs = xs

instance NestedList (n :. Int) => NestedList (n :. Int :. Int) where
  toNestedList (n :. x) xs = chunksOf x $ toNestedList n xs

arrayToList :: (Shape sh, NestedList sh) => Array sh a -> ShapeToList sh a
arrayToList a = toNestedList (arrayShape a) (A.toList a)
