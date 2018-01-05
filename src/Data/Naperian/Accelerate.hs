{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Naperian.Accelerate where

import           Data.Array.Accelerate ((:.) (..), Acc, Array, Elt, Exp,
                                        Lift (..), Shape, Unlift (..), Z (..),
                                        arrayShape, the, unit)
import qualified Data.Array.Accelerate as A
import qualified Data.Foldable         as F
import           Data.Kind             (Type)
import           Data.List.Split       (chunksOf)
import           Data.Naperian
import           GHC.Exts              (IsList (..))
import           Prelude               hiding (map)

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

-- | Instances for lifting @'Embed'@ded expressions to and from the Accelerate
-- language
instance Lift Acc (Embed (f ': fs) a) where
  type Plain (Embed (f ': fs) a) = Array (ToShape (f ': fs)) a
  lift (Embed x) = x

instance (Shape (ToShape (f ': fs))) => Unlift Acc (Embed (f ': fs) a) where
  unlift = Embed

instance (Elt a) => Lift Exp (Embed '[] a) where
  type Plain (Embed '[] a) = a
  lift (Embed x) = the x

instance (Elt a) => Unlift Exp (Embed '[] a) where
  unlift = Embed . unit

data Embed fs a where
  Embed :: (Shape (ToShape fs)) => Acc (Array (ToShape fs) a) -> Embed fs a

embed :: Elt a => Flat fs a -> Embed fs a
embed (Flat xs) = Embed (A.use xs)

execute :: Elt a => Embed fs a -> (Acc (Array (ToShape fs) a) -> Array (ToShape fs) a) -> Flat fs a
execute (Embed xs) evaluator = Flat $ evaluator xs

extract :: (Elt a) => Flat '[] a -> a
extract = point . unflatten

-- Wrappers around Accelerate functions
compute :: (Elt a) => Embed fs a -> Embed fs a
compute (Embed xs) = Embed (A.compute xs)

(!) :: (ToShape fs ~ sh, Elt a) => Embed fs a -> Exp sh -> Exp a
(!) (Embed xs) = (A.!) xs

zipWith :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b -> Exp c) -> Embed fs a -> Embed fs b -> Embed fs c
zipWith f (Embed xs) (Embed ys) = Embed (A.zipWith f xs ys)

map :: (Elt a, Elt b) => (Exp a -> Exp b) -> Embed fs a -> Embed fs b
map f (Embed xs) = Embed (A.map f xs)

fold :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp a -> Exp a) -> Exp a -> Embed (f ': fs) a -> Embed fs a
fold f e (Embed xs) = Embed $ A.fold f e xs

fold1 :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp a -> Exp a) -> Embed (f ': fs) a -> Embed fs a
fold1 f (Embed xs) = Embed $ A.fold1 f xs

foldAll :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp a -> Exp a) -> Exp a -> Embed fs a -> Embed '[] a
foldAll f e (Embed xs) = Embed $ A.foldAll f e xs

fold1All :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp a -> Exp a) -> Embed fs a -> Embed '[] a
fold1All f (Embed xs) = Embed $ A.fold1All f xs

all :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp Bool) -> Embed (f ': fs) a -> Embed fs Bool
all p (Embed xs) = Embed $ A.all p xs

any :: (Elt a, Shape (ToShape fs)) => (Exp a -> Exp Bool) -> Embed (f ': fs) a -> Embed fs Bool
any p (Embed xs) = Embed $ A.any p xs

and :: (Shape (ToShape fs)) => Embed (f ': fs) Bool -> Embed fs Bool
and (Embed xs) = Embed $ A.and xs

or :: (Shape (ToShape fs)) => Embed (f ': fs) Bool -> Embed fs Bool
or (Embed xs) = Embed $ A.or xs

sum :: (Shape (ToShape fs), A.Num a) => Embed (f ': fs) a -> Embed fs a
sum (Embed xs) = Embed $ A.sum xs

product :: (Shape (ToShape fs), A.Num a) => Embed (f ': fs) a -> Embed fs a
product (Embed xs) = Embed $ A.product xs

minimum :: (Shape (ToShape fs), A.Ord a) => Embed (f ': fs) a -> Embed fs a
minimum (Embed xs) = Embed $ A.minimum xs

maximum :: (Shape (ToShape fs), A.Ord a) => Embed (f ': fs) a -> Embed fs a
maximum (Embed xs) = Embed $ A.maximum xs

instance Show (Flat fs a) where
  show f = show (getArray f)

-- | Convert a Hyper to a Flat, preserving type information
flatten :: (Shape (ToShape fs), Elt a) => Hyper fs a -> Flat fs a
flatten = Flat . toArray

-- | Extracts extent of top-level Hyper dimension
topDimension :: Hyper fs a -> Int
topDimension (Scalar _) = error "Scalar has no top dimension"
topDimension (Prism x)  = F.length . head $ elements x

-- | Extracts extents of Hyper dimensions
dimensions :: Hyper fs a -> [Int]
dimensions (Scalar _) = []
dimensions (Prism x)  = (F.length . F.toList $ first x) : dimensions x

-- | Convert a Hyper value to its corresponding Array Shape (dimensionality)
toShape :: Hyper fs a -> ToShape fs
toShape (Scalar _)  = Z
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
  hyperise Z _   = error "cannot hyperise non-singleton list"

instance ( Dimension f
         , Shapely fs
         , Hyperise fs (f a)
         , Item (f a) ~ a
         , IsList (f a)
         , Show a
         ) =>
         Hyperise (f ': fs) a where
  hyperise (ss :. s) xs =
    Prism . hyperise ss $ GHC.Exts.fromList <$> (chunksOf s xs)

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
