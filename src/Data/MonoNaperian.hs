{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Data.MonoNaperian where

import           Data.Kind            (Type)
import           Data.MonoTraversable

class MonoFunctor f => MonoNaperian f where
  type MonoLog f
  olookup :: f -> MonoLog f -> Element f
  otabulate :: (MonoLog f -> Element f) -> f

-- horrific?
otranspose :: ( MonoNaperian f
              , MonoNaperian (Element f)
              , MonoNaperian g
              , MonoNaperian (Element g)
              , Element (Element f) ~ Element (Element g)
              , MonoLog (Element f) ~ MonoLog g
              , MonoLog f ~ MonoLog (Element g))
           => f -> g
otranspose = otabulate . fmap otabulate . flip . fmap olookup . olookup

class (MonoPointed f, MonoNaperian f, MonoTraversable f) => MonoDimension f where
  osize :: f -> Int
  osize = length . otoList

ozipWith :: MonoNaperian f => (Element f -> Element f -> Element f) -> f -> f -> f
ozipWith f xs ys = otabulate (\i -> f (olookup xs i) (olookup ys i))

odotp :: (a ~ Element f, Num a, MonoDimension f) => f -> f -> a
odotp xs ys = osum (ozipWith (*) xs ys)

omatrixp xss yss = ozipWith (ozipWith odotp) (fmap opoint xss) (opoint (otranspose yss))

data MonoHyper :: [Type] -> Type -> Type where
  OScalar :: a -> MonoHyper '[] a
  OPrism :: (MonoDimension f) => MonoHyper fs f -> MonoHyper (f ': fs) (Element f)

type instance Element (MonoHyper fs a) = a -- useful???
