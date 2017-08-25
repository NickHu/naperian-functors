{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Naperian.Symbolic where

import           Data.Foldable (toList)
import           Data.Kind     (Type)

import           Data.Naperian

azipWithL :: Applicative f => (a -> b -> c) -> f a -> b -> f c
azipWithL f xs y = fmap (`f` y) xs

azipWithR :: Applicative f => (a -> b -> c) -> a -> f b -> f c
azipWithR f = fmap . f

-- | A Hyper representation with symbolic replication
data HyperR :: [Type -> Type] -> Type -> Type where
  ScalarR :: a -> HyperR '[] a
  PrismR :: (Dimension f) => HyperR fs (f a) -> HyperR (f ': fs) a
  ReplR :: (Dimension f) => HyperR fs a -> HyperR (f ': fs) a

instance Show a => Show (HyperR fs a) where
  show (ScalarR x) = show x
  show (PrismR x)  = show $ toList <$> x
  show r@(ReplR _) = show $ forceReplR r

instance Eq a => Eq (HyperR '[] a) where
  ScalarR x == ScalarR y = x == y

instance (Eq a, Eq (HyperR fs (f a)), Eq (HyperR fs a))
      => Eq (HyperR (f ': fs) a) where
  PrismR x == PrismR y = x == y
  p@(PrismR _) == r@(ReplR _) = p == forceReplR r
  r@(ReplR _) == p@(PrismR _) = forceReplR r == p
  ReplR x == ReplR y = x == y

deriving instance Functor (HyperR fs)

instance Foldable (HyperR fs) where
  foldr f e (ScalarR x) = f x e
  foldr f e (PrismR x)  = foldr (flip $ foldr f) e x
  -- the above is derivable
  foldr f e x@(ReplR _) = foldr f e (forceReplR x)

instance Traversable (HyperR fs) where
  traverse f (ScalarR x) = ScalarR <$> f x
  traverse f (PrismR x)  = PrismR <$> traverse (traverse f) x
  -- the above is derivable
  traverse f x@(ReplR _) = traverse f (forceReplR x)

instance Applicative (HyperR '[]) where
  pure = ScalarR
  (<*>) = rzipWith ($)

instance (Dimension f, Applicative (HyperR fs))
      => Applicative (HyperR (f ': fs)) where
  pure = ReplR . pure
  (<*>) = rzipWith ($)

-- | Force the replication to be performed
forceReplR :: HyperR fs a -> HyperR fs a
forceReplR (ReplR x) = PrismR (fmap areplicate x)
forceReplR x         = x

rzipWith :: (a -> b -> c) -> HyperR fs a -> HyperR fs b -> HyperR fs c
rzipWith f (ScalarR x) (ScalarR y) = ScalarR (f x y)
rzipWith f (PrismR x) (PrismR y)   = PrismR (rzipWith (azipWith f) x y)
rzipWith f (PrismR x) (ReplR y)    = PrismR (rzipWith (azipWithL f) x y)
rzipWith f (ReplR x) (PrismR y)    = PrismR (rzipWith (azipWithR f) x y)
rzipWith f (ReplR x) (ReplR y)     = ReplR (rzipWith f x y)

rtranspose :: (Dimension f, Dimension g)
           => HyperR (f ': g ': fs) a -> HyperR (g ': f ': fs) a
rtranspose (PrismR (PrismR x)) = PrismR . PrismR $ transpose <$> x
rtranspose (PrismR (ReplR x))  = ReplR $ PrismR x
rtranspose (ReplR (PrismR x))  = PrismR $ ReplR x
rtranspose (ReplR (ReplR x))   = ReplR $ ReplR x

-- | A Hyper representation with symbolic transposition
data HyperT :: [Type -> Type] -> Type -> Type where
  ScalarT :: a -> HyperT '[] a
  PrismT :: (Dimension f) => HyperT fs (f a) -> HyperT (f ': fs) a
  TransT :: (Dimension f, Dimension g)
         => HyperT (f ': g ': fs) a ->  HyperT (g ': f ': fs) a

instance Show a => Show (HyperT fs a) where
  show (ScalarT x)  = show x
  show (PrismT x)   = show $ toList <$> x
  show t@(TransT _) = show $ forceTransT t

instance Eq a => Eq (HyperT '[] a) where
  ScalarT x == ScalarT y = x == y

instance (Eq a, Eq (f a)) => Eq (HyperT '[f] a) where
  PrismT x == PrismT y = x == y

instance (Eq a, Eq (HyperT (g ': fs) (f a)), Eq (HyperT (f ': fs) (g a)))
      => Eq (HyperT (f ': g ': fs) a) where
  PrismT x == PrismT y = x == y
  p@(PrismT _) == t@(TransT _) = p == forceTransT t
  t@(TransT _) == p@(PrismT _) = forceTransT t == p
  TransT x == TransT y = x == y

deriving instance Functor (HyperT fs)

instance Foldable (HyperT fs) where
  foldr f e (ScalarT x)  = f x e
  foldr f e (PrismT x)   = foldr (flip $ foldr f) e x
  -- the above is derivable
  foldr f e x@(TransT _) = foldr f e (forceTransT x)

instance Traversable (HyperT fs) where
  traverse f (ScalarT x)  = ScalarT <$> f x
  traverse f (PrismT x)   = PrismT <$> traverse (traverse f) x
  -- the above is derivable
  traverse f x@(TransT _) = traverse f (forceTransT x)

instance Applicative (HyperT '[]) where
  pure = ScalarT
  (<*>) = tzipWith ($)

instance (Dimension f, Applicative (HyperT fs))
      => Applicative (HyperT (f ': fs)) where
  pure = PrismT . pure . pure
  (<*>) = tzipWith ($)

transT :: (Dimension f, Dimension g)
       => HyperT (f ': g ': fs) a ->  HyperT (g ': f ': fs) a
transT (TransT x) = x
transT x          = TransT x

-- | Force the transposition to be performed
forceTransT :: (Dimension f, Dimension g)
            => HyperT (f ': g ': fs) a ->  HyperT (f ': g ': fs) a
forceTransT (TransT (PrismT (PrismT x))) = PrismT . PrismT $ transpose <$> x
forceTransT (TransT (PrismT x@(TransT _))) =
  case forceTransT x of
    PrismT x' -> PrismT . PrismT $ transpose <$> x'
forceTransT x                            = x

tzipWith :: (a -> b -> c) -> HyperT fs a -> HyperT fs b -> HyperT fs c
tzipWith f (ScalarT x) (ScalarT y)   = ScalarT (f x y)
tzipWith f (PrismT x) (PrismT y)     = PrismT (tzipWith (azipWith f) x y)
tzipWith f (TransT x) (TransT y)     = TransT (tzipWith f x y)
tzipWith f t@(TransT _) p@(PrismT _) = tzipWith f (forceTransT t) p
tzipWith f p@(PrismT _) t@(TransT _) = tzipWith f p $ forceTransT t

-- | A Hyper representation with symbolic replication and transposition
data HyperS :: [Type -> Type] -> Type -> Type where
  ScalarS :: a -> HyperS '[] a
  PrismS :: (Dimension f) => HyperS fs (f a) -> HyperS (f ': fs) a
  ReplS :: (Dimension f) => HyperS fs a -> HyperS (f ': fs) a
  TransS :: (Dimension f, Dimension g)
         => HyperS (f ': g ': fs) a ->  HyperS (g ': f ': fs) a

instance Show a => Show (HyperS fs a) where
  show (ScalarS x)  = show x
  show (PrismS x)   = show $ toList <$> x
  show r@(ReplS _)  = show $ forceReplS r
  show t@(TransS _) = show $ forceTransS t

instance Eq a => Eq (HyperS '[] a) where
  ScalarS x == ScalarS y = x == y

instance (Eq a, Eq (f a)) => Eq (HyperS '[f] a) where
  PrismS x     == PrismS y     = x            == y
  ReplS x      == ReplS y      = x            == y
  p@(PrismS _) == r@(ReplS _)  = p            == forceReplS r
  r@(ReplS _)  == p@(PrismS _) = forceReplS r == p

instance ( Eq a
         , Eq (HyperS (g ': fs) a) -- Repl equality
         , Eq (HyperS (g ': fs) (f a)) -- Prism equality
         , Eq (HyperS (g ': f ': fs) a) -- Trans equality
         )
      => Eq (HyperS (f ': g ': fs) a) where
  PrismS x     == PrismS y     = x             == y
  ReplS x      == ReplS y      = x             == y
  TransS x     == TransS y     = x             == y
  p@(PrismS _) == r@(ReplS _)  = p             == forceReplS r
  p@(PrismS _) == t@(TransS _) = p             == forceTransS t
  r@(ReplS _)  == p@(PrismS _) = forceReplS r  == p
  r@(ReplS _)  == t@(TransS _) = forceReplS r  == forceTransS t
  t@(TransS _) == p@(PrismS _) = forceTransS t == p
  t@(TransS _) == r@(ReplS _)  = forceTransS t == forceReplS r

deriving instance Functor (HyperS fs)

instance Foldable (HyperS fs) where
  foldr f e (ScalarS x)  = f x e
  foldr f e (PrismS x)   = foldr (flip $ foldr f) e x
  -- the above is derivable
  foldr f e x@(ReplS _)  = foldr f e (forceReplS x)
  foldr f e x@(TransS _) = foldr f e (forceTransS x)

instance Traversable (HyperS fs) where
  traverse f (ScalarS x)  = ScalarS <$> f x
  traverse f (PrismS x)   = PrismS <$> traverse (traverse f) x
  -- the above is derivable
  traverse f x@(ReplS _)  = traverse f (forceReplS x)
  traverse f x@(TransS _) = traverse f (forceTransS x)

instance Applicative (HyperS '[]) where
  pure = ScalarS
  (<*>) = szipWith ($)

instance (Dimension f, Applicative (HyperS fs))
      => Applicative (HyperS (f ': fs)) where
  pure = ReplS . pure
  (<*>) = szipWith ($)

szipWith :: (a -> b -> c) -> HyperS fs a -> HyperS fs b -> HyperS fs c
szipWith f  (ScalarS a) (ScalarS b)  = ScalarS (f a b)
szipWith f  (PrismS x) (PrismS y)    = PrismS (szipWith (azipWith f) x y)
szipWith f  (PrismS x)  (ReplS y)    = PrismS (szipWith (azipWithL f) x y)
szipWith f  (ReplS x)  (PrismS y)    = PrismS (szipWith (azipWithR f) x y)
szipWith f  (ReplS x)  (ReplS y)     = ReplS (szipWith f x y)
szipWith f  (TransS x) (TransS y)    = TransS (szipWith f x y)
szipWith f  (TransS x)
            (PrismS (ReplS y))       = TransS (szipWith f x (ReplS (PrismS y)))
szipWith f  (TransS x)
            (ReplS (PrismS y))       = TransS (szipWith f x (PrismS (ReplS y)))
szipWith f  (TransS x)
            (ReplS (ReplS y))        = TransS (szipWith f x (ReplS (ReplS y)))
szipWith f  x@(TransS _)
            y@(PrismS (PrismS _))    = szipWith f (forceTransS x) y
szipWith f  x@(TransS _)
            y@(PrismS (TransS _))    = szipWith f (forceTransS x) y
szipWith f  x@(TransS _)
            y@(ReplS (TransS _))     = szipWith f (forceTransS x) y
szipWith f  x y@(TransS _)           = szipWith (flip f) y x

forceReplS :: HyperS fs a -> HyperS fs a
forceReplS (ReplS x) = PrismS (fmap areplicate x)
forceReplS x         = x

forceTransS :: (Dimension f, Dimension g)
            => HyperS (f ': g ': fs) a -> HyperS (f ': g ': fs) a
forceTransS (TransS (ReplS (ReplS x))) = ReplS (ReplS x)
forceTransS (TransS (PrismS (ReplS x))) = ReplS (PrismS x)
forceTransS (TransS (ReplS (PrismS x))) =  PrismS (ReplS x)
forceTransS (TransS (PrismS (PrismS x))) = PrismS (PrismS (fmap transpose x))
forceTransS (TransS (PrismS x@(TransS _))) =
  forceTransS (TransS (PrismS (forceTransS x)))
forceTransS (TransS (ReplS x@(TransS _))) =
  forceTransS (TransS (ReplS (forceTransS x)))
forceTransS x = x

transS :: (Dimension f, Dimension g)
       => HyperS (f ': g ': fs) a -> HyperS (g ': f ': fs) a
transS (TransS x) = x
transS x          = TransS x

hStranspose :: (Dimension f, Dimension g) =>
               HyperS (f ': g ': fs) a -> HyperS (g ': f ': fs) a
hStranspose = transS
