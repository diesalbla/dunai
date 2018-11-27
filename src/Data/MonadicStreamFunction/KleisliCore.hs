{-# LANGUAGE Arrows, TypeOperators, ScopedTypeVariables, TypeSynonymInstances  #-}

-- | Monadic Stream Functions are Monadic streams in a Kleisli Monad. 
--

module Data.MonadicStreamFunction.KleisliCore where

-- External
import Control.Arrow (returnA, Arrow(..), Kleisli(..), runKleisli, ArrowApply(..))
import Control.Applicative
import Control.Category (Category(..))
import Control.Monad

import Prelude hiding ((.), id, sum)

-- * Definitions

-- | Stepwise, side-effectful 'MSF's without implicit knowledge of time.
--
-- 'MSF's should be applied to streams or executed indefinitely or until they
-- terminate. See 'reactimate' and 'reactimateB' for details. In general,
-- calling the value constructor 'MSF' or the function 'unMSF' is discouraged.

data MS m o = MS { unMS :: m (o, MS m o) }

instance Functor m => Functor (MS m) where
  fmap f = MS . fmap (inMap) . unMS where
    inMap (b, cont) = (f b, fmap f cont) 

-- | 'Applicative' instance for 'MSF's.
--
-- Pure: a constant MSF that always returns the given value, without effects, and continues with itself.
--
-- Apply: zips the outputs of a monadic stream of A => B with the  a
instance Applicative m => Applicative (MS m) where
  pure b = MS $ pure (b, pure b) 
  sf <*> sb = MS $ liftA2 mix (unMS sf) (unMS sb) where
    mix (f, fcont) (b, bcont)= (f b, fcont <*> bcont)

-- Functor, Applicative, and Monad Instances for Kleisli
instance Functor m => Functor (Kleisli m a) where
  fmap f kl = Kleisli $ \a -> fmap f (runKleisli kl a)

instance Applicative m => Applicative (Kleisli m a) where
  pure b = Kleisli $ \ _ -> pure b
  kf <*> kb = Kleisli $ \ a -> runKleisli kf a <*> runKleisli kb a where

instance Monad m => Monad (Kleisli m a) where
  klab >>= bklac = Kleisli $ \ a -> (runKleisli klab a) >>= (\ b -> runKleisli (bklac b) a)

-- | Wrapper type for a generic Monadic Stream.
--
-- The MSC m a b type, which is isomorphic to Monadic Stream Function, is not really needed.
-- The only reason we have it is because Haskell does not allow instances of partial application
-- for type aliases. 
newtype MSC m a b = MSC { ms :: MS (m a) b }

instance ArrowApply m => Category (MSC m) where
  id = MSC idMS
  f . g = MSC $ ms f `composeMS` ms g

idMS :: Arrow m => MS (m a) a 
idMS = MS $ arr (\ a -> (a, idMS) )

arrMS :: Arrow m => (a -> b) -> MS (m a) b
arrMS f = MS $ arr (\ a -> (f a, arrMS f))

composeMS :: ArrowApply m => MS (m a) b -> MS (m c) a -> MS (m c) b
composeMS msab msca =
  let fab = unMS msab
      fca = unMS msca
  in MS $ proc c -> do
    (a, fca') <- app -< (fca, c)
    (b, fab') <- app -< (fab, a)
    returnA -< (b, fab' `composeMS` fca' )

firstMS :: ArrowApply m => MS (m a) b -> MS (m (a,c) ) (b, c)
firstMS msab = MS $ proc (a,c) -> do
  (b, fab') <- app -< (fab, a)
  returnA -< ( (b, c), firstMS fab' )
    where
      fab = unMS msab

-- | 'Arrow' instance for 'MSF's.
instance ArrowApply m => Arrow (MSC m) where
  arr  = MSC . arrMS 
  first = MSC . firstMS . ms 

-- | Monadic Stream Functions as Monadic Streams of Kleisli
--
-- With a type alias, 
type KSF m = MSC (Kleisli m)

-- arrM_ksf :: Functor m => (a -> m b) -> KSF m a b
-- arrM_ksf f = MSF $ MS $ Kleisli $ \ a -> f a <&>  \ b -> (b, arrM_ksf f)
