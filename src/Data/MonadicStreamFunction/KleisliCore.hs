{-# LANGUAGE Arrows, TypeOperators, Rank2Types, ScopedTypeVariables, TypeSynonymInstances  #-}

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
  klab >>= bklac = Kleisli $
    \ a -> (runKleisli klab a) >>= (\ b -> runKleisli (bklac b) a)

-- | Wrapper type for a generic Monadic Stream.
--
-- The MSC m a b type, which is isomorphic to Monadic Stream Function, is not really needed.
-- The only reason we have it is because Haskell does not allow instances of partial application
-- for type aliases.
newtype MSC m a b = MSC { ms :: MS (m a) b }

instance ArrowApply m => Category (MSC m) where
  id = MSC idMS
  f . g = MSC $ ms f `composeMS` ms g

-- | 'Arrow' instance for 'MSF's.
instance ArrowApply m => Arrow (MSC m) where
  arr  = MSC . arrMS
  first = MSC . firstMS . ms

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
  (b, fab') <- app -< (unMS msab, a)
  returnA -< ( (b, c), firstMS fab' )

-- | MapK apply a natural transformation to map between the Kleislis
mapK :: (m ~> n) -> Kleisli m a b -> Kleisli n a b
mapK nt klei = Kleisli $ nt . runKleisli klei

-- | transMS Apply a natural transformation to map between types of
--
transMS :: Functor n => (m ~> n) -> MS m a -> MS n a
transMS nt = MS . fmap inNa . nt . unMS where
  inNa (a, mcont) = (a, transMS nt mcont)

transMSC :: Functor (n a) => (m a ~> n a) -> MSC m a b -> MSC n a b
transMSC = transMS ()

-- | Monadic Stream Functions as Monadic Streams of Kleisli
--
-- With a type alias,
type KSF m = MSC (Kleisli m)

unKSF :: Functor m => KSF m a b -> a -> m (b, KSF m a b)
unKSF ksf a = fmap inM  (flip runKleisli a . unMS . ms $ ksf) where
  inM (b, cont) = (b, MSC cont)

type InMorph m a b c = a -> m (b, c)
morphKS :: Functor m2
         => (InMorph m1 a1 b1 ~> InMorph m2 a2 b2)
           -- ^ The natural transformation. @mi@, @ai@ and @bi@ for @i = 1, 2@
           --   can be chosen freely, but @c@ must be universally quantified
         -> KSF m1 a1 b1
         -> KSF m2 a2 b2
morphKS morph msf = MSC $ MS $ Kleisli $ undefined -- x\ a2 -> morphU <$> morph (unMS msf) a2 where
--   morphU (b2, cont) = (b2, morphKS morph cont)


-- | A natural transformation from @f@ to @g@.
-- Copied from the natural-transformations package
-- http://hackage.haskell.org/package/natural-transformation-0.4/docs/Control-Natural.html
infixr 0 ~>
type (~>) f g = forall x. f x -> g x
