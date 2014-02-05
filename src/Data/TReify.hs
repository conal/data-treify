{-# LANGUAGE UndecidableInstances, TypeFamilies, BangPatterns, Rank2Types
           , ExistentialQuantification, PatternGuards, ScopedTypeVariables
           , MultiParamTypeClasses, GADTs
           , ConstraintKinds
  #-}
{-# OPTIONS_GHC -Wall #-}

-- Variation on Andy's Data.Reify.  This version uses Int in place of
-- Unique and handles /typed/ nodes.

module Data.TReify (
        MuRef(..),
        module Data.Reify.TGraph,
        reifyGraph
        ) where

import Control.Concurrent.MVar
-- import Control.Monad
import Control.Applicative (Applicative)
import System.Mem.StableName (StableName, makeStableName, hashStableName)
import Data.IntMap as M

import Data.IsTy

import Data.Proof.EQ ((:=:)(..))
import Data.Reify.TGraph


class MuRef ty h where
  type DeRef h :: (* -> *) -> * -> *  -- DeRef h v a

  mapDeRef :: forall m v. (Applicative m)
           => (forall a. IsTyConstraint ty a => ty a -> h a -> m (        v a))
           -> (forall a. IsTyConstraint ty a => ty a -> h a -> m (DeRef h v a))


data StableBind ty h =
  forall a. IsTyConstraint ty a => StableBind (V ty a) (StableName (h a))


-- | 'reifyGraph' takes a data structure that admits 'MuRef', and returns
-- a 'Graph' that contains the dereferenced nodes, with their children as
-- 'Integer' rather than recursive values.
reifyGraph :: (IsTy ty, IsTyConstraint ty a, MuRef ty h) =>
              ty a -> h a -> IO (Graph ty (DeRef h) a)
reifyGraph tya ha = do rt1   <- newMVar M.empty
                       rt2   <- newMVar []
                       root  <- findNodes rt1 rt2 tya ha
                       binds <- readMVar rt2
                       return (Graph binds root)


findNodes :: forall ty h a. (IsTy ty, IsTyConstraint ty a, MuRef ty h) 
          => MVar (IntMap [StableBind ty h])
          -> MVar [Bind ty (DeRef h)]
          -> ty a -> h a -> IO (V ty a)
findNodes rt1 rt2 tya ha =
  do nextI <- newMVar (0 :: Int)
     let newIndex = modifyMVar nextI (\ n -> return (n+1,n))
         loop :: IsTyConstraint ty b =>
                 ty b -> h b -> IO (V ty b)
         loop tyb !hb = do
               st  <- makeStableName hb
               tab <- takeMVar rt1
               case mylookup tyb st tab of
                 Just var -> do putMVar rt1 tab
                                return $ var
                 Nothing -> 
                   do i <- newIndex
                      let var = V i tyb
                      putMVar rt1 $
                        M.insertWith (++) (hashStableName st) [StableBind var st] tab
                      res <- mapDeRef loop tyb hb
                      tab' <- takeMVar rt2
                      putMVar rt2 $ Bind var res : tab'
                      return var
       in loop tya ha


mylookup :: forall ty h a. (IsTy ty, IsTyConstraint ty a) =>
            ty a -> StableName (h a) -> IntMap [StableBind ty h] -> Maybe (V ty a)
mylookup tya sta tab =
   M.lookup (hashStableName sta) tab >>= llookup
 where
   llookup :: [StableBind ty h] -> Maybe (V ty a)
   llookup [] = Nothing
   llookup (StableBind v@(V _ tyb) stb : binds') 
     | Just Refl <- tya `tyEq` tyb, sta == stb = Just v
     | otherwise                               = llookup binds'

-- unsafeReify :: (IsTy ty, MuRef ty h) => ty a -> h a -> Graph ty (DeRef h) a
-- unsafeReify = unsafePerformIO . reifyGraph
