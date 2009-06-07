{-# LANGUAGE UndecidableInstances, TypeFamilies, BangPatterns, Rank2Types
           , ExistentialQuantification, PatternGuards, ScopedTypeVariables
  #-}

-- Variation on Andy's Data.Reify.  This version uses Int in place of
-- Unique and handles /typed/ nodes.

module Data.TReify (
        MuRef(..),
        module Data.Reify.TGraph,
        reifyGraph
        ) where

import Control.Concurrent.MVar
import Control.Monad
import Control.Applicative
import System.Mem.StableName
import Data.IntMap as M
import Data.Typeable (Typeable)

import Data.Ty
import Data.Proof.EQ ((:=:)(..))
import Data.Reify.TGraph


class MuRef h where
  type DeRef h :: (* -> *) -> * -> *  -- DeRef h v a

  mapDeRef :: forall m v. (Applicative m)
           => (forall a. Typeable a => h a -> m (        v a))
           -> (forall a. Typeable a => h a -> m (DeRef h v a))


data StableBind h = forall a. StableBind (V a) (StableName (h a))


-- | 'reifyGraph' takes a data structure that admits 'MuRef', and returns
-- a 'Graph' that contains the dereferenced nodes, with their children as
-- 'Integer' rather than recursive values.

reifyGraph :: (MuRef h, Typeable a) => h a -> IO (Graph (DeRef h) a)
reifyGraph m = do rt1   <- newMVar M.empty
                  rt2   <- newMVar []
                  root  <- findNodes rt1 rt2 m
                  binds <- readMVar rt2
                  return (Graph binds root)

-- mylookup' :: StableName a -> IntMap [(StableName a, b)] -> Maybe b

-- mylookup' st tab =
--    case M.lookup (hashStableName st) tab of
--      Just tab2 -> Prelude.lookup st tab2
--      Nothing   -> Nothing

-- mylookup' st tab =
--    M.lookup (hashStableName st) tab >>= Prelude.lookup st


findNodes :: forall h a. (MuRef h, Typeable a) 
          => MVar (IntMap [StableBind h])
          -> MVar [Bind (DeRef h)]
          -> h a
          -> IO (V a)

-- findNodes = undefined

findNodes rt1 rt2 j0 =
  do nextI <- newMVar 0
     let newIndex = modifyMVar nextI (\ n -> return (n+1,n))
         loop :: Typeable b => h b -> IO (V b)
         loop !j = do
               st  <- makeStableName j
               tab <- takeMVar rt1
               case mylookup st tab of
                 Just var -> do putMVar rt1 tab
                                return $ var
                 Nothing -> 
                   do i <- newIndex
                      let var = V i ty
                      putMVar rt1 $
                        M.insertWith (++) (hashStableName st) [StableBind var st] tab
                      res <- mapDeRef loop j
                      tab' <- takeMVar rt2
                      putMVar rt2 $ Bind var res : tab'
                      return var
       in loop j0


mylookup :: forall h a. Typeable a =>
            StableName (h a) -> IntMap [StableBind h] -> Maybe (V a)
mylookup sta tab =
   M.lookup (hashStableName sta) tab >>= llookup
 where
   tya :: Ty a
   tya = ty
   llookup :: [StableBind h] -> Maybe (V a)
   llookup [] = Nothing
   llookup (StableBind v@(V _ tyb) stb : binds') 
     | Just Refl <- tya `tyEq` tyb, sta == stb = Just v
     | otherwise                               = llookup binds'
