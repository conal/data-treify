{-# LANGUAGE GADTs, ExistentialQuantification, FlexibleContexts
           , UndecidableInstances, PatternGuards
  #-}
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, Rank2Types #-} -- for bindEnv

{-# OPTIONS_GHC -Wall #-}

module Data.Reify.TGraph
  ( ShowF(..), Id, V(..), Bind(..), bindEnv, Graph(..)
  ) where

-- For bindEnv
import Data.IsTy
import Data.Proof.EQ
import qualified Data.IntMap as I

-- | Identifiers
type Id = Int

-- | Typed variables
data V ty a = V Id (ty a)

instance Eq (V ty a) where V i _ == V j _ = i == j

class ShowF f where
  showF :: f a -> String                -- maybe Show a => 

instance ShowF (V ty) where
  -- showF (V i t) = parens $ show i ++ "::" ++ show t
  showF (V i _) = 'x' : show i

-- parens :: String -> String
-- parens = ("(" ++) . (++ ")")

instance Show (V ty a) where show = showF

-- | Typed binding pair, parameterized by variable and node type
-- constructors. 
data Bind ty n = forall a. IsTyConstraint ty a => Bind (V ty a) (n (V ty) a)

instance ShowF (n (V ty)) => Show (Bind ty n) where
  show (Bind v n) = showF v ++" = "++ showF n

{-
-- Slow version
bindEnv' :: IsTy ty => [Bind ty n] -> (V ty a -> n (V ty) a)
bindEnv' [] _ = error "bindEnv': ran out of bindings"
bindEnv' (Bind (V i a) n : binds') v@(V i' a')
  | Just Refl <- a `tyEq` a', i == i' = n
  | otherwise                         = bindEnv' binds' v
-}

-- | Fast version, using an IntMap.
-- Important: partially apply.
bindEnv :: forall ty n. [Bind ty n] -> 
             forall a. (IsTy ty, IsTyConstraint ty a) => 
               (V ty a -> n (V ty) a)
bindEnv binds = \ (V i' a') -> extract a' (I.lookup i' m)
 where
   m :: I.IntMap (Bind ty n)
   m = I.fromList [(i,b) | b@(Bind (V i _) _) <- binds]
--    extract :: forall a'. IsTyConstraint ty a' => 
--               ty a' -> Maybe (Bind ty n) -> n (V ty) a'
   extract :: IsTyConstraint ty a => 
              ty a -> Maybe (Bind ty n) -> n (V ty) a
   extract _ Nothing            = error "bindEnv: variable not found"
   extract a' (Just (Bind (V _ a) n))
     | Just Refl <- a `tyEq` a' = n
     | otherwise                = error "bindEnv: wrong type"

-- TODO: Does the partial application *really* avoid the IntMap reconstruction?

-- | Graph, described by bindings and a root variable
data Graph ty n a = Graph [Bind ty n] (V ty a)

-- We could generalize V out of Bind and Graph.


instance (ShowF (n (V ty)), Show (V ty a)) => Show (Graph ty n a) where
  show (Graph netlist start) = "let " ++ show netlist ++ " in " ++ show start
