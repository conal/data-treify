{-# LANGUAGE GADTs, ExistentialQuantification, FlexibleContexts
           , UndecidableInstances
  #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Reify.TGraph
  ( ShowF(..), Id, V(..), Bind(..), Graph(..)
  ) where

import Data.Ty

-- | Identifiers
type Id = Int

-- | Typed variables
data V a = V Id (Ty a)

-- | Typed binding pair, parameterized by variable and node type
-- constructors. 
data Bind n = forall a. Bind (V a) (n V a)

class ShowF f where
  showF :: f a -> String                -- maybe Show a => 

instance ShowF V where
  -- showF (V i t) = parens $ show i ++ "::" ++ show t
  showF (V i _) = 'x' : show i

-- parens :: String -> String
-- parens = ("(" ++) . (++ ")")

instance Show (V a) where show = showF

instance ShowF (n V) => Show (Bind n) where
  show (Bind v n) = showF v ++" = "++ showF n

-- | Graph, described by bindings and a root variable
data Graph n a = Graph [Bind n] (V a)

-- We could generalize V out of Bind and Graph.


instance (ShowF (n V), Show (V a)) => Show (Graph n a) where
  show (Graph netlist start) = "let " ++ show netlist ++ " in " ++ show start
